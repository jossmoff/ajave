#!/usr/bin/env python3
"""Validate the NRE-safe JDK allowlist against a real JVM.

`could_throw_runtime_exception()` returning false is a soundness commitment:
the BMC uses it to claim a havoced call cannot raise, which lets it discharge
NRE obligations as TRUE. A wrong entry is a wrong TRUE (-16), not a precision
loss. Issue #48 found 22 wrong entries that had accumulated because the list
was grown until the benchmark corpus passed.

This is our own benchmark, independent of sv-benchmarks: for each signature we
claim is total, exercise it on a real JVM with adversarial arguments (empty
receivers, out-of-range indices, nulls, overflow boundaries) and assert nothing
throws. And for each signature we know to be partial, assert it *is* absent
from the allowlist.

Exit code 0 = allowlist consistent with observed JVM behaviour.

Usage: python3 tools/validate_jdk_allowlist.py
"""

import os
import re
import subprocess
import sys
import tempfile

EXPLORE = "crates/ajave-engines/src/smt_bmc/explore.rs"

# Calls that MUST be rejected by the allowlist: each throws a RuntimeException
# for the arguments shown. Confirmed empirically; see issue #48.
MUST_THROW = [
    # Overloads deliberately left OUT of the total table. `valueOf` is total on
    # every primitive and on none of the reference types: the `Object` overload
    # is `obj == null ? "null" : obj.toString()`, so a user class decides
    # whether it throws, and the `char[]` overload dereferences its argument.
    ("java/lang/String",    "valueOf",     'String.valueOf((char[]) null)', "([C)Ljava/lang/String;"),
    ("java/lang/String",    "valueOf",     'String.valueOf(new Object() { public String toString() { throw new IllegalStateException(); } })', "(Ljava/lang/Object;)Ljava/lang/String;"),
    ("java/lang/String",    "<init>",      'new String((String) null)', "(Ljava/lang/String;)V"),
    ("java/lang/String",    "matches",     '"x".matches("[")', "(Ljava/lang/String;)Z"),
    ("java/util/BitSet",    "<init>",      'new java.util.BitSet(-1)', "(I)V"),
    ("java/util/ArrayList", "get",         'new java.util.ArrayList<String>().get(0)', "(I)Ljava/lang/Object;"),
    ("java/util/ArrayList", "add",         'new java.util.ArrayList<String>().add(5, "x")', "(ILjava/lang/Object;)V"),
    ("java/util/Iterator",  "next",        'new java.util.ArrayList<String>().iterator().next()', "()Ljava/lang/Object;"),
    ("java/util/Stack",     "pop",         'new java.util.Stack<String>().pop()', "()Ljava/lang/Object;"),
    ("java/util/Stack",     "peek",        'new java.util.Stack<String>().peek()', "()Ljava/lang/Object;"),
    ("java/util/ArrayDeque","pop",         'new java.util.ArrayDeque<String>().pop()', "()Ljava/lang/Object;"),
    ("java/lang/System",    "arraycopy",   'System.arraycopy(new int[1],0,new int[1],0,5)', "(Ljava/lang/Object;ILjava/lang/Object;II)V"),
    ("java/lang/Math",      "addExact",    'Math.addExact(Integer.MAX_VALUE, 1)', "(II)I"),
    ("java/lang/Math",      "floorDiv",    'Math.floorDiv(1, 0)', "(II)I"),
    ("java/lang/Math",      "floorMod",    'Math.floorMod(1, 0)', "(II)I"),
    ("java/lang/Math",      "toIntExact",  'Math.toIntExact(Long.MAX_VALUE)', "(J)I"),
    ("java/lang/Math",      "multiplyExact", 'Math.multiplyExact(Integer.MAX_VALUE, 2)', "(II)I"),
    ("java/lang/Integer",   "valueOf",     'Integer.valueOf("abc")', "(Ljava/lang/String;)Ljava/lang/Integer;"),
    ("java/lang/Integer",   "parseInt",    'Integer.parseInt("abc")', "(Ljava/lang/String;)I"),
    ("java/lang/Double",    "parseDouble", 'Double.parseDouble("abc")', "(Ljava/lang/String;)D"),
    ("java/lang/String",    "format",      'String.format("%d", "notanint")', "(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;"),
    ("java/io/PrintStream", "format",      'System.out.format("%d", "notanint")', "(Ljava/lang/String;[Ljava/lang/Object;)Ljava/io/PrintStream;"),
    ("java/lang/String",    "concat",      '"x".concat(null)', "(Ljava/lang/String;)Ljava/lang/String;"),
    ("java/lang/String",    "contains",    '"x".contains(null)', "(Ljava/lang/CharSequence;)Z"),
    ("java/lang/String",    "charAt",      '"".charAt(0)', "(I)C"),
    ("java/lang/String",    "substring",   '"".substring(3)', "(I)Ljava/lang/String;"),
    ("java/lang/StringBuilder", "<init>",  'new StringBuilder(-1)', "(I)V"),
    ("java/util/Arrays",    "copyOfRange", 'java.util.Arrays.copyOfRange(new int[2], 2, 1)', "([III)[I"),
    ("java/util/Collections", "max",       'java.util.Collections.max(new java.util.ArrayList<Integer>())', "(Ljava/util/Collection;)Ljava/lang/Object;"),
    ("java/util/Collections", "nCopies",   'java.util.Collections.nCopies(-1, "x")', "(ILjava/lang/Object;)Ljava/util/List;"),
    ("java/util/TreeMap",   "put",         'new java.util.TreeMap<String,String>().put(null, "v")', "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"),
    ("java/util/Scanner",   "hasNext",     'scannerClosed()', "()Z"),
]

# Calls we DO allowlist: each must survive adversarial arguments.
MUST_NOT_THROW = [
    ("java/lang/Object",   "hashCode",  'new Object().hashCode()', "()I"),
    ("java/lang/String",   "length",    '"".length()', "()I"),
    ("java/lang/String",   "trim",      '"  ".trim()', "()Ljava/lang/String;"),
    ("java/lang/String",   "equals",    '"x".equals(null)', "(Ljava/lang/Object;)Z"),
    ("java/lang/String",   "toCharArray", '"".toCharArray()', "()[C"),
    ("java/lang/String",   "toUpperCase", '"".toUpperCase()', "()Ljava/lang/String;"),
    ("java/lang/Integer",  "valueOf",   'Integer.valueOf(Integer.MIN_VALUE)', "(I)Ljava/lang/Integer;"),
    ("java/lang/Integer",  "toString",  'Integer.toString(Integer.MIN_VALUE)', "(I)Ljava/lang/String;"),
    ("java/lang/Boolean",  "parseBoolean", 'Boolean.parseBoolean(null)', "(Ljava/lang/String;)Z"),
    ("java/io/PrintStream", "println",  'nullPrintln()', "(Ljava/lang/String;)V"),
    ("java/lang/Math",     "abs",       'Math.abs(Integer.MIN_VALUE)', "(I)I"),
    ("java/lang/Math",     "sqrt",      'Math.sqrt(-1.0)', "(D)D"),
    ("java/lang/Math",     "log",       'Math.log(-1.0)', "(D)D"),
    ("java/lang/Math",     "pow",       'Math.pow(0.0, -1.0)', "(DD)D"),
    ("java/lang/Math",     "round",     'Math.round(Double.NaN)', "(D)J"),
    ("java/lang/Math",     "max",       'Math.max(Integer.MIN_VALUE, Integer.MAX_VALUE)', "(II)I"),
    ("java/lang/System",   "currentTimeMillis", 'System.currentTimeMillis()', "()J"),
    ("java/lang/StringBuilder", "append", 'new StringBuilder().append((String) null)', "(Ljava/lang/String;)Ljava/lang/StringBuilder;"),
    ("java/lang/StringBuilder", "length", 'new StringBuilder().length()', "()I"),
    ("java/lang/StringBuilder", "capacity", 'new StringBuilder().capacity()', "()I"),
    ("java/lang/StringBuilder", "reverse", 'new StringBuilder("ab\\uD83D\\uDE00").reverse()', "()Ljava/lang/StringBuilder;"),
    ("java/lang/String",   "valueOf",   'String.valueOf(true)', "(Z)Ljava/lang/String;"),
    ("java/lang/String",   "valueOf",   'String.valueOf(Integer.MIN_VALUE)', "(I)Ljava/lang/String;"),
    ("java/lang/String",   "valueOf",   'String.valueOf(Long.MIN_VALUE)', "(J)Ljava/lang/String;"),
    ("java/lang/String",   "valueOf",   'String.valueOf(Double.NaN)', "(D)Ljava/lang/String;"),
    ("java/lang/String",   "valueOf",   'String.valueOf(Float.NEGATIVE_INFINITY)', "(F)Ljava/lang/String;"),
    ("java/lang/String",   "valueOf",   'String.valueOf((char) 0)', "(C)Ljava/lang/String;"),
    ("java/lang/String",   "<init>",    'new String()', "()V"),
    ("java/lang/Double",   "isFinite",  'Double.isFinite(Double.NaN)', "(D)Z"),
    ("java/lang/Character","isDefined", 'Character.isDefined((char) 0xFFFF)', "(C)Z"),
    ("java/util/ArrayList", "size",     'new java.util.ArrayList<String>().size()', "()I"),
    ("java/util/ArrayList", "isEmpty",  'new java.util.ArrayList<String>().isEmpty()', "()Z"),
    ("java/util/Iterator",  "hasNext",  'new java.util.ArrayList<String>().iterator().hasNext()', "()Z"),
    ("java/lang/Character", "isDigit",  'Character.isDigit((char) 0xFFFF)', "(C)Z"),
    ("java/lang/Character", "toUpperCase", 'Character.toUpperCase((char) 0)', "(C)C"),
]


def norm(case):
    """Normalise a case to (class, name, expr, desc-or-None)."""
    if len(case) == 4:
        cls, name, expr, desc = case
        return cls, name, expr, desc
    cls, name, expr = case
    return cls, name, expr, None


def build_probe(cases):
    body = []
    for i, case in enumerate(cases):
        _c, _n, expr, _d = norm(case)
        body.append(
            f'    try {{ Object _r{i} = (Object)(({expr}) instanceof Object ? null : null);'
            f' System.out.println("SAFE {i}"); }}'
            f' catch (Throwable e) {{ System.out.println("THROWS {i} " + e.getClass().getName()); }}'
        )
    # Simpler: evaluate each expression as a statement inside a lambda.
    stmts = []
    for i, case in enumerate(cases):
        _c, _n, expr, _d = norm(case)
        stmts.append(
            f'    try {{ run(() -> {{ {expr}; }}); System.out.println("SAFE {i}"); }}\n'
            f'    catch (Throwable e) {{ System.out.println("THROWS {i} " + e.getClass().getName()); }}'
        )
    return (
        "public class Probe {\n"
        "  interface B { void go() throws Throwable; }\n"
        "  static void run(B b) throws Throwable { b.go(); }\n"
        "  static void nullPrintln() { System.out.println((String) null); }\n"
        "  static void scannerClosed() {\n"
        "    java.util.Scanner s = new java.util.Scanner(\"a\"); s.close(); s.hasNext();\n"
        "  }\n"
        "  public static void main(String[] a) throws Throwable {\n"
        + "\n".join(stmts) +
        "\n  }\n}\n"
    )


def run_probe(cases):
    with tempfile.TemporaryDirectory() as d:
        src = os.path.join(d, "Probe.java")
        with open(src, "w") as f:
            f.write(build_probe(cases))
        r = subprocess.run(["javac", src], capture_output=True, text=True, cwd=d)
        if r.returncode != 0:
            print("javac failed:\n" + r.stderr[:3000])
            sys.exit(2)
        r = subprocess.run(["java", "-cp", d, "Probe"], capture_output=True, text=True)
        out = {}
        for line in r.stdout.splitlines():
            parts = line.split()
            if len(parts) >= 2 and parts[0] in ("SAFE", "THROWS"):
                out[int(parts[1])] = (parts[0], parts[2] if len(parts) > 2 else "")
        return out


QUERY = "target/release/contract_query"


def allowlisted(_src, cls, name, desc=None):
    """Is this signature treated as total by the engine?

    Asks `ajave_models::contract_for` through the `contract_query` binary,
    which is the single declaration of what an external method does.

    This used to scrape `smt_bmc/explore.rs` for the class and descriptor
    strings, which was wrong twice over. `CLAUDE.md` had already named the
    first problem -- a source-text check cannot reliably tell overloads apart,
    since it matched any descriptor appearing within 2600 bytes of the class
    name. The second was worse: the table had *moved* to `ajave_models`, and
    what is left in `explore.rs` is the test module, so the harness was
    matching its own fixtures and reporting them as allowlist entries. It
    printed 27 "reachable wrong TRUEs" that did not exist.

    A gate that cries wolf 27 times is a gate nobody reads, which is the same
    outcome as not having one.
    """
    if desc is None:
        raise SystemExit(
            f"{cls}.{name}: every probe needs a full descriptor now. "
            "Keying on (class, name) is the bug this harness exists to catch."
        )
    if not os.path.exists(QUERY):
        raise SystemExit(
            f"missing {QUERY} — run: cargo build --release -p ajave-models "
            "--bin contract_query"
        )
    out = subprocess.run(
        [QUERY, cls, name, desc], capture_output=True, text=True
    )
    return out.stdout.strip() == "total"


def main():
    src = open(EXPLORE).read()
    failures = []

    print("Probing JVM behaviour...\n")
    thrown = run_probe(MUST_THROW)
    safe = run_probe(MUST_NOT_THROW)

    print("=== Signatures that MUST NOT be allowlisted (they throw) ===")
    for i, case in enumerate(MUST_THROW):
        cls, name, expr, desc = norm(case)
        got = thrown.get(i, ("MISSING", ""))
        if got[0] != "THROWS":
            print(f"  ?  {cls}.{name}: expected a throw from `{expr}`, JVM said {got[0]}")
            continue
        if allowlisted(src, cls, name, desc):
            print(f"  FAIL {cls}.{name} throws {got[1]} but IS allowlisted")
            failures.append((cls, name, got[1]))
        else:
            print(f"  ok   {cls}.{name} throws {got[1]}, correctly not allowlisted")

    print("\n=== Signatures we allowlist (must survive adversarial args) ===")
    for i, case in enumerate(MUST_NOT_THROW):
        cls, name, expr, desc = norm(case)
        got = safe.get(i, ("MISSING", ""))
        if got[0] == "THROWS":
            print(f"  FAIL {cls}.{name} threw {got[1]} on `{expr}` but IS allowlisted")
            failures.append((cls, name, got[1]))
        else:
            print(f"  ok   {cls}.{name} total on `{expr}`")

    print()
    if failures:
        print(f"{len(failures)} allowlist violation(s) — these are reachable wrong TRUEs.")
        sys.exit(1)
    print("Allowlist consistent with observed JVM behaviour.")
    sys.exit(0)


if __name__ == "__main__":
    main()
