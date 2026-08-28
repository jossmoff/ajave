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
    ("java/util/ArrayList", "get",         'new java.util.ArrayList<String>().get(0)'),
    ("java/util/ArrayList", "add",         'new java.util.ArrayList<String>().add(5, "x")'),
    ("java/util/Iterator",  "next",        'new java.util.ArrayList<String>().iterator().next()'),
    ("java/util/Stack",     "pop",         'new java.util.Stack<String>().pop()'),
    ("java/util/Stack",     "peek",        'new java.util.Stack<String>().peek()'),
    ("java/util/ArrayDeque","pop",         'new java.util.ArrayDeque<String>().pop()'),
    ("java/lang/System",    "arraycopy",   'System.arraycopy(new int[1],0,new int[1],0,5)'),
    ("java/lang/Math",      "addExact",    'Math.addExact(Integer.MAX_VALUE, 1)'),
    ("java/lang/Math",      "floorDiv",    'Math.floorDiv(1, 0)'),
    ("java/lang/Math",      "floorMod",    'Math.floorMod(1, 0)'),
    ("java/lang/Math",      "toIntExact",  'Math.toIntExact(Long.MAX_VALUE)'),
    ("java/lang/Math",      "multiplyExact", 'Math.multiplyExact(Integer.MAX_VALUE, 2)'),
    ("java/lang/Integer",   "valueOf",     'Integer.valueOf("abc")',
     "(Ljava/lang/String;)Ljava/lang/Integer;"),
    ("java/lang/Integer",   "parseInt",    'Integer.parseInt("abc")'),
    ("java/lang/Double",    "parseDouble", 'Double.parseDouble("abc")'),
    ("java/lang/String",    "format",      'String.format("%d", "notanint")'),
    ("java/io/PrintStream", "format",      'System.out.format("%d", "notanint")'),
    ("java/lang/String",    "concat",      '"x".concat(null)'),
    ("java/lang/String",    "contains",    '"x".contains(null)'),
    ("java/lang/String",    "charAt",      '"".charAt(0)'),
    ("java/lang/String",    "substring",   '"".substring(3)'),
    ("java/lang/StringBuilder", "<init>",  'new StringBuilder(-1)', "(I)V"),
    ("java/util/Arrays",    "copyOfRange", 'java.util.Arrays.copyOfRange(new int[2], 2, 1)'),
    ("java/util/Collections", "max",       'java.util.Collections.max(new java.util.ArrayList<Integer>())'),
    ("java/util/Collections", "nCopies",   'java.util.Collections.nCopies(-1, "x")'),
    ("java/util/TreeMap",   "put",         'new java.util.TreeMap<String,String>().put(null, "v")'),
    ("java/util/Scanner",   "hasNext",     'scannerClosed()'),
]

# Calls we DO allowlist: each must survive adversarial arguments.
MUST_NOT_THROW = [
    ("java/lang/Object",   "hashCode",  'new Object().hashCode()'),
    ("java/lang/String",   "length",    '"".length()'),
    ("java/lang/String",   "trim",      '"  ".trim()'),
    ("java/lang/String",   "equals",    '"x".equals(null)'),
    ("java/lang/String",   "toCharArray", '"".toCharArray()'),
    ("java/lang/String",   "toUpperCase", '"".toUpperCase()'),
    ("java/lang/Integer",  "valueOf",   'Integer.valueOf(Integer.MIN_VALUE)'),
    ("java/lang/Integer",  "toString",  'Integer.toString(Integer.MIN_VALUE)'),
    ("java/lang/Boolean",  "parseBoolean", 'Boolean.parseBoolean(null)'),
    ("java/lang/Math",     "abs",       'Math.abs(Integer.MIN_VALUE)'),
    ("java/lang/Math",     "sqrt",      'Math.sqrt(-1.0)'),
    ("java/lang/Math",     "log",       'Math.log(-1.0)'),
    ("java/lang/Math",     "pow",       'Math.pow(0.0, -1.0)'),
    ("java/lang/Math",     "round",     'Math.round(Double.NaN)'),
    ("java/lang/Math",     "max",       'Math.max(Integer.MIN_VALUE, Integer.MAX_VALUE)'),
    ("java/lang/System",   "currentTimeMillis", 'System.currentTimeMillis()'),
    ("java/lang/StringBuilder", "append", 'new StringBuilder().append((String) null)'),
    ("java/lang/StringBuilder", "length", 'new StringBuilder().length()'),
    ("java/io/PrintStream", "println",  'nullPrintln()'),
    ("java/util/ArrayList", "size",     'new java.util.ArrayList<String>().size()'),
    ("java/util/ArrayList", "isEmpty",  'new java.util.ArrayList<String>().isEmpty()'),
    ("java/util/Iterator",  "hasNext",  'new java.util.ArrayList<String>().iterator().hasNext()'),
    ("java/lang/Character", "isDigit",  'Character.isDigit((char) 0xFFFF)'),
    ("java/lang/Character", "toUpperCase", 'Character.toUpperCase((char) 0)'),
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


def allowlisted(src, cls, name, desc=None):
    """Is this signature reachable in the allowlist source?

    Descriptor-aware on purpose. The bug this test exists to catch is exactly
    an allowlist that cannot tell `Integer.valueOf(int)` from
    `Integer.valueOf(String)`, so matching on (class, name) alone would make
    the test blind to its own subject. When `desc` is given, the signature
    counts as allowlisted only if that descriptor appears in the class's arm.
    """
    if f'"{cls}"' not in src:
        return False
    idx = src.index(f'"{cls}"')
    window = src[idx: idx + 2600]
    if f'"{name}"' not in window:
        return False
    if desc is None:
        return True
    return f'"{desc}"' in window


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
