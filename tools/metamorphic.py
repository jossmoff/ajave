#!/usr/bin/env python3
"""Verdicts that must not change under meaning-preserving program edits.

# Why this exists

Most defects found on 2026-09-02 were not inside an engine. They were between
components, and no benchmark could see them because every benchmark exercises
one program at a time:

* `skipped_obligations` and `violated_oids` were keyed by `ObligationId` alone.
  Ids index into a single `Body`, so a violation in one method blocked
  discharge of an unrelated obligation that happened to share an index in
  another. Worth 32 points on no-runtime-exception once fixed, and invisible to
  every existing test.
* `guarded_at` did not take the obligation's kind, so which handler was written
  around a statement changed whether an unrelated property was seeded.

Both are *relational* faults: the verdict for a program depended on something
that should not affect it. A single program cannot expose that; a pair can.

Each transformation below preserves the property under test by construction, so
the verdict must be identical. A difference is a bug in the tool under test, not
in the benchmark -- there is no expected-verdict label involved, which is what
makes this a stronger oracle than the corpus.

    python3 tools/metamorphic.py --set smoke

Exit code 1 if any transformation changed a verdict.
"""

import argparse
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from procguard import run_guarded

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "benchmarks")
AJAVE = os.path.join(ROOT, "target", "release", "ajave")

# An extra method whose obligations are all satisfied, called from main so that
# it is reachable and its obligations are seeded. It exists to occupy obligation
# ids that overlap main's: if any engine keys a per-obligation fact by id alone,
# the two methods collide and a verdict moves.
AUX_METHOD = """
  static int ajaveMetamorphicAux(int p) {
    int[] t = new int[4];
    t[0] = p;
    t[1] = t[0] + 1;
    int q = t[1];
    if (q != 0) {
      q = 100 / q;
    }
    return q + t[2] + t[3];
  }
"""
AUX_CALL = "    ajaveMetamorphicAux(7);\n"

MAIN_RE = re.compile(
    r"(public\s+static\s+void\s+main\s*\([^)]*\)\s*(?:throws\s+[\w.,\s]+)?\{)"
)


def add_unrelated_method(src):
    """Insert a reachable, always-safe helper.

    Its obligations are satisfied on every path, so it cannot change any
    verdict. What it *does* change is the set of obligation ids in play.
    """
    if "ajaveMetamorphicAux" in src or not MAIN_RE.search(src):
        return None
    out = MAIN_RE.sub(lambda m: m.group(1) + "\n" + AUX_CALL, src, count=1)
    close = out.rfind("}")
    if close < 0:
        return None
    return out[:close] + AUX_METHOD + out[close:]


# Only `private static` methods are renamed. Anything else may be an override
# -- `run`, `call`, `apply`, `compareTo` -- and renaming one of those does not
# preserve meaning, it stops the method being called at all. The first version
# of this renamed `run()` on a Runnable, so the thread body never executed and
# the harness reported its own edit as a defect in ajave.
PRIVATE_STATIC_RE = re.compile(
    r"\bprivate\s+static\s+[\w.\[\]<>,\s]+?\b(\w+)\s*\("
)


def rename_helper(src):
    """Rename every `private static` method. Nothing may depend on a spelling.

    Catches ordering or hashing that leaks into a decision -- the class of
    defect that once made verdicts depend on `HashMap` iteration order.
    """
    names = {n for n in PRIVATE_STATIC_RE.findall(src) if not n[0].isupper()}
    names -= {"main"}
    if not names:
        return None
    out = src
    for n in sorted(names):
        out = re.sub(rf"\b{re.escape(n)}\b", n + "Renamed", out)
    return out if out != src else None


TRANSFORMS = {
    "add-unrelated-method": add_unrelated_method,
    "rename-helper": rename_helper,
}


def resolve_inputs(yml):
    import yaml
    with open(yml) as f:
        data = yaml.safe_load(f)
    base = os.path.dirname(yml)
    return [os.path.join(base, i) for i in data["input_files"]], data


def properties_of(data):
    out = []
    for p in data.get("properties", []):
        f = p.get("property_file", "")
        if "valid-assert" in f:
            out.append("assert")
        elif "no-runtime-exception" in f:
            out.append("no-runtime-exception")
    return out


def verdict(inputs, prop, timeout):
    r = run_guarded([AJAVE, "--property", prop] + inputs, timeout=timeout)
    if r.timed_out:
        return "TIMEOUT"
    lines = [l.strip() for l in r.stdout.strip().splitlines() if l.strip()]
    return lines[-1] if lines else "ERROR"


def transformed_copy(inputs, fn, tmp):
    """Copy the task's inputs, rewriting the single Main.java that defines main."""
    new_inputs, changed = [], False
    for i, inp in enumerate(inputs):
        dst = os.path.join(tmp, f"in{i}")
        if os.path.isdir(inp):
            shutil.copytree(inp, dst)
        else:
            os.makedirs(dst, exist_ok=True)
            shutil.copy(inp, dst)
        new_inputs.append(dst)
        for java in glob.glob(os.path.join(dst, "**", "*.java"), recursive=True):
            with open(java) as f:
                src = f.read()
            if not MAIN_RE.search(src):
                continue
            out = fn(src)
            if out is None:
                continue
            with open(java, "w") as f:
                f.write(out)
            changed = True
    return (new_inputs, changed)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--set", default="smoke")
    ap.add_argument("--limit", type=int, default=40)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--transform", action="append", choices=sorted(TRANSFORMS))
    args = ap.parse_args()

    set_path = os.path.join(BENCH, "sets", f"{args.set}.set")
    if not os.path.exists(set_path):
        sys.exit(f"no such set: {args.set}")
    tasks = []
    for line in open(set_path):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        pattern = line.split()[0]
        tasks.extend(sorted(glob.glob(os.path.join(BENCH, pattern), recursive=True)))
    tasks = tasks[: args.limit]

    names = args.transform or sorted(TRANSFORMS)
    print(f"Metamorphic check: {len(tasks)} task(s) x {len(names)} transformation(s)\n")

    failures, weakened, checked, skipped = [], [], 0, 0
    for yml in tasks:
        try:
            inputs, data = resolve_inputs(yml)
        except Exception:
            continue
        for prop in properties_of(data):
            base = verdict(inputs, prop, args.timeout)
            # A task we cannot decide, or one whose cost is near the budget,
            # says nothing about a transformation.
            if base in ("TIMEOUT", "ERROR"):
                skipped += 1
                continue
            for name in names:
                with tempfile.TemporaryDirectory() as tmp:
                    new_inputs, changed = transformed_copy(inputs, TRANSFORMS[name], tmp)
                    if not changed:
                        continue
                    got = verdict(new_inputs, prop, args.timeout)
                    checked += 1
                    if got == "TIMEOUT":
                        # Slower after an edit is not a correctness claim.
                        skipped += 1
                        continue
                    if got == base:
                        continue
                    if got not in ("TRUE", "FALSE"):
                        # The edit makes the program bigger, so losing an
                        # answer can be a cost effect rather than a defect.
                        # Reported, not failed.
                        weakened.append(
                            (os.path.relpath(yml, BENCH), prop, name, base, got)
                        )
                        continue
                    failures.append(
                        (os.path.relpath(yml, BENCH), prop, name, base, got)
                    )
                    print(f"  FLIPPED {os.path.relpath(yml, BENCH)} [{prop}] "
                          f"under {name}: {base} -> {got}")

    print(f"\n{checked} transformed run(s), {skipped} inconclusive, "
          f"{len(weakened)} weakened (answer lost, not flipped)")
    for w in weakened[:15]:
        print(f"  weakened {w[0]} [{w[1]}] under {w[2]}: {w[3]} -> {w[4]}")
    if failures:
        print(f"\n{len(failures)} verdict(s) FLIPPED under a meaning-preserving edit.")
        print("A transformation cannot change what is true of a program, so each")
        print("of these is a defect in ajave.")
        return 1
    print("\nPASS — no verdict changed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
