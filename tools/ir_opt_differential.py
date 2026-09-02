#!/usr/bin/env python3
"""`AJAVE_IR_OPT=0` versus `=1` must give the same verdict on every task.

An IR reduction is a meaning-preserving transformation, so a verdict that
changes under it is a defect -- in the passes, or in an engine that is sensitive
to something it should not be. No expected-verdict label is involved, so this
holds on programs no benchmark covers.

    python3 tools/ir_opt_differential.py --set smoke

Exit code 1 if any verdict changed.
"""
import argparse, glob, os, sys, yaml, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from procguard import run_guarded

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "benchmarks")
AJAVE = os.path.join(ROOT, "target", "release", "ajave")


def verdict(inputs, prop, timeout, opt):
    env = dict(os.environ)
    env["AJAVE_IR_OPT"] = opt
    r = run_guarded([AJAVE, "--property", prop] + inputs, timeout=timeout, env=env)
    if r.timed_out:
        return "TIMEOUT"
    lines = [l.strip() for l in r.stdout.strip().splitlines() if l.strip()]
    return lines[-1] if lines else "ERROR"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--set", default="smoke")
    ap.add_argument("--limit", type=int, default=60)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--base", default="0", help="AJAVE_IR_OPT for the baseline side")
    ap.add_argument("--against", default="1", help="AJAVE_IR_OPT for the other side")
    a = ap.parse_args()

    path = os.path.join(BENCH, "sets", f"{a.set}.set")
    tasks = []
    for line in open(path):
        line = line.split("#", 1)[0].strip()
        if line:
            tasks.extend(sorted(glob.glob(os.path.join(BENCH, line.split()[0]), recursive=True)))
    tasks = tasks[: a.limit]

    changed, checked = [], 0
    counts = collections.Counter()
    for yml in tasks:
        try:
            d = yaml.safe_load(open(yml))
        except Exception:
            continue
        base = os.path.dirname(yml)
        inputs = [os.path.join(base, i) for i in d["input_files"]]
        for p in d.get("properties", []):
            f = p.get("property_file", "")
            prop = "assert" if "valid-assert" in f else (
                "no-runtime-exception" if "no-runtime-exception" in f else None)
            if not prop:
                continue
            off = verdict(inputs, prop, a.timeout, a.base)
            if off in ("TIMEOUT", "ERROR"):
                continue
            on = verdict(inputs, prop, a.timeout, a.against)
            checked += 1
            if on == off:
                continue
            if on == "TIMEOUT":
                counts["slower"] += 1
                continue
            changed.append((os.path.relpath(yml, BENCH), prop, off, on))
            print(f"  CHANGED {os.path.relpath(yml, BENCH)} [{prop}]: {off} -> {on}")

    print(f"\n{checked} task/property pairs compared, {counts['slower']} became timeouts")
    if changed:
        print(f"\n{len(changed)} verdict(s) changed. An IR reduction cannot change what is")
        print("true of a program, so each is a defect in the passes or in an engine.")
        return 1
    print("\nPASS — AJAVE_IR_OPT does not change any verdict.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
