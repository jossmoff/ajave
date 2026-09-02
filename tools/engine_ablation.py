#!/usr/bin/env python3
"""Disable one engine at a time; verdicts may weaken but must never flip.

# Why this exists

The portfolio is its own oracle. Removing an engine can only remove evidence,
so a task that answered TRUE may become UNKNOWN -- but it must never become
FALSE, and a FALSE must never become TRUE. A flip means two engines disagree
about a fact of the program and at least one of them is unsound.

This needs no expected-verdict label, so it holds on programs no benchmark
covers, and unlike every other check in `tools/` it looks *between* engines
rather than inside one. Most defects found on 2026-09-02 lived there:

* obligation ids collided across methods, so one engine's finding suppressed
  another's on an unrelated obligation;
* `Bounded { k }` meant a path-depth bound to its producer and an
  iteration count to its consumer;
* k-induction published a bounded check as an inductive proof, and was harmless
  only because a gate starved it of base cases.

    python3 tools/engine_ablation.py --set smoke

Exit code 1 if any verdict flipped.
"""

import argparse
import glob
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from procguard import run_guarded

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "benchmarks")
AJAVE = os.path.join(ROOT, "target", "release", "ajave")

ENGINES = [
    "presolve", "concurrency", "concrete", "nra", "float-search",
    "interval-ai", "smt-bmc", "k-induction", "chc", "imc", "cegar",
]
DECIDED = {"TRUE", "FALSE"}


def resolve(yml):
    import yaml
    with open(yml) as f:
        data = yaml.safe_load(f)
    base = os.path.dirname(yml)
    props = []
    for p in data.get("properties", []):
        f_ = p.get("property_file", "")
        if "valid-assert" in f_:
            props.append("assert")
        elif "no-runtime-exception" in f_:
            props.append("no-runtime-exception")
    return [os.path.join(base, i) for i in data["input_files"]], props


def verdict(inputs, prop, timeout, disable=None):
    env = dict(os.environ)
    if disable:
        env["AJAVE_DISABLE"] = disable
    r = run_guarded([AJAVE, "--property", prop] + inputs, timeout=timeout, env=env)
    if r.timed_out:
        return "TIMEOUT"
    lines = [l.strip() for l in r.stdout.strip().splitlines() if l.strip()]
    return lines[-1] if lines else "ERROR"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--set", default="smoke")
    ap.add_argument("--limit", type=int, default=25)
    ap.add_argument("--timeout", type=int, default=60)
    args = ap.parse_args()

    set_path = os.path.join(BENCH, "sets", f"{args.set}.set")
    if not os.path.exists(set_path):
        sys.exit(f"no such set: {args.set}")
    tasks = []
    for line in open(set_path):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        tasks.extend(sorted(glob.glob(os.path.join(BENCH, line.split()[0]), recursive=True)))
    tasks = tasks[: args.limit]

    print(f"Ablation: {len(tasks)} task(s) x {len(ENGINES)} engine(s)\n")
    flips, weakened, checked = [], 0, 0

    for yml in tasks:
        try:
            inputs, props = resolve(yml)
        except Exception:
            continue
        for prop in props:
            base = verdict(inputs, prop, args.timeout)
            if base not in DECIDED:
                continue
            for eng in ENGINES:
                got = verdict(inputs, prop, args.timeout, disable=eng)
                checked += 1
                if got == base or got == "TIMEOUT":
                    continue
                if got not in DECIDED:
                    weakened += 1          # answer lost: expected and allowed
                    continue
                flips.append((os.path.relpath(yml, BENCH), prop, eng, base, got))
                print(f"  FLIP {os.path.relpath(yml, BENCH)} [{prop}] without "
                      f"{eng}: {base} -> {got}")

    print(f"\n{checked} ablated run(s); {weakened} answer(s) merely lost")
    if flips:
        print(f"\n{len(flips)} verdict(s) FLIPPED between TRUE and FALSE.")
        print("Removing an engine can only remove evidence, so a flip means two")
        print("engines disagree about the program and one of them is unsound.")
        return 1
    print("\nPASS — no verdict flipped.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
