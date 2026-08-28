#!/usr/bin/env python3
"""Score ajave against its own benchmark suite.

Independent of `sv-benchmarks/`: these tasks were written to isolate one JVM
semantic rule or one engine capability each, and their verdicts were verified
against a real JVM by `tools/validate_own_benchmarks.py`.

Reports per category, and lists every wrong answer with the feature it names —
that is the point of the suite. A wrong answer here says which capability broke,
not merely that some large program changed verdict.

Usage: python3 tools/score_own.py [--dir ajave-benchmarks] [--timeout 30]
"""

import argparse
import glob
import os
import subprocess
import sys
import yaml
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed

AJAVE = "./target/release/ajave"
PROP_FLAG = {"assert": "assert", "nre": "no-runtime-exception"}


def load_tasks(root):
    tasks = []
    for yml in sorted(glob.glob(os.path.join(root, "*", "*.yml"))):
        with open(yml) as f:
            data = yaml.safe_load(f)
        name = os.path.splitext(os.path.basename(yml))[0]
        d = os.path.dirname(yml)
        inputs = [os.path.join(d, i) for i in data["input_files"]]
        for p in data.get("properties", []):
            pf = p.get("property_file", "")
            key = "assert" if "valid-assert" in pf else "nre"
            tasks.append((yml, name, os.path.basename(d), key, inputs,
                          p.get("expected_verdict")))
    return tasks


def run_one(t):
    yml, name, cat, key, inputs, expected = t
    exp = "TRUE" if expected else "FALSE"
    try:
        r = subprocess.run(
            [AJAVE, "--property", PROP_FLAG[key]] + inputs,
            capture_output=True, text=True, timeout=RUN_TIMEOUT,
        )
        got = r.stdout.strip().split("\n")[-1] if r.stdout.strip() else "ERROR"
    except subprocess.TimeoutExpired:
        got = "TIMEOUT"
    except Exception:
        got = "ERROR"
    return cat, name, key, exp, got


RUN_TIMEOUT = 30


def main():
    global RUN_TIMEOUT
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default="ajave-benchmarks")
    ap.add_argument("--timeout", type=int, default=30)
    ap.add_argument("--parallel", type=int, default=4)
    args = ap.parse_args()
    RUN_TIMEOUT = args.timeout

    tasks = load_tasks(args.dir)
    print(f"Scoring {len(tasks)} property instances from {args.dir}/\n")

    per_cat = defaultdict(lambda: defaultdict(int))
    wrong, unknown = [], []

    with ProcessPoolExecutor(max_workers=args.parallel) as ex:
        futs = [ex.submit(run_one, t) for t in tasks]
        for f in as_completed(futs):
            cat, name, key, exp, got = f.result()
            if got == exp:
                per_cat[cat]["correct"] += 1
            elif got in ("UNKNOWN", "TIMEOUT", "ERROR"):
                per_cat[cat][got.lower()] += 1
                unknown.append((cat, name, key, exp, got))
            else:
                per_cat[cat]["wrong"] += 1
                wrong.append((cat, name, key, exp, got))

    hdr = f"{'Category':<22s} {'ok':>4s} {'unk':>4s} {'TO':>4s} {'WRONG':>6s}"
    print(hdr)
    print("-" * len(hdr))
    tot = defaultdict(int)
    for cat in sorted(per_cat):
        c = per_cat[cat]
        print(f"{cat:<22s} {c['correct']:4d} {c['unknown']:4d} "
              f"{c['timeout']:4d} {c['wrong']:6d}")
        for k, v in c.items():
            tot[k] += v
    print("-" * len(hdr))
    print(f"{'TOTAL':<22s} {tot['correct']:4d} {tot['unknown']:4d} "
          f"{tot['timeout']:4d} {tot['wrong']:6d}")

    n = len(tasks)
    print(f"\ncorrect: {tot['correct']}/{n} = {100*tot['correct']/n:.1f}%")

    if wrong:
        print(f"\nWRONG ANSWERS ({len(wrong)}) — each names a broken feature:")
        for cat, name, key, exp, got in sorted(wrong):
            print(f"  [{cat}] {name} ({key}): said {got}, expected {exp}")

    if unknown:
        print(f"\nUnsolved ({len(unknown)}):")
        for cat, name, key, exp, got in sorted(unknown):
            print(f"  [{cat}] {name} ({key}): {got}, expected {exp}")

    sys.exit(1 if wrong else 0)


if __name__ == "__main__":
    main()
