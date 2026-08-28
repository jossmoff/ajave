#!/usr/bin/env python3
"""Measure how many timeouts are real capability limits vs. an impatient harness.

We score at 60s; SV-COMP allows ~900s CPU. A task that times out at 60s and
answers correctly at 300s was never a capability failure — it was a measurement
artifact, and counting it as an analysis gap sends effort to the wrong place.

Runs only the tasks that TIMEOUT at the short limit, re-runs them long, and
reports which ones convert. The output splits the timeout budget into:

  converts  - answers correctly given more time (harness artifact)
  still TO  - genuinely too slow (real work: profile these)
  wrong     - answers, but incorrectly (a latent unsoundness the timeout was
              accidentally hiding — worth knowing about urgently)

Usage: python3 tools/timeout_probe.py [--short 60] [--long 300] [--property ...]
"""

import argparse
import glob
import os
import subprocess
import sys
import time
import yaml
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed

AJAVE = "./target/release/ajave"
SV = "sv-benchmarks"
SET_FILE = os.path.join(SV, "ReachSafety-Java.set")
PROP_FLAG = {"assert": "valid-assert", "no-runtime-exception": "no-runtime-exception"}


def resolve(yml_path, prop):
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None, None
    d = os.path.dirname(yml_path)
    inputs = [os.path.join(d, i) for i in data["input_files"]]
    want = "valid-assert" if prop == "assert" else "no-runtime-exception"
    for p in data.get("properties", []):
        if want in p.get("property_file", ""):
            return inputs, p.get("expected_verdict")
    return None, None


def find_all_tasks():
    tasks = []
    with open(SET_FILE) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                tasks.extend(sorted(glob.glob(os.path.join(SV, line))))
    return tasks


def category_of(p):
    parts = os.path.relpath(p, SV).split(os.sep)
    if len(parts) >= 3 and parts[0] == "java-ranger-regression":
        return f"{parts[0]}/{parts[1]}"
    return parts[0] if len(parts) >= 2 else "other"


def run(inputs, prop, timeout):
    t0 = time.time()
    try:
        r = subprocess.run(
            [AJAVE, "--property", prop] + inputs,
            capture_output=True, text=True, timeout=timeout,
        )
        v = r.stdout.strip().split("\n")[-1] if r.stdout.strip() else "ERROR"
    except subprocess.TimeoutExpired:
        v = "TIMEOUT"
    except Exception:
        v = "ERROR"
    return v, time.time() - t0


def probe(arg):
    yml, prop, short, long_ = arg
    inputs, expected = resolve(yml, prop)
    if inputs is None or expected is None:
        return None
    v_short, _ = run(inputs, prop, short)
    if v_short != "TIMEOUT":
        return None  # only interested in what the short limit loses
    v_long, elapsed = run(inputs, prop, long_)
    exp = "TRUE" if expected else "FALSE"
    return yml, v_long, exp, elapsed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--short", type=int, default=60)
    ap.add_argument("--long", type=int, default=300)
    ap.add_argument("--property", default="no-runtime-exception")
    ap.add_argument("--parallel", type=int, default=4)
    args = ap.parse_args()

    prop = args.property
    tasks = find_all_tasks()
    print(f"property={prop}  short={args.short}s  long={args.long}s")
    print(f"scanning {len(tasks)} tasks for short-limit timeouts...\n")

    converts, still_to, wrong = [], [], []
    per_cat = defaultdict(lambda: defaultdict(int))

    with ProcessPoolExecutor(max_workers=args.parallel) as ex:
        futs = [ex.submit(probe, (t, prop, args.short, args.long)) for t in tasks]
        for f in as_completed(futs):
            res = f.result()
            if res is None:
                continue
            yml, got, exp, elapsed = res
            cat = category_of(yml)
            name = os.path.basename(yml)
            if got == exp:
                converts.append((cat, name, elapsed))
                per_cat[cat]["converts"] += 1
            elif got in ("TIMEOUT", "ERROR"):
                still_to.append((cat, name))
                per_cat[cat]["still"] += 1
            elif got in ("TRUE", "FALSE"):
                wrong.append((cat, name, got, exp))
                per_cat[cat]["wrong"] += 1
            else:
                per_cat[cat]["unknown"] += 1

    n = len(converts) + len(still_to) + len(wrong)
    print(f"{n} task(s) timed out at {args.short}s\n")
    print(f"  converts at {args.long}s : {len(converts)}")
    print(f"  still timeout           : {len(still_to)}")
    print(f"  WRONG when given time   : {len(wrong)}")

    if converts:
        print(f"\nRecoverable by a longer limit ({len(converts)}):")
        for cat, name, el in sorted(converts, key=lambda x: -x[2])[:20]:
            print(f"  [{cat}] {name}  ({el:.0f}s)")

    if wrong:
        print(f"\nWRONG once they finish ({len(wrong)}) — the timeout was hiding these:")
        for cat, name, got, exp in wrong:
            print(f"  [{cat}] {name}: said {got}, expected {exp}")

    if still_to:
        print(f"\nGenuinely too slow ({len(still_to)}) — profile these:")
        by_cat = defaultdict(int)
        for cat, _ in still_to:
            by_cat[cat] += 1
        for cat, c in sorted(by_cat.items(), key=lambda x: -x[1]):
            print(f"  {cat:<42s} {c}")


if __name__ == "__main__":
    main()
