#!/usr/bin/env python3
"""Rank the JDK signatures that block no-runtime-exception proofs.

A call whose exception behaviour we do not model prevents a TRUE verdict, since
we cannot claim "no runtime exception" about code we never examined. That rule
is correct, but it is only *useful* if the allowlist is calibrated: a signature
that is genuinely total and merely absent from the list costs us every proof it
appears in, for nothing.

This ranks the offenders by how many tasks each one blocks, so the allowlist can
be extended where the JDK contract actually justifies it — and so the ones that
genuinely throw are visible as real modelling work rather than oversights.

Usage: python3 tools/blocking_calls.py [per_category_limit]
"""

import glob
import os
import re
import subprocess
import sys
import yaml
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed

AJAVE = "./target/release/ajave"
SV = "sv-benchmarks"
SET_FILE = os.path.join(SV, "ReachSafety-Java.set")
BLOCK_RE = re.compile(r"calls (\S+)\.(\S+?)(\([^ ]*) whose exception behaviour")


def resolve(yml_path):
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None, None
    d = os.path.dirname(yml_path)
    inputs = [os.path.join(d, i) for i in data["input_files"]]
    verdicts = {}
    for p in data.get("properties", []):
        if "no-runtime-exception" in p.get("property_file", ""):
            verdicts["nre"] = p.get("expected_verdict")
    return inputs, verdicts


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


def run_one(arg):
    yml, timeout = arg
    inputs, verdicts = resolve(yml)
    if inputs is None or verdicts.get("nre") is not True:
        return None  # only tasks whose expected answer is TRUE can be lost here
    try:
        r = subprocess.run(
            [AJAVE, "--property", "no-runtime-exception"] + inputs,
            capture_output=True, text=True, timeout=timeout,
        )
    except Exception:
        return None
    m = BLOCK_RE.search(r.stderr)
    if not m:
        return None
    cls, name, desc = m.group(1), m.group(2), m.group(3)
    return yml, f"{cls}.{name}{desc}"


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 25
    by_cat = defaultdict(list)
    for t in find_all_tasks():
        by_cat[category_of(t)].append(t)
    sample = []
    for cat, ts in by_cat.items():
        sample.extend(ts[:limit])

    print(f"Sampling {len(sample)} tasks (expected-TRUE only)\n")

    blocked = Counter()
    per_cat = defaultdict(Counter)
    n = 0
    with ProcessPoolExecutor(max_workers=6) as ex:
        futs = [ex.submit(run_one, (t, 60)) for t in sample]
        for f in as_completed(futs):
            res = f.result()
            if res is None:
                continue
            yml, sig = res
            n += 1
            blocked[sig] += 1
            per_cat[category_of(yml)][sig] += 1

    print(f"{n} task(s) lost a TRUE to an unmodelled throwing call\n")
    print("Blocking signatures, most costly first:")
    for sig, c in blocked.most_common(30):
        print(f"  {c:4d}  {sig}")

    print("\nPer category (top blocker):")
    for cat in sorted(per_cat):
        top = per_cat[cat].most_common(1)
        if top:
            sig, c = top[0]
            print(f"  {cat:<40s} {c:3d}x  {sig}")


if __name__ == "__main__":
    main()
