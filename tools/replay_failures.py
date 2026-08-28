#!/usr/bin/env python3
"""Classify why FALSE verdicts get downgraded to UNKNOWN by JVM replay.

76% of valid-assert UNKNOWNs have no open obligations: an engine found a real
violation, the JVM refused to reproduce it from our witness, and we downgraded.
That is the single biggest bucket of lost points, so it is worth knowing which
*kind* of witness fails rather than guessing.

For each sampled task we re-run with -vv, keep only those that downgraded, and
bucket by the shape of the witness and the obligation:

  no-entries    witness carries no nondet values at all — nothing to replay,
                so the violation depends on state we never recorded
  float         witness assigns a float/double nondet (BMC's bitvector float
                encoding not matching IEEE 754 is a known failure mode)
  string        witness assigns a string (passed via -Dajave.str.N, and our
                string modelling is partial)
  int-only      only integer nondets — these *should* replay, so a failure
                here points at a modelling divergence rather than encoding

Usage: python3 tools/replay_failures.py [property] [per_category_limit]
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

DOWNGRADE = "downgrading FALSE to UNKNOWN"
REFUTED_RE = re.compile(r"jvm-replay: Refuted for (\S+)")
# `--show-witness` style debug line from the blackboard artifact dump.
ENTRY_RE = re.compile(r"NondetEntry \{ value: (\w+)\(([^)]*)\), nondet_method: \"(\w+)\"")
KIND_RE = re.compile(r"kind=(\w+)")


def resolve(yml_path):
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None, None
    d = os.path.dirname(yml_path)
    inputs = [os.path.join(d, i) for i in data["input_files"]]
    verdicts = {}
    for p in data.get("properties", []):
        pf = p.get("property_file", "")
        if "valid-assert" in pf:
            verdicts["assert"] = p.get("expected_verdict")
        elif "no-runtime-exception" in pf:
            verdicts["no-runtime-exception"] = p.get("expected_verdict")
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
    yml, prop, timeout = arg
    inputs, verdicts = resolve(yml)
    if inputs is None or verdicts.get(prop) is None:
        return None
    # Only tasks whose expected answer is FALSE can be lost this way.
    if verdicts[prop] is not False:
        return None
    try:
        r = subprocess.run(
            [AJAVE, "-vv", "--property", prop, "--show-witness"] + inputs,
            capture_output=True, text=True, timeout=timeout,
        )
    except Exception:
        return None

    verdict = r.stdout.strip().split("\n")[-1] if r.stdout.strip() else "ERROR"
    log = r.stderr + r.stdout
    if verdict != "UNKNOWN" or DOWNGRADE not in log:
        return None

    kinds = Counter(v for v in ENTRY_RE.findall(log) for v in [v[0]])
    methods = Counter(m[2] for m in ENTRY_RE.findall(log))

    if not kinds:
        bucket = "no-entries"
    elif any(k in ("Float", "Double") for k in kinds):
        bucket = "float"
    elif "Str" in kinds:
        bucket = "string"
    else:
        bucket = "int-only"

    return yml, bucket, methods


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else "both"
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    props = ["assert", "no-runtime-exception"] if arg == "both" else [arg]

    by_cat = defaultdict(list)
    for t in find_all_tasks():
        by_cat[category_of(t)].append(t)
    sample = []
    for cat, ts in by_cat.items():
        sample.extend(ts[:limit])

    print(f"sampling {len(sample)} tasks per property: {', '.join(props)}")
    print("keeping only expected-FALSE tasks we downgraded to UNKNOWN")
    print("(only those are recoverable — where the expected verdict is TRUE,")
    print(" replay was correctly rejecting a spurious violation)\n")

    grand = Counter()
    for prop in props:
        buckets = Counter()
        per_cat = defaultdict(Counter)
        methods = Counter()
        examples = defaultdict(list)

        with ProcessPoolExecutor(max_workers=6) as ex:
            futs = [ex.submit(run_one, (t, prop, 60)) for t in sample]
            for f in as_completed(futs):
                res = f.result()
                if res is None:
                    continue
                yml, bucket, ms = res
                buckets[bucket] += 1
                per_cat[category_of(yml)][bucket] += 1
                methods.update(ms)
                if len(examples[bucket]) < 4:
                    examples[bucket].append(os.path.basename(yml))

        total = sum(buckets.values()) or 1
        print("=" * 70)
        print(f"  {prop}")
        print("=" * 70)
        print(f"Downgraded FALSE->UNKNOWN: {sum(buckets.values())} tasks\n")
        print("By witness shape:")
        for b, n in buckets.most_common():
            print(f"  {b:<12s} {n:4d}  ({100*n/total:4.1f}%)   e.g. {', '.join(examples[b][:3])}")
            grand[f"{prop}:{b}"] += n

        print("\nBy category:")
        for cat in sorted(per_cat):
            top = ", ".join(f"{k}={v}" for k, v in per_cat[cat].most_common())
            print(f"  {cat:<40s} {top}")

        if methods:
            print("\nNondet methods appearing in failing witnesses:")
            for m, n in methods.most_common(12):
                print(f"  {m:<28s} {n:5d}")
        print()

    if len(props) > 1:
        print("=" * 70)
        print("  COMBINED — recoverable points by witness shape")
        print("=" * 70)
        # valid-assert FALSE scores +1, no-runtime-exception FALSE scores +1.
        for k, n in grand.most_common():
            print(f"  {k:<40s} {n:4d} tasks  (~{n} pts)")
        print(f"\n  TOTAL recoverable: {sum(grand.values())} tasks")


if __name__ == "__main__":
    main()
