#!/usr/bin/env python3
"""Full scoring harness for ajave against SV-COMP Java benchmarks.

Usage:
    python3 tools/score_full.py                           # both properties
    python3 tools/score_full.py --property valid-assert   # one property
    python3 tools/score_full.py --property no-runtime-exception
    python3 tools/score_full.py --timeout 90              # custom timeout (default 60)
    python3 tools/score_full.py --parallel 4              # parallel workers (default 4)
"""

import glob
import os
import subprocess
import sys
import time
import yaml
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed

ROAST = "./target/release/ajave"
DEFAULT_TIMEOUT = 60
SV_BENCHMARKS = "sv-benchmarks"
SET_FILE = os.path.join(SV_BENCHMARKS, "ReachSafety-Java.set")

def resolve_inputs(yml_path):
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None, None, None
    task_dir = os.path.dirname(yml_path)
    inputs = [os.path.join(task_dir, inp) for inp in data["input_files"]]
    props = data.get("properties", [])
    result = {}
    for p in props:
        pfile = p.get("property_file", "")
        expected = p.get("expected_verdict")
        if "valid-assert" in pfile:
            result["valid-assert"] = expected
        elif "no-runtime-exception" in pfile:
            result["no-runtime-exception"] = expected
    return inputs, result, data

def find_all_tasks():
    """Find all .yml tasks from the set file."""
    tasks = []
    with open(SET_FILE) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            pattern = os.path.join(SV_BENCHMARKS, line)
            for yml in sorted(glob.glob(pattern)):
                tasks.append(yml)
    return tasks

def run_one(args):
    yml_path, prop, timeout = args
    inputs, verdicts, _ = resolve_inputs(yml_path)
    if inputs is None:
        return yml_path, prop, None, "SKIP", 0
    expected = verdicts.get(prop)
    if expected is None:
        return yml_path, prop, None, "SKIP", 0
    expected_str = "TRUE" if expected else "FALSE"
    try:
        cmd = [ROAST, "--property", prop] + inputs
        t0 = time.time()
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        elapsed = time.time() - t0
        verdict = result.stdout.strip().split("\n")[-1] if result.stdout.strip() else "ERROR"
        return yml_path, prop, expected_str, verdict, elapsed
    except subprocess.TimeoutExpired:
        return yml_path, prop, expected_str, "TIMEOUT", timeout
    except Exception:
        return yml_path, prop, expected_str, "ERROR", 0

def category_of(yml_path):
    # Extract category from path: sv-benchmarks/CATEGORY/...
    rel = os.path.relpath(yml_path, SV_BENCHMARKS)
    parts = rel.split(os.sep)
    if len(parts) >= 2:
        cat = parts[0]
        if len(parts) >= 3 and parts[0] in ("java-ranger-regression",):
            cat = f"{parts[0]}/{parts[1]}"
        return cat
    return "other"

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--property", choices=["valid-assert", "no-runtime-exception"])
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    parser.add_argument("--parallel", type=int, default=4)
    args = parser.parse_args()

    props = [args.property] if args.property else ["valid-assert", "no-runtime-exception"]

    if not os.path.exists(ROAST):
        print(f"Binary not found: {ROAST}")
        sys.exit(1)

    tasks = find_all_tasks()
    print(f"Found {len(tasks)} benchmark files")

    for prop in props:
        print(f"\n{'='*70}")
        print(f"  SCORING: {prop}")
        print(f"{'='*70}")

        # Build work items
        work = [(yml, prop, args.timeout) for yml in tasks]

        results = []
        t0 = time.time()

        with ProcessPoolExecutor(max_workers=args.parallel) as pool:
            futures = {pool.submit(run_one, w): w for w in work}
            done_count = 0
            for fut in as_completed(futures):
                yml, p, expected, verdict, elapsed = fut.result()
                if expected is None:
                    continue
                done_count += 1
                results.append((yml, expected, verdict, elapsed))
                name = os.path.basename(yml).replace(".yml", "")
                if verdict == expected:
                    sym = "✓"
                elif verdict in ("UNKNOWN", "TIMEOUT", "ERROR"):
                    sym = "·"
                else:
                    sym = "✗"
                # Print progress every 50
                if done_count % 50 == 0:
                    print(f"  ... {done_count} done")

        total_time = time.time() - t0

        # Tally
        correct_true = 0
        correct_false = 0
        wrong_true = 0
        wrong_false = 0
        unknowns = 0
        timeouts = 0
        errors = 0
        wrong_list = []
        cat_stats = defaultdict(lambda: {"cT": 0, "cF": 0, "wT": 0, "wF": 0, "UNK": 0, "TO": 0})

        for yml, expected, verdict, elapsed in results:
            cat = category_of(yml)
            name = os.path.basename(yml).replace(".yml", "")
            cs = cat_stats[cat]

            if verdict == expected:
                if expected == "TRUE":
                    correct_true += 1
                    cs["cT"] += 1
                else:
                    correct_false += 1
                    cs["cF"] += 1
            elif verdict == "TIMEOUT":
                timeouts += 1
                cs["TO"] += 1
            elif verdict in ("UNKNOWN", "ERROR"):
                unknowns += 1
                cs["UNK"] += 1
            elif verdict == "TRUE" and expected == "FALSE":
                wrong_true += 1
                cs["wT"] += 1
                wrong_list.append((name, "TRUE", "FALSE"))
            elif verdict == "FALSE" and expected == "TRUE":
                wrong_false += 1
                cs["wF"] += 1
                wrong_list.append((name, "FALSE", "TRUE"))

        score = correct_true * 2 + correct_false - wrong_true * 16 - wrong_false * 32

        print(f"\nResults ({total_time:.0f}s):")
        print(f"  Correct TRUE:  {correct_true:4d}  (+{correct_true*2})")
        print(f"  Correct FALSE: {correct_false:4d}  (+{correct_false})")
        print(f"  Wrong TRUE:    {wrong_true:4d}  (-{wrong_true*16})")
        print(f"  Wrong FALSE:   {wrong_false:4d}  (-{wrong_false*32})")
        print(f"  UNKNOWN:       {unknowns:4d}")
        print(f"  TIMEOUT:       {timeouts:4d}")
        print(f"  TOTAL SCORE: {score}")

        print(f"\n{'Category':<45s} {'cT':>3s} {'cF':>3s} {'wT':>3s} {'wF':>3s} {'UNK':>4s} {'TO':>3s} {'Score':>6s}")
        print("-" * 75)
        for cat in sorted(cat_stats.keys()):
            cs = cat_stats[cat]
            s = cs["cT"]*2 + cs["cF"] - cs["wT"]*16 - cs["wF"]*32
            print(f"  {cat:<43s} {cs['cT']:3d} {cs['cF']:3d} {cs['wT']:3d} {cs['wF']:3d} {cs['UNK']:4d} {cs['TO']:3d} {s:>+6d}")

        if wrong_list:
            print(f"\nWRONG ANSWERS ({len(wrong_list)}):")
            for name, said, expected in wrong_list:
                print(f"  {name}: said {said}, expected {expected}")

if __name__ == "__main__":
    main()
