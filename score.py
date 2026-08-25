#!/usr/bin/env python3
"""Score roast against the full SV-COMP Java valid-assert benchmark suite."""

import os
import subprocess
import sys
import yaml
import glob
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

TIMEOUT = 60  # seconds per task
ROAST = "./target/release/ajave"

def find_tasks():
    tasks = []
    for yml in sorted(glob.glob("sv-benchmarks/**/*.yml", recursive=True)):
        try:
            with open(yml) as f:
                data = yaml.safe_load(f)
            if not data or "properties" not in data:
                continue
            for prop in data["properties"]:
                pf = prop.get("property_file", "")
                if "valid-assert" not in pf:
                    continue
                ev = prop.get("expected_verdict")
                if ev is None:
                    continue
                task_dir = os.path.dirname(yml)
                inputs = data.get("input_files", [])
                # Resolve input paths relative to the yml directory
                resolved = []
                for inp in inputs:
                    resolved.append(os.path.join(task_dir, inp))
                tasks.append((yml, ev, resolved))
        except Exception:
            pass
    return tasks

def run_task(yml, expected, inputs):
    try:
        result = subprocess.run(
            [ROAST] + inputs,
            capture_output=True, text=True, timeout=TIMEOUT
        )
        verdict = result.stdout.strip().split("\n")[-1] if result.stdout.strip() else "ERROR"
    except subprocess.TimeoutExpired:
        verdict = "TIMEOUT"
    except Exception as e:
        verdict = "ERROR"
    return yml, expected, verdict

def main():
    tasks = find_tasks()
    print(f"Found {len(tasks)} valid-assert tasks")
    print(f"  Expected TRUE: {sum(1 for _,e,_ in tasks if e)}")
    print(f"  Expected FALSE: {sum(1 for _,e,_ in tasks if not e)}")
    print()

    results = {"correct_true": 0, "correct_false": 0,
               "wrong_true": 0, "wrong_false": 0,
               "unknown": 0, "timeout": 0, "error": 0}
    wrong_list = []
    correct_false_list = []
    score = 0

    start = time.time()
    with ThreadPoolExecutor(max_workers=16) as pool:
        futures = {pool.submit(run_task, y, e, i): (y, e) for y, e, i in tasks}
        done = 0
        for f in as_completed(futures):
            done += 1
            yml, expected, verdict = f.result()
            name = os.path.basename(yml).replace(".yml", "")
            expected_str = "TRUE" if expected else "FALSE"

            if verdict == "TIMEOUT":
                results["timeout"] += 1
            elif verdict in ("ERROR", ""):
                results["error"] += 1
            elif verdict == "TRUE":
                if expected:
                    results["correct_true"] += 1
                    score += 2
                else:
                    results["wrong_true"] += 1
                    score -= 16
                    wrong_list.append(f"  {name}: said TRUE, expected FALSE")
            elif verdict == "FALSE":
                if not expected:
                    results["correct_false"] += 1
                    score += 1
                    correct_false_list.append(name)
                else:
                    results["wrong_false"] += 1
                    score -= 32
                    wrong_list.append(f"  {name}: said FALSE, expected TRUE")
            elif verdict == "UNKNOWN":
                results["unknown"] += 1

            status = "✓" if (verdict == "TRUE" and expected) or (verdict == "FALSE" and not expected) else \
                     "✗" if (verdict == "TRUE" and not expected) or (verdict == "FALSE" and expected) else \
                     "·"
            elapsed = time.time() - start
            print(f"  {status} [{done}/{len(tasks)}] {name}: {verdict} (expected {expected_str}) [{elapsed:.0f}s] score={score}", file=sys.stderr)

    elapsed = time.time() - start
    print(f"\nResults ({elapsed:.0f}s):")
    print(f"  Correct TRUE:  {results['correct_true']:4d}  (+{results['correct_true']*2})")
    print(f"  Correct FALSE: {results['correct_false']:4d}  (+{results['correct_false']})")
    print(f"  Wrong TRUE:    {results['wrong_true']:4d}  (-{results['wrong_true']*16})")
    print(f"  Wrong FALSE:   {results['wrong_false']:4d}  (-{results['wrong_false']*32})")
    print(f"  UNKNOWN:       {results['unknown']:4d}")
    print(f"  TIMEOUT:       {results['timeout']:4d}")
    print(f"  ERROR:         {results['error']:4d}")
    print(f"\n  TOTAL SCORE: {score}")

    if wrong_list:
        print(f"\nWRONG ANSWERS ({len(wrong_list)}):")
        for w in sorted(wrong_list):
            print(w)

    if correct_false_list:
        print(f"\nCORRECT FALSE ({len(correct_false_list)}):")
        for c in sorted(correct_false_list):
            print(f"  {c}")

if __name__ == "__main__":
    main()
