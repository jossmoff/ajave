#!/usr/bin/env python3
"""Score roast against the SV-COMP Java no-runtime-exception benchmark suite."""

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
                if "no-runtime-exception" not in pf:
                    continue
                ev = prop.get("expected_verdict")
                if ev is None:
                    continue
                task_dir = os.path.dirname(yml)
                inputs = data.get("input_files", [])
                resolved = [os.path.join(task_dir, inp) for inp in inputs]
                tasks.append((yml, ev, resolved))
        except Exception:
            pass
    return tasks

def run_task(yml, expected, inputs):
    try:
        result = subprocess.run(
            [ROAST, "--property", "no-runtime-exception"] + inputs,
            capture_output=True, text=True, timeout=TIMEOUT
        )
        verdict = result.stdout.strip().split("\n")[-1] if result.stdout.strip() else "ERROR"
    except subprocess.TimeoutExpired:
        verdict = "TIMEOUT"
    except Exception:
        verdict = "ERROR"
    return yml, expected, verdict

def main():
    tasks = find_tasks()
    print(f"Found {len(tasks)} no-runtime-exception tasks")
    print(f"  Expected TRUE: {sum(1 for _,e,_ in tasks if e)}")
    print(f"  Expected FALSE: {sum(1 for _,e,_ in tasks if not e)}")
    print()

    results = {"correct_true": 0, "correct_false": 0,
               "wrong_true": 0, "wrong_false": 0,
               "unknown": 0, "timeout": 0, "error": 0}
    wrong_list = []
    unknown_list = []
    # Per-category stats
    categories = {}
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

            # Category from path
            rel = os.path.relpath(yml, "sv-benchmarks")
            cat = os.path.dirname(rel)

            if cat not in categories:
                categories[cat] = {"cT": 0, "cF": 0, "wT": 0, "wF": 0, "UNK": 0, "TO": 0}

            if verdict == "TIMEOUT":
                results["timeout"] += 1
                categories[cat]["TO"] += 1
            elif verdict in ("ERROR", ""):
                results["error"] += 1
            elif verdict == "TRUE":
                if expected:
                    results["correct_true"] += 1
                    score += 2
                    categories[cat]["cT"] += 1
                else:
                    results["wrong_true"] += 1
                    score -= 16
                    wrong_list.append(f"  {name}: said TRUE, expected FALSE")
                    categories[cat]["wT"] += 1
            elif verdict == "FALSE":
                if not expected:
                    results["correct_false"] += 1
                    score += 1
                    categories[cat]["cF"] += 1
                else:
                    results["wrong_false"] += 1
                    score -= 32
                    wrong_list.append(f"  {name}: said FALSE, expected TRUE")
                    categories[cat]["wF"] += 1
            elif verdict == "UNKNOWN":
                results["unknown"] += 1
                categories[cat]["UNK"] += 1
                unknown_list.append(f"  {name} (expected {expected_str})")

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

    # Per-category breakdown
    print(f"\n{'='*70}")
    print("PER-CATEGORY BREAKDOWN:")
    print(f"{'='*70}")
    print(f"{'Category':<40s} {'cT':>3s} {'cF':>3s} {'wT':>3s} {'wF':>3s} {'UNK':>4s} {'TO':>3s} {'Score':>6s}")
    print("-"*40, "---", "---", "---", "---", "----", "---", "------")
    for cat in sorted(categories.keys()):
        c = categories[cat]
        cat_score = c["cT"]*2 + c["cF"] - c["wT"]*16 - c["wF"]*32
        print(f"  {cat:<38s} {c['cT']:3d} {c['cF']:3d} {c['wT']:3d} {c['wF']:3d} {c['UNK']:4d} {c['TO']:3d}  {'+' if cat_score >= 0 else ''}{cat_score}")
    print("-"*40, "---", "---", "---", "---", "----", "---", "------")
    print(f"  {'TOTAL':<38s} {results['correct_true']:3d} {results['correct_false']:3d} {results['wrong_true']:3d} {results['wrong_false']:3d} {results['unknown']:4d} {results['timeout']:3d}  {'+' if score >= 0 else ''}{score}")

    if wrong_list:
        print(f"\nWRONG ANSWERS ({len(wrong_list)}):")
        for w in sorted(wrong_list):
            print(w)

    if unknown_list:
        print(f"\nUNKNOWN ({len(unknown_list)}):")
        for u in sorted(unknown_list):
            print(u)

if __name__ == "__main__":
    main()
