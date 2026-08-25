#!/usr/bin/env python3
"""Score roast against the SV-COMP ReachSafety-Java benchmark subset."""

import os
import subprocess
import sys
import yaml
import glob
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

TIMEOUT = 60  # seconds per task
ROAST = "./target/release/ajave"

# From sv-benchmarks/ReachSafety-Java.set
REACHSAFETY_PATTERNS = [
    "jayhorn-recursive/*.yml",
    "jbmc-regression/*.yml",
    "jpf-regression/*.yml",
    "java-ranger-regression/*.yml",
    "java-ranger-regression/WBS/*.yml",
    "java-ranger-regression/alarm/*.yml",
    "java-ranger-regression/infusion/*.yml",
    "java-ranger-regression/siena_eqchk/*.yml",
    "java-ranger-regression/replace5_eqchk/*.yml",
    "java-ranger-regression/nanoxml_eqchk/*.yml",
    "java-ranger-regression/printtokens_eqchk/*.yml",
    "MinePump/*.yml",
    "algorithms/*.yml",
    "juliet-java/*.yml",
    "jdart-regression/*.yml",
    "securibench/*.yml",
    "float_unboundedloop/*.yml",
    "float-nonlinear-calculation/*.yml",
    "argv-tasks/*.yml",
    "autostub/*.yml",
    "objects/*.yml",
]

def find_tasks():
    tasks = []
    seen = set()
    for pattern in REACHSAFETY_PATTERNS:
        full = os.path.join("sv-benchmarks", pattern)
        for yml in sorted(glob.glob(full)):
            if yml in seen:
                continue
            seen.add(yml)
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
    print(f"Found {len(tasks)} ReachSafety valid-assert tasks")
    print(f"  Expected TRUE: {sum(1 for _,e,_ in tasks if e)}")
    print(f"  Expected FALSE: {sum(1 for _,e,_ in tasks if not e)}")
    print()

    # Group by benchmark directory for per-category reporting
    categories = {}
    for yml, ev, inputs in tasks:
        # Extract category from path: sv-benchmarks/<category>/...
        parts = yml.split(os.sep)
        if len(parts) >= 3:
            cat = parts[1]
            # Sub-categories for java-ranger-regression
            if cat == "java-ranger-regression" and len(parts) >= 4:
                cat = f"java-ranger-regression/{parts[2]}"
        else:
            cat = "unknown"
        if cat not in categories:
            categories[cat] = {"true": 0, "false": 0, "total": 0}
        categories[cat]["total"] += 1
        if ev:
            categories[cat]["true"] += 1
        else:
            categories[cat]["false"] += 1

    results = {"correct_true": 0, "correct_false": 0,
               "wrong_true": 0, "wrong_false": 0,
               "unknown": 0, "timeout": 0, "error": 0}
    wrong_list = []
    correct_true_list = []
    correct_false_list = []
    unknown_list = []
    timeout_list = []
    cat_results = {}  # category -> {correct_true, correct_false, wrong_true, wrong_false, unknown, timeout}
    score = 0

    start = time.time()
    with ThreadPoolExecutor(max_workers=16) as pool:
        futures = {pool.submit(run_task, y, e, i): (y, e, i) for y, e, i in tasks}
        done = 0
        for f in as_completed(futures):
            done += 1
            yml, expected, verdict = f.result()
            name = os.path.basename(yml).replace(".yml", "")

            # Determine category
            parts = yml.split(os.sep)
            if len(parts) >= 3:
                cat = parts[1]
                if cat == "java-ranger-regression" and len(parts) >= 4:
                    cat = f"java-ranger-regression/{parts[2]}"
            else:
                cat = "unknown"
            if cat not in cat_results:
                cat_results[cat] = {"correct_true": 0, "correct_false": 0,
                                    "wrong_true": 0, "wrong_false": 0,
                                    "unknown": 0, "timeout": 0}

            expected_str = "TRUE" if expected else "FALSE"

            if verdict == "TIMEOUT":
                results["timeout"] += 1
                cat_results[cat]["timeout"] += 1
                timeout_list.append(f"{name} (expected {expected_str})")
            elif verdict in ("ERROR", ""):
                results["error"] += 1
            elif verdict == "TRUE":
                if expected:
                    results["correct_true"] += 1
                    cat_results[cat]["correct_true"] += 1
                    score += 2
                    correct_true_list.append(name)
                else:
                    results["wrong_true"] += 1
                    cat_results[cat]["wrong_true"] += 1
                    score -= 16
                    wrong_list.append(f"  {name}: said TRUE, expected FALSE")
            elif verdict == "FALSE":
                if not expected:
                    results["correct_false"] += 1
                    cat_results[cat]["correct_false"] += 1
                    score += 1
                    correct_false_list.append(name)
                else:
                    results["wrong_false"] += 1
                    cat_results[cat]["wrong_false"] += 1
                    score -= 32
                    wrong_list.append(f"  {name}: said FALSE, expected TRUE")
            elif verdict == "UNKNOWN":
                results["unknown"] += 1
                cat_results[cat]["unknown"] += 1
                unknown_list.append(f"{name} (expected {expected_str})")

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
    print(f"{'Category':<40} {'cT':>3} {'cF':>3} {'wT':>3} {'wF':>3} {'UNK':>4} {'TO':>3} {'Score':>6}")
    print(f"{'-'*40} {'-'*3} {'-'*3} {'-'*3} {'-'*3} {'-'*4} {'-'*3} {'-'*6}")
    for cat in sorted(cat_results.keys()):
        r = cat_results[cat]
        cat_score = r["correct_true"]*2 + r["correct_false"] - r["wrong_true"]*16 - r["wrong_false"]*32
        total = sum(r.values())
        print(f"  {cat:<38} {r['correct_true']:3d} {r['correct_false']:3d} {r['wrong_true']:3d} {r['wrong_false']:3d} {r['unknown']:4d} {r['timeout']:3d} {cat_score:>+6d}")
    print(f"{'-'*40} {'-'*3} {'-'*3} {'-'*3} {'-'*3} {'-'*4} {'-'*3} {'-'*6}")
    total_score = results["correct_true"]*2 + results["correct_false"] - results["wrong_true"]*16 - results["wrong_false"]*32
    print(f"  {'TOTAL':<38} {results['correct_true']:3d} {results['correct_false']:3d} {results['wrong_true']:3d} {results['wrong_false']:3d} {results['unknown']:4d} {results['timeout']:3d} {total_score:>+6d}")

    if wrong_list:
        print(f"\nWRONG ANSWERS ({len(wrong_list)}):")
        for w in sorted(wrong_list):
            print(w)

    if unknown_list:
        print(f"\nUNKNOWN ({len(unknown_list)}):")
        for u in sorted(unknown_list):
            print(f"  {u}")

if __name__ == "__main__":
    main()
