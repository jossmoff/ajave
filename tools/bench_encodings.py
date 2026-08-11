#!/usr/bin/env python3
"""
Benchmark harness for SMT encoding performance.

Each encoding is tested by running a representative autostub benchmark
and measuring solve time. Results are compared against baseline budgets
to detect performance regressions.

Usage:
    python3 tools/bench_encodings.py              # run all, show table
    python3 tools/bench_encodings.py --save       # save current times as baseline
    python3 tools/bench_encodings.py --category bit  # filter by category
"""

import json
import os
import subprocess
import sys
import time

ROAST = "./target/release/roast"
BASELINE_FILE = "tools/encoding_baselines.json"

# (category, method, benchmark_yml, timeout_budget_secs)
# timeout_budget is the max acceptable time; exceeding it = regression.
BENCHMARKS = [
    # ── Bit manipulation ─────────────────────────────────────────────
    ("bit", "Integer.bitCount",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_bitCount_int.yml", 10),
    ("bit", "Long.bitCount",
     "sv-benchmarks/autostub/Long_public_static_int_java_lang_Long_bitCount_long.yml", 10),
    ("bit", "Integer.reverse",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_reverse_int.yml", 30),
    ("bit", "Integer.reverseBytes",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_reverseBytes_int.yml", 10),
    ("bit", "Long.reverseBytes",
     "sv-benchmarks/autostub/Long_public_static_long_java_lang_Long_reverseBytes_long.yml", 10),
    ("bit", "Integer.highestOneBit",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_highestOneBit_int.yml", 10),
    ("bit", "Integer.lowestOneBit",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_lowestOneBit_int.yml", 10),
    ("bit", "Integer.numberOfLeadingZeros",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_numberOfLeadingZeros_int.yml", 30),
    ("bit", "Integer.numberOfTrailingZeros",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_numberOfTrailingZeros_int.yml", 30),
    ("bit", "Integer.rotateLeft",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_rotateLeft_int_int.yml", 10),
    ("bit", "Integer.rotateRight",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_rotateRight_int_int.yml", 10),

    # ── Arithmetic / compare ─────────────────────────────────────────
    ("arith", "Math.abs",
     "sv-benchmarks/autostub/Math_public_static_int_java_lang_Math_abs_int.yml", 10),
    ("arith", "Integer.compare",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_compare_int_int.yml", 10),
    ("arith", "Integer.compareUnsigned",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_compareUnsigned_int_int.yml", 10),
    ("arith", "Integer.max",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_max_int_int.yml", 10),
    ("arith", "Integer.min",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_min_int_int.yml", 10),
    ("arith", "Integer.sum",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_sum_int_int.yml", 10),
    ("arith", "Integer.signum",
     "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_signum_int.yml", 10),

    # ── Character methods ────────────────────────────────────────────
    ("char", "Character.isDigit",
     "sv-benchmarks/autostub/Character_public_static_boolean_java_lang_Character_isDigit_char.yml", 10),
    ("char", "Character.isLetter",
     "sv-benchmarks/autostub/Character_public_static_boolean_java_lang_Character_isLetter_char.yml", 10),
    ("char", "Character.isUpperCase",
     "sv-benchmarks/autostub/Character_public_static_boolean_java_lang_Character_isUpperCase_char.yml", 10),

    # ── toString / string encoding ───────────────────────────────────
    ("string", "Integer.toString",
     "sv-benchmarks/autostub/Integer_public_static_java_lang_String_java_lang_Integer_toString_int.yml", 60),
    ("string", "Integer.toOctalString",
     "sv-benchmarks/autostub/Integer_public_static_java_lang_String_java_lang_Integer_toOctalString_int.yml", 30),
    ("string", "Integer.toUnsignedString",
     "sv-benchmarks/autostub/Integer_public_static_java_lang_String_java_lang_Integer_toUnsignedString_int.yml", 30),
    ("string", "Integer.toUnsignedLong",
     "sv-benchmarks/autostub/Integer_public_static_long_java_lang_Integer_toUnsignedLong_int.yml", 10),
]


def resolve_inputs(yml_path):
    """Parse .yml to get input directories."""
    import yaml
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None
    task_dir = os.path.dirname(yml_path)
    return [os.path.join(task_dir, inp) for inp in data["input_files"]]


def run_benchmark(yml_path, timeout):
    """Run roast on a benchmark, return (verdict, elapsed_secs)."""
    inputs = resolve_inputs(yml_path)
    if inputs is None:
        return ("SKIP", 0.0)
    t0 = time.monotonic()
    try:
        r = subprocess.run(
            [ROAST] + inputs,
            capture_output=True, text=True, timeout=timeout + 5,
        )
        elapsed = time.monotonic() - t0
        verdict = r.stdout.strip().split("\n")[-1] if r.stdout.strip() else "ERROR"
        return (verdict, elapsed)
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - t0
        return ("TIMEOUT", elapsed)


def load_baselines():
    if os.path.exists(BASELINE_FILE):
        with open(BASELINE_FILE) as f:
            return json.load(f)
    return {}


def save_baselines(results):
    data = {}
    for cat, method, _, budget, verdict, elapsed in results:
        data[method] = {"time": round(elapsed, 2), "verdict": verdict}
    with open(BASELINE_FILE, "w") as f:
        json.dump(data, f, indent=2, sort_keys=True)
    print(f"\nBaselines saved to {BASELINE_FILE}")


def main():
    save = "--save" in sys.argv
    category_filter = None
    for i, arg in enumerate(sys.argv):
        if arg == "--category" and i + 1 < len(sys.argv):
            category_filter = sys.argv[i + 1]

    if not os.path.exists(ROAST):
        print(f"ERROR: {ROAST} not found. Run `cargo build --release` first.")
        sys.exit(1)

    baselines = load_baselines()
    results = []
    regressions = 0

    print(f"{'Method':<35} {'Verdict':<8} {'Time':>7} {'Budget':>7} {'Status'}")
    print("-" * 75)

    for cat, method, yml, budget in BENCHMARKS:
        if category_filter and category_filter not in cat:
            continue
        if not os.path.exists(yml):
            print(f"{method:<35} {'MISSING':<8} {'—':>7} {budget:>5}s  SKIP")
            continue

        verdict, elapsed = run_benchmark(yml, budget)
        status = ""

        if verdict == "TIMEOUT":
            status = "TIMEOUT"
        elif elapsed > budget:
            status = "OVER BUDGET"
            regressions += 1
        elif method in baselines:
            bl = baselines[method]["time"]
            ratio = elapsed / bl if bl > 0 else 1.0
            if ratio > 2.0:
                status = f"REGRESSED (was {bl:.1f}s)"
                regressions += 1
            elif ratio < 0.5:
                status = f"FASTER (was {bl:.1f}s)"
            else:
                status = "OK"
        else:
            status = "NEW"

        print(f"{method:<35} {verdict:<8} {elapsed:>6.1f}s {budget:>5}s  {status}")
        results.append((cat, method, yml, budget, verdict, elapsed))

    total = len(results)
    solved = sum(1 for _, _, _, _, v, _ in results if v in ("TRUE", "FALSE"))
    print(f"\n{solved}/{total} solved, {regressions} regressions")

    if save:
        save_baselines(results)

    sys.exit(1 if regressions > 0 else 0)


if __name__ == "__main__":
    main()
