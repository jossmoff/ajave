#!/usr/bin/env python3
"""Fast smoke test for roast engine changes.

Run this BEFORE full scoring to catch regressions early. Tests a curated set
of benchmarks that exercise sensitive engine behaviors:

  - Exhaustive discharge (TRUE verdicts via all_paths_complete)
  - Exception handling (throw/catch dispatch)
  - Float/double operations (havoced, tainted branches)
  - Virtual dispatch + inlining
  - Tainted branch merging (diamond merge)
  - String operations
  - autostub wrapper methods
  - Wrong-answer canaries (known-tricky benchmarks)

Usage:
    python3 tools/smoke_test.py [--binary ./target/release/roast]

Exit code 0 = all pass, 1 = regressions detected.
"""

import os
import subprocess
import sys
import time

ROAST = sys.argv[2] if len(sys.argv) > 2 and sys.argv[1] == "--binary" else "./target/release/roast"
TIMEOUT = 60

# Each entry: (category, benchmark_yml_path, expected_verdict)
# These are chosen to cover sensitive engine behaviors.
TESTS = [
    # ── Exhaustive discharge (TRUE) ──────────────────────────────────────
    ("exhaust-true", "sv-benchmarks/jbmc-regression/lookupswitch1.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/virtual1.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/virtual4.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/tableswitch1.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/swap1.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/overloading1.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/putfield_getfield1.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/putstatic_getstatic1.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/package1.yml", "TRUE"),
    ("exhaust-true", "sv-benchmarks/jbmc-regression/uninitialised1.yml", "TRUE"),

    # ── Exhaustive discharge (FALSE) ─────────────────────────────────────
    ("exhaust-false", "sv-benchmarks/jbmc-regression/assert2.yml", "FALSE"),
    ("exhaust-false", "sv-benchmarks/jbmc-regression/assert3.yml", "FALSE"),
    ("exhaust-false", "sv-benchmarks/jbmc-regression/assert4.yml", "FALSE"),
    ("exhaust-false", "sv-benchmarks/jbmc-regression/virtual2.yml", "FALSE"),

    # ── Exception handling ───────────────────────────────────────────────
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions1.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions2.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions3.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions6.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions7.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions8.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions10.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions11.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions12.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions13.yml", "FALSE"),
    ("exceptions", "sv-benchmarks/jbmc-regression/exceptions16.yml", "FALSE"),

    # ── JPF symbolic execution (TRUE + FALSE) ────────────────────────────
    ("jpf-true", "sv-benchmarks/jpf-regression/ExDarko_true.yml", "TRUE"),
    ("jpf-true", "sv-benchmarks/jpf-regression/ExSymExe1_true.yml", "TRUE"),
    ("jpf-true", "sv-benchmarks/jpf-regression/ExSymExeLCMP_true.yml", "TRUE"),
    ("jpf-true", "sv-benchmarks/jpf-regression/ExSymExeGetStatic_true.yml", "TRUE"),
    ("jpf-true", "sv-benchmarks/jpf-regression/ExSymExeLongBytecodes_true.yml", "TRUE"),
    ("jpf-false", "sv-benchmarks/jpf-regression/ExDarko_false.yml", "FALSE"),
    ("jpf-false", "sv-benchmarks/jpf-regression/ExSymExe1_false.yml", "FALSE"),
    ("jpf-false", "sv-benchmarks/jpf-regression/ExSymExeLCMP_false.yml", "FALSE"),

    # ── Float/coral (tainted branches, NRA) ──────────────────────────────
    ("float", "sv-benchmarks/float-nonlinear-calculation/coral1.yml", "FALSE"),
    ("float", "sv-benchmarks/float-nonlinear-calculation/coral4.yml", "FALSE"),

    # ── Autostub wrapper methods ─────────────────────────────────────────
    ("autostub", "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_reverseBytes_int.yml", "FALSE"),
    ("autostub", "sv-benchmarks/autostub/Long_public_static_long_java_lang_Long_reverseBytes_long.yml", "FALSE"),
    ("autostub", "sv-benchmarks/autostub/Integer_public_static_int_java_lang_Integer_compare_int_int.yml", "FALSE"),
    ("autostub", "sv-benchmarks/autostub/Boolean_public_static_boolean_java_lang_Boolean_logicalAnd_boolean_boolean.yml", "FALSE"),
    ("autostub", "sv-benchmarks/autostub/Character_public_static_boolean_java_lang_Character_isDigit_char.yml", "FALSE"),
    ("autostub", "sv-benchmarks/autostub/Math_public_static_int_java_lang_Math_abs_int.yml", "FALSE"),

    # ── MinePump (FALSE, complex switch/branch) ──────────────────────────
    ("minepump", "sv-benchmarks/MinePump/spec1-5_product1.yml", "FALSE"),
    ("minepump", "sv-benchmarks/MinePump/spec1-5_product24.yml", "FALSE"),

    # ── String operations ────────────────────────────────────────────────
    ("string", "sv-benchmarks/jbmc-regression/StringCompare02.yml", "FALSE"),
    ("string", "sv-benchmarks/jbmc-regression/StringContains01.yml", "FALSE"),
    # StringBuilder: constructor + charAt + indexOf
    ("string", "sv-benchmarks/jbmc-regression/StringBuilderConstructors01.yml", "TRUE"),
    ("string", "sv-benchmarks/jbmc-regression/StringBuilderConstructors02.yml", "FALSE"),
    ("string", "sv-benchmarks/jbmc-regression/StringBuilderAppend02.yml", "FALSE"),
    # String comparison: compareTo, startsWith, endsWith
    ("string", "sv-benchmarks/jbmc-regression/StringCompare04.yml", "FALSE"),
    ("string", "sv-benchmarks/jbmc-regression/StringStartEnd02.yml", "FALSE"),
    # String indexOf
    ("string", "sv-benchmarks/jbmc-regression/StringIndexMethods01.yml", "TRUE"),
    ("string", "sv-benchmarks/jbmc-regression/StringIndexMethods02.yml", "FALSE"),
    # String valueOf
    ("string", "sv-benchmarks/jbmc-regression/StringValueOf06.yml", "FALSE"),

    # ── Wrong-answer canaries (must NOT be wrong) ────────────────────────
    # compareTo/compareToIgnoreCase: sign-only encoding caused wrong TRUE
    ("canary", "sv-benchmarks/autostub/String_public_int_java_lang_String_compareTo_java_lang_String.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/String_public_int_java_lang_String_compareToIgnoreCase_java_lang_String.yml", "FALSE"),
    # These have been wrong in the past. They should be UNKNOWN or correct.
    # StringValueOf07: was wrong TRUE (signed_bv_to_str BV32/BV64 sort mismatch)
    ("canary", "sv-benchmarks/jbmc-regression/StringValueOf07.yml", "FALSE"),
    # Inter13, Refl3: fixed to UNKNOWN by all_calls_resolved tightening.
    ("canary", "sv-benchmarks/securibench/Inter13.yml", "FALSE"),
    ("canary", "sv-benchmarks/securibench/Refl3.yml", "FALSE"),
    ("canary", "sv-benchmarks/juliet-java/CWE369_Divide_by_Zero__float_connect_tcp_divide_01_bad.yml", "FALSE"),

    # VelocityTracker: was wrong TRUE (Unknown solver result not skipped)
    ("canary", "sv-benchmarks/argv-tasks/VelocityTracker_false.yml", "FALSE"),
    # Base64, StrictLineReader: were wrong FALSE (non-seeded obligations leaked)
    ("canary", "sv-benchmarks/argv-tasks/Base64.yml", "TRUE"),
    ("canary", "sv-benchmarks/argv-tasks/StrictLineReader.yml", "TRUE"),
    # StrongUpdates5: was wrong FALSE (non-seeded NullDeref leaked)
    ("canary", "sv-benchmarks/securibench/StrongUpdates5.yml", "TRUE"),
    # MathHelper_true: was wrong TRUE (NRA discharged over reals, not IEEE 754)
    ("canary", "sv-benchmarks/argv-tasks/MathHelper_true.yml", "FALSE"),

    # Byte/Short/Character compareTo: were UNKNOWN (missing from math_call_modelled)
    ("canary", "sv-benchmarks/autostub/Byte_public_int_java_lang_Byte_compareTo_java_lang_Byte.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/Short_public_int_java_lang_Short_compareTo_java_lang_Short.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/Character_public_int_java_lang_Character_compareTo_java_lang_Character.yml", "FALSE"),
    # Character.toString: was wrong TRUE (fresh string, not str.from_code)
    ("canary", "sv-benchmarks/autostub/Character_public_java_lang_String_java_lang_Character_toString.yml", "FALSE"),
    # highestOneBit: ITE cascade was in wrong order (LSB winning, not MSB)
    ("canary", "sv-benchmarks/autostub/Long_public_static_long_java_lang_Long_highestOneBit_long.yml", "FALSE"),
    # objects: vacuous TRUE guard was counting unreachable assertions
    ("canary", "sv-benchmarks/objects/objects01.yml", "TRUE"),
    # forDigit: radix bounds check was missing
    ("canary", "sv-benchmarks/autostub/Character_public_static_char_java_lang_Character_forDigit_int_int.yml", "FALSE"),

    # ── Float/Double bit-level operations ───────────────────────────────
    ("float", "sv-benchmarks/autostub/Float_public_static_native_int_java_lang_Float_floatToRawIntBits_float.yml", "FALSE"),
    ("float", "sv-benchmarks/autostub/Float_public_static_boolean_java_lang_Float_isNaN_float.yml", "FALSE"),
    ("float", "sv-benchmarks/autostub/Float_public_static_int_java_lang_Float_compare_float_float.yml", "FALSE"),
    ("float", "sv-benchmarks/autostub/Double_public_static_native_long_java_lang_Double_doubleToRawLongBits_double.yml", "FALSE"),
    ("float", "sv-benchmarks/autostub/Double_public_static_boolean_java_lang_Double_isNaN_double.yml", "FALSE"),
    ("float", "sv-benchmarks/autostub/Double_public_static_int_java_lang_Double_compare_double_double.yml", "FALSE"),

    # Character toUpperCase/toTitleCase: were wrong TRUE (ASCII-only model + ASCII constraint)
    ("canary", "sv-benchmarks/autostub/Character_public_static_int_java_lang_Character_toUpperCase_int.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/Character_public_static_int_java_lang_Character_toTitleCase_int.yml", "FALSE"),

    # CEGAR wrong TRUE: predicate abstraction unsound with havoced heap ops.
    # These were wrongly TRUE when CEGAR's body_uses_havoced_ops guard was removed.
    ("canary", "sv-benchmarks/algorithms/BellmanFord-MemUnsat01.yml", "FALSE"),
    ("canary", "sv-benchmarks/algorithms/InsertionSort-MemUnsat01.yml", "FALSE"),

    # ── Aliasing / strong updates ────────────────────────────────────────
    ("aliasing", "sv-benchmarks/securibench/Aliasing3.yml", "TRUE"),

    # ── Inheritance / field resolution ─────────────────────────────────
    # Inheritance1: constructor chain writes fields with parent class key,
    # reads with subclass key. Tests field_key_resolved.
    ("inheritance", "sv-benchmarks/jbmc-regression/Inheritance1.yml", "TRUE"),
]

import yaml

def resolve_inputs(yml_path):
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None
    task_dir = os.path.dirname(yml_path)
    return [os.path.join(task_dir, inp) for inp in data["input_files"]]

def run_one(yml_path):
    inputs = resolve_inputs(yml_path)
    if inputs is None:
        return "SKIP"
    try:
        result = subprocess.run(
            [ROAST] + inputs,
            capture_output=True, text=True, timeout=TIMEOUT
        )
        verdict = result.stdout.strip().split("\n")[-1] if result.stdout.strip() else "ERROR"
        return verdict
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    except Exception:
        return "ERROR"

def main():
    if not os.path.exists(ROAST):
        print(f"Binary not found: {ROAST}")
        print("Build first: cargo build --release")
        sys.exit(1)

    # Filter to existing benchmarks
    valid_tests = []
    for cat, yml, expected in TESTS:
        if os.path.exists(yml):
            valid_tests.append((cat, yml, expected))
        else:
            print(f"  SKIP {yml} (not found)")

    print(f"Running {len(valid_tests)} smoke tests...")
    start = time.time()

    passed = 0
    failed = 0
    unknown = 0
    failures = []

    for cat, yml, expected in valid_tests:
        name = os.path.basename(yml).replace(".yml", "")
        verdict = run_one(yml)

        if verdict == expected:
            passed += 1
            status = "ok"
        elif verdict in ("UNKNOWN", "TIMEOUT", "ERROR", "SKIP"):
            unknown += 1
            status = "??"
        else:
            # Wrong answer
            failed += 1
            status = "FAIL"
            failures.append((cat, name, expected, verdict))

        sym = {"ok": "+", "??": ".", "FAIL": "X"}[status]
        print(f"  {sym} [{cat:15s}] {name}: {verdict} (expected {expected})")

    elapsed = time.time() - start
    print()
    print(f"Results ({elapsed:.0f}s): {passed} correct, {unknown} unknown, {failed} WRONG")

    if failures:
        print()
        print("REGRESSIONS DETECTED:")
        for cat, name, expected, got in failures:
            penalty = -16 if got == "TRUE" else -32
            print(f"  [{cat}] {name}: said {got}, expected {expected} (penalty: {penalty})")
        print()
        print("DO NOT deploy this build. Fix the regressions first.")
        sys.exit(1)
    else:
        print("No regressions. Safe to run full scoring.")
        sys.exit(0)

if __name__ == "__main__":
    main()
