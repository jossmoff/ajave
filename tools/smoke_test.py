#!/usr/bin/env python3
"""Fast smoke test for ajave engine changes.

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
    python3 tools/smoke_test.py [--binary ./target/release/ajave]

Exit code 0 = all pass, 1 = regressions detected.
"""

import os
import subprocess
from concurrent.futures import ProcessPoolExecutor
import sys
import time

ROAST = sys.argv[2] if len(sys.argv) > 2 and sys.argv[1] == "--binary" else "./target/release/ajave"
TIMEOUT = 60
# Workers for the parallel run. Kept below core count on purpose — see the
# comment in main(). Override with SMOKE_JOBS.
JOBS = int(os.environ.get("SMOKE_JOBS", "6"))

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
    # StringValueOf09: was wrong TRUE (valueOf(double) used signed_bv_to_str → integer string)
    ("canary", "sv-benchmarks/jbmc-regression/StringValueOf09.yml", "FALSE"),
    # Inter13, Refl3: fixed to UNKNOWN by all_calls_resolved tightening.
    ("canary", "sv-benchmarks/securibench/Inter13.yml", "FALSE"),
    ("canary", "sv-benchmarks/securibench/Refl3.yml", "FALSE"),
    ("canary", "sv-benchmarks/juliet-java/CWE369_Divide_by_Zero__float_connect_tcp_divide_01_bad.yml", "FALSE"),

    # Refl4: was wrong TRUE (vacuous TRUE with unreachable assertions)
    ("canary", "sv-benchmarks/securibench/Refl4.yml", "FALSE"),
    # StrongUpdates1: relaxed discharge for assertions when no depth-limited/try havoc
    ("canary", "sv-benchmarks/securibench/StrongUpdates1.yml", "TRUE"),
    # VelocityTracker: was wrong TRUE (Unknown solver result not skipped)
    ("canary", "sv-benchmarks/argv-tasks/VelocityTracker_false.yml", "FALSE"),
    # Base64, StrictLineReader: were wrong FALSE (non-seeded obligations leaked)
    ("canary", "sv-benchmarks/argv-tasks/Base64.yml", "TRUE"),
    ("canary", "sv-benchmarks/argv-tasks/StrictLineReader.yml", "TRUE"),
    # StrongUpdates5: was wrong FALSE (non-seeded NullDeref leaked)
    ("canary", "sv-benchmarks/securibench/StrongUpdates5.yml", "TRUE"),
    # MathHelper_true: was wrong TRUE (NRA discharged over reals, not IEEE 754)
    ("canary", "sv-benchmarks/argv-tasks/MathHelper_true.yml", "FALSE"),
    # BufferedReaderReadLine: was wrong TRUE (tainted-path violation suppressed, k-induction consumed Bounded)
    ("canary", "sv-benchmarks/jbmc-regression/BufferedReaderReadLine.yml", "FALSE"),
    # EquidistantConicProjection_false: was wrong TRUE (tainted paths blocked obligation check, relaxed discharge unsound)
    ("canary", "sv-benchmarks/argv-tasks/EquidistantConicProjection_false.yml", "FALSE"),
    # HttpTransport_false: was wrong TRUE (CHC discharged catch-block assertion via unsound LIA encoding)
    ("canary", "sv-benchmarks/argv-tasks/HttpTransport_false.yml", "FALSE"),
    # UnsatAddition02: was wrong TRUE (BMC tainted-path relaxed discharge on havoced recursive calls)
    ("canary", "sv-benchmarks/jayhorn-recursive/UnsatAddition02.yml", "FALSE"),

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
    # Character Unicode table methods: getType, isMirrored, getNumericValue, getDirectionality
    ("canary", "sv-benchmarks/autostub/Character_public_static_int_java_lang_Character_getType_char.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/Character_public_static_boolean_java_lang_Character_isMirrored_char.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/Character_public_static_int_java_lang_Character_getNumericValue_char.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/Character_public_static_byte_java_lang_Character_getDirectionality_char.yml", "FALSE"),

    # CEGAR wrong TRUE: predicate abstraction unsound with havoced heap ops.
    # These were wrongly TRUE when CEGAR's body_uses_havoced_ops guard was removed.
    # They also guard the exceptional-edge fix in cpa.rs `successors()`: their
    # assertion sits in a `catch` reachable only by an exception propagating out
    # of a call. With no exceptional edge from call positions the check is never
    # visited, and `discharge_obligations` reads a never-visited check as
    # vacuously safe — which produced a wrong TRUE once AI widening made these
    # methods report a complete analysis.
    ("canary", "sv-benchmarks/algorithms/BellmanFord-MemUnsat01.yml", "FALSE"),
    ("canary", "sv-benchmarks/algorithms/InsertionSort-MemUnsat01.yml", "FALSE"),

    # JVM slot reuse across the int/float domains. A local that held an int can
    # be reassigned as a double; if the interval domain writes only the float
    # side and leaves the stale integer interval in place, it narrows a value it
    # no longer describes and wrongly proves the assertion. These three were
    # wrong TRUEs when IntervalCpa became float-aware without clearing the
    # other domain.
    ("canary", "sv-benchmarks/autostub/Byte_public_double_java_lang_Byte_doubleValue.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/Integer_public_double_java_lang_Integer_doubleValue.yml", "FALSE"),
    ("canary", "sv-benchmarks/autostub/Short_public_double_java_lang_Short_doubleValue.yml", "FALSE"),

    # AI array-length tracking + interval bitwise ops. javac lowers
    # `idx >= 0 && idx < len` to a bitwise `&` of two 0/1 values, so both the
    # array-length propagation and `eval_bitwise` are needed to discharge the
    # constant-index ArrayBounds checks in a synthetic enum `$values()`.
    # AI int-loop widening: MinePump's `randomSequenceOfActions` only converges
    # under the widening retry, and the enum bounds checks only under the above.
    ("ai-widen", "sv-benchmarks/MinePump/spec1-5_product14.yml", "TRUE", "no-runtime-exception"),
    ("ai-widen", "sv-benchmarks/MinePump/spec1-5_product1.yml", "TRUE", "no-runtime-exception"),

    # Float taint + JVM slot reuse: bvmul on IEEE 754 doubles is garbage.
    # VarInfo type can be wrong when locals are reused (int→double).
    ("canary", "sv-benchmarks/argv-tasks/AbstractSerializationStreamReader_false.yml", "FALSE"),

    # ── Float constants and comparisons in concrete engine ───────────────
    # fcmpx_dcmpx1: float/double constant comparisons — was wrong FALSE
    ("canary", "sv-benchmarks/jbmc-regression/fcmpx_dcmpx1.yml", "TRUE"),
    # store_load1: JVM slot reuse across int/long/double/float blocks
    ("canary", "sv-benchmarks/jbmc-regression/store_load1.yml", "TRUE"),

    # ── CHC inter-procedural recursive proofs ──────────────────────────
    # These are proved by the CHC engine using LIA inter-proc encoding.
    ("chc-recursive", "sv-benchmarks/jayhorn-recursive/SatAckermann01.yml", "TRUE"),
    ("chc-recursive", "sv-benchmarks/jayhorn-recursive/SatFibonacci01.yml", "TRUE"),
    ("chc-recursive", "sv-benchmarks/jayhorn-recursive/SatMccarthy91.yml", "TRUE"),
    # UnsatAddition02: LIA overflow unsoundness canary — must NOT be TRUE
    ("chc-recursive", "sv-benchmarks/jayhorn-recursive/UnsatEvenOdd01.yml", "FALSE"),

    # ── nondetObject replay ────────────────────────────────────────────
    ("canary", "sv-benchmarks/objects/objects03.yml", "FALSE"),
    # objects14: nondetObject factory inlining (was wrong TRUE via Nondet(Ref))
    ("canary", "sv-benchmarks/objects/objects14.yml", "FALSE"),
    # instanceof8: library class instanceof (was wrong FALSE via I32(0) fallback)
    ("canary", "sv-benchmarks/jbmc-regression/instanceof8.yml", "TRUE"),
    # instanceof3: array covariance — String[] instanceof Object[] (was wrong FALSE, skip fixed)
    ("canary", "sv-benchmarks/jbmc-regression/instanceof3.yml", "TRUE"),

    # ── String constraint solving (Z3 string theory) ───────────────────
    # Securibench: nondetString() → field store → field load → string op → contains → assert false
    # These exercise the fresh_str propagation for unresolved String-returning calls.
    ("string-flow", "sv-benchmarks/securibench/Basic3.yml", "FALSE"),
    ("string-flow", "sv-benchmarks/securibench/Basic11.yml", "FALSE"),
    ("string-flow", "sv-benchmarks/securibench/Basic4.yml", "FALSE"),
    ("string-flow", "sv-benchmarks/securibench/Inter1.yml", "FALSE"),
    ("string-flow", "sv-benchmarks/securibench/Inter5.yml", "FALSE"),

    # ── Aliasing / strong updates ────────────────────────────────────────
    ("aliasing", "sv-benchmarks/securibench/Aliasing3.yml", "TRUE"),

    # ── Inheritance / field resolution ─────────────────────────────────
    # Inheritance1: constructor chain writes fields with parent class key,
    # reads with subclass key. Tests field_key_resolved.
    ("inheritance", "sv-benchmarks/jbmc-regression/Inheritance1.yml", "TRUE"),

    # ── Collections modeling ──────────────────────────────────────────
    # Securibench-Micro collection taint flow through addLast/getLast etc.
    ("collections", "sv-benchmarks/securibench/Collections1.yml", "FALSE"),
    ("collections", "sv-benchmarks/securibench/Collections2.yml", "FALSE"),
    ("collections", "sv-benchmarks/securibench/Collections3.yml", "FALSE"),
    ("collections", "sv-benchmarks/securibench/Collections4.yml", "FALSE"),
    ("collections", "sv-benchmarks/securibench/Collections5.yml", "FALSE"),
    ("collections", "sv-benchmarks/securibench/Collections6.yml", "FALSE"),
    ("collections", "sv-benchmarks/securibench/Collections7.yml", "FALSE"),
    ("collections", "sv-benchmarks/securibench/Collections10.yml", "FALSE"),

    # Float widening: unbounded float loops proved via interval fixpoint
    ("float-widen", "sv-benchmarks/float_unboundedloop/Ramp-and-Hold.yml", "TRUE"),
    ("float-widen", "sv-benchmarks/float_unboundedloop/Bounded-Reset-Linear-Growth.yml", "TRUE"),
    ("float-widen", "sv-benchmarks/float_unboundedloop/Saturating-Integrator.yml", "TRUE"),
    ("float-widen", "sv-benchmarks/float_unboundedloop/Two-Variable_Averaging_Filter.yml", "TRUE"),

    # NRA engine: transcendental math via CVC5
    ("nra", "sv-benchmarks/float-nonlinear-calculation/coral4.yml", "FALSE"),
    ("nra", "sv-benchmarks/float-nonlinear-calculation/coral29.yml", "FALSE"),
    ("nra", "sv-benchmarks/float-nonlinear-calculation/coral48.yml", "FALSE"),
    ("nra", "sv-benchmarks/float-nonlinear-calculation/Optimization1.yml", "FALSE"),

    # NRE soundness canaries: these benchmarks should NOT return TRUE in NRE mode.
    # Expected UNKNOWN (we can't prove safety, and we must not falsely claim it).
    # If any returns TRUE, it's a soundness regression (wrong answer).
    # Ground truth is FALSE for both of these. They were recorded as UNKNOWN when
    # we could not solve them; the replay exception-family fix (2026-08-28) made
    # them solvable and both are now JVM-confirmed. Expected verdicts must be the
    # known-correct answer, never a snapshot of current behaviour.
    ("nre-canary", "sv-benchmarks/jbmc-regression/SubString02.yml", "FALSE", "no-runtime-exception"),
    ("nre-canary", "sv-benchmarks/jbmc-regression/StringBuilderChars05.yml", "UNKNOWN", "no-runtime-exception"),
    ("nre-canary", "sv-benchmarks/jbmc-regression/StringValueOf08.yml", "UNKNOWN", "no-runtime-exception"),
    # NRE soundness: explicit throw of RuntimeException subclass
    ("nre-canary", "sv-benchmarks/argv-tasks/StdRandom_exceptionprone.yml", "FALSE", "no-runtime-exception"),
    # NRE soundness: checked-exception handler must not guard RuntimeException obligations
    ("nre-canary", "sv-benchmarks/jdart-regression/URLDecoder01.yml", "UNKNOWN", "no-runtime-exception"),

    # NRE proof canaries: benchmarks that should be provably TRUE for NRE.
    ("nre-true", "sv-benchmarks/jpf-regression/ExDarko_true.yml", "TRUE", "no-runtime-exception"),
    ("nre-true", "sv-benchmarks/jpf-regression/ExException_true.yml", "TRUE", "no-runtime-exception"),
    # ── k-induction: a bounded check is not a proof (#76) ────────────────
    # `try_step_case` encoded the body once and published the resulting UNSAT
    # as an inductive proof. LoopFailsOnSecondIteration is the shape that
    # separates the two -- it holds on the first iteration and fails on the
    # second -- so a TRUE here means the engine has gone back to reporting one
    # unrolling as an induction. LoopInvariantNeedsInduction is the converse:
    # it needs a real step case, so an UNKNOWN means the capability was lost.
    ("kinduction", "benchmarks/ajave/kinduction/LoopFailsOnSecondIteration.yml", "FALSE"),
    ("kinduction", "benchmarks/ajave/kinduction/LoopInvariantNeedsInduction.yml", "TRUE"),
    ("kinduction", "benchmarks/ajave/kinduction/LoopFreeEntryCallsLoopingHelper.yml", "FALSE"),

    # ── heap: stored values reach later reads ────────────────────────────
    # Every heap read used to be a fresh unconstrained value and every write
    # was dropped, so these two were indistinguishable to the encoder.
    ("heap", "benchmarks/ajave/heap/ArrayInvariantViolated.yml", "FALSE"),

    # ── string models: an unknown argument is not an empty one ───────────
    # `new StringBuffer(x)` was modelled as "" whenever x's content could not
    # be resolved, which proved `contains(...)` false, pruned the branch
    # holding the assertion, and discharged it as unreachable. Basic15 is the
    # corpus task that produced the wrong TRUE; the two reduced programs
    # isolate the String and CharSequence constructors.
    ("strings", "benchmarks/sv-comp/securibench/Basic15.yml", "FALSE"),
    ("strings", "benchmarks/ajave/jvm-strings/StringBufferFromUnknownStringIsNotEmpty.yml", "FALSE"),
    ("strings", "benchmarks/ajave/jvm-strings/StringBufferFromCharSequenceIsNotEmpty.yml", "FALSE"),

]

import yaml

def resolve_inputs(yml_path):
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None
    task_dir = os.path.dirname(yml_path)
    return [os.path.join(task_dir, inp) for inp in data["input_files"]]

def run_one(yml_path, prop=None):
    inputs = resolve_inputs(yml_path)
    if inputs is None:
        return "SKIP"
    try:
        cmd = [ROAST]
        if prop:
            cmd.extend(["--property", prop])
        cmd.extend(inputs)
        result = subprocess.run(
            cmd,
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
    # Each test is (category, yml, expected) or (category, yml, expected, property)
    valid_tests = []
    for entry in TESTS:
        cat, yml, expected = entry[0], entry[1], entry[2]
        prop = entry[3] if len(entry) > 3 else None
        if os.path.exists(yml):
            valid_tests.append((cat, yml, expected, prop))
        else:
            print(f"  SKIP {yml} (not found)")

    jobs = JOBS
    print(f"Running {len(valid_tests)} smoke tests ({jobs} workers)...")
    start = time.time()

    passed = 0
    failed = 0
    unknown = 0
    failures = []

    # Each test is an independent subprocess, so this is embarrassingly
    # parallel; serially it took ~40 minutes on a 10-core machine.
    #
    # Deliberately leaves cores idle rather than saturating them. Parallelism
    # cannot turn a correct verdict into a WRONG one, but it can turn a WRONG
    # one into a TIMEOUT, which this script scores as "??" rather than "FAIL" —
    # so oversubscribing would quietly weaken the very gate this is. Each ajave
    # also spawns a solver child, so the real load is above one process per job.
    with ProcessPoolExecutor(max_workers=jobs) as ex:
        futures = [ex.submit(run_one, yml, prop) for _, yml, _, prop in valid_tests]
        verdicts = []
        for f in futures:
            try:
                verdicts.append(f.result())
            except Exception:
                verdicts.append("ERROR")

    for (cat, yml, expected, prop), verdict in zip(valid_tests, verdicts):
        name = os.path.basename(yml).replace(".yml", "")

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
