#!/usr/bin/env python3
"""
Fast pre-scoring gate: run roast against a curated canary set and fail on any
regression.

CLAUDE.md has mandated this script for a while; it did not exist, so the rule
that "every wrong-answer fix MUST add a canary test" had nowhere to land. This
is that script.

Relationship to the other two harnesses:

  * `cargo test -p roast` runs the full corpus (114 tasks) as Rust integration
    tests. Thorough, but it needs a toolchain and takes minutes.
  * `scripts/run-corpus.py` diffs every task against the snapshot in
    `tasks/verdicts.txt` and can rewrite it. That is the bookkeeping tool.
  * This is the gate. A hand-picked list of tasks with *known-correct*
    expected verdicts, kept small enough to run before every scoring run.

Exit code 0 = safe to score. 1 = a regression.

Usage:
    python3 tools/smoke_test.py [--timeout SECONDS] [--verbose]
"""

import argparse
import os
import subprocess
import sys

# ---------------------------------------------------------------------------
# The canary set.
#
# Format: ("category", "path/to/task.yml", "EXPECTED_VERDICT")
#
# The expected verdict is the *known-correct* answer, not merely what roast
# happens to produce. A task roast currently answers UNKNOWN does not belong
# here — put it in tasks/verdicts.txt and let scripts/run-corpus.py track it.
#
# Keep this under 80 entries so the whole run stays inside a few minutes.
# ---------------------------------------------------------------------------
TESTS = [
    # -- exceptions -------------------------------------------------------
    ("exceptions", "tasks/ArithmeticException1/ArithmeticException1.yml", "TRUE"),
    ("exceptions", "tasks/ArithmeticException2/ArithmeticException2.yml", "FALSE"),
    ("exceptions", "tasks/ArithmeticException3/ArithmeticException3.yml", "TRUE"),
    # -- integer arithmetic ----------------------------------------------
    ("arith", "tasks/IntegerArithmetic1/IntegerArithmetic1.yml", "TRUE"),
    ("arith", "tasks/IntegerArithmetic2/IntegerArithmetic2.yml", "FALSE"),
    # -- loops -------------------------------------------------------------
    ("loops", "tasks/BoundedLoop2/BoundedLoop2.yml", "FALSE"),
    # -- branching ---------------------------------------------------------
    ("branch", "tasks/NestedBranch1/NestedBranch1.yml", "TRUE"),
    ("branch", "tasks/stage02_branch/stage02_branch.yml", "TRUE"),
    # -- canaries: the staged end-to-end path ------------------------------
    ("canary", "tasks/stage00_const/stage00_const.yml", "FALSE"),
    ("canary", "tasks/stage01_nondet/stage01_nondet.yml", "TRUE"),
]

# Tasks whose correct verdict roast cannot currently produce. Reported at the
# end of a run, but not failures -- a gate that is permanently red teaches
# everyone to ignore it. Move an entry up into TESTS the moment it starts
# passing, so it can never silently regress again.
KNOWN_GAPS = [
    (
        "tasks/ModuloZero1/ModuloZero1.yml",
        "FALSE",
        "div-by-zero reaches the check but the obligation is not seeded: the "
        "orchestrator runs assertion-only, so the DivByZero obligation both "
        "engines flag is filtered out before it can decide the verdict",
    ),
    (
        "tasks/stage04_divzero/stage04_divzero.yml",
        "FALSE",
        "same as ModuloZero1 -- concrete and smt-bmc both find the violation "
        "(witness=[0]) and the blackboard drops it as non-seeded",
    ),
]

ROAST_CANDIDATES = ["./target/release/roast", "./target/debug/roast"]


def find_roast():
    override = os.environ.get("ROAST")
    if override:
        return override
    for candidate in ROAST_CANDIDATES:
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


def resolve_inputs(yml_path):
    """The task's input_files, resolved relative to the task directory."""
    try:
        import yaml
    except ImportError:
        print("PyYAML is required: pip install pyyaml", file=sys.stderr)
        sys.exit(2)

    task_dir = os.path.dirname(yml_path)
    with open(yml_path) as f:
        spec = yaml.safe_load(f)
    paths = []
    for rel in spec.get("input_files", []):
        abs_p = os.path.normpath(os.path.join(task_dir, rel))
        if os.path.exists(abs_p):
            paths.append(abs_p)
    return paths


def run_roast(roast, inputs, timeout):
    try:
        r = subprocess.run(
            [roast] + inputs,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    lines = [l.strip() for l in r.stdout.strip().splitlines() if l.strip()]
    return lines[-1] if lines else "(no output)"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--timeout",
        type=int,
        default=30,
        help="per-task timeout in seconds (default: 30)",
    )
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

    roast = find_roast()
    if not roast:
        print("roast binary not found; run 'cargo build --release' first", file=sys.stderr)
        return 2

    failures = []
    skipped = []
    passed = 0

    for category, yml, expected in TESTS:
        if not os.path.exists(yml):
            skipped.append((category, yml, "task file not present"))
            continue
        inputs = resolve_inputs(yml)
        if not inputs:
            skipped.append((category, yml, "no input files resolved"))
            continue

        verdict = run_roast(roast, inputs, args.timeout)
        if verdict == expected:
            passed += 1
            if args.verbose:
                print(f"  ok       [{category}] {yml} -> {verdict}")
        else:
            failures.append((category, yml, expected, verdict))
            print(f"  FAIL     [{category}] {yml}: expected {expected}, got {verdict}")

    print()
    print(f"smoke test: {passed} passed, {len(failures)} failed, {len(skipped)} skipped")

    if KNOWN_GAPS and args.verbose:
        print("\nknown gaps (not failures):")
        for yml, expected, why in KNOWN_GAPS:
            print(f"  {yml} — should be {expected}: {why}")

    if skipped:
        print("\nskipped:")
        for category, yml, why in skipped:
            print(f"  [{category}] {yml} — {why}")

    if failures:
        print("\nRegressions detected. Do not score until these are resolved.")
        print("A wrong verdict here is a soundness bug; an UNKNOWN where a")
        print("verdict is expected is a lost result. Both block scoring.")
        return 1

    if skipped and passed == 0:
        print("\nNothing actually ran. Treating that as a failure rather than a pass.")
        return 1

    print("\nNo regressions. Safe to score.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
