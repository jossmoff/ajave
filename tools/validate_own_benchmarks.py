#!/usr/bin/env python3
"""Check benchmarks/ajave expected verdicts against a real JVM.

The suite is only useful if its ground truth is actually true. A hand-written
`expected_verdict` that is wrong is worse than no benchmark at all: it trains
the tool toward an incorrect answer and it does so silently.

So for every benchmark we compile and execute `Main` with assertions enabled
and compare what the JVM does against what the .yml claims:

  valid-assert          FALSE  <=>  an AssertionError escapes main
  no-runtime-exception  FALSE  <=>  a RuntimeException escapes main

Nondeterministic benchmarks are a special case. `Verifier.nondet*` returns
random values at runtime, so a single execution cannot confirm a FALSE verdict
(the run may simply miss the triggering input) and cannot confirm a TRUE verdict
either (one passing run proves nothing). We therefore:

  - fully verify deterministic benchmarks, and
  - for nondeterministic ones, check only for *contradictions*: a run that
    throws where the task claims the property holds is a real defect, since no
    input may violate a TRUE property.

Exit code 0 = no contradictions found.

Usage: python3 tools/validate_own_benchmarks.py [--dir benchmarks/ajave] [--runs 200]
"""

import argparse
import glob
import os
import re
import subprocess
import sys
import tempfile
import yaml
from collections import Counter

NONDET = re.compile(r"Verifier\s*\.\s*nondet")

# A program whose only nondeterminism is the *scheduler* has no
# `Verifier.nondet` call, so the input-nondeterminism test above calls it
# deterministic and runs it once. That is wrong in the direction that matters:
# a data race is FALSE because the JMM *permits* a violating execution, not
# because a JVM will show you one, and eight racy benchmarks were reported as
# defective on the strength of a single run that happened to interleave
# benignly.
#
# Anything that can start a thread is therefore treated as nondeterministic:
# it goes down the contradiction-only path, where an unobserved violation
# proves nothing but an observed one against an expected TRUE still fails.
CONCURRENT = re.compile(
    r"\bnew\s+Thread\b|\.start\s*\(\)|ExecutorService|CompletableFuture"
    r"|ForkJoinPool|\bThread\s*\.\s*ofVirtual\b"
)


def load_tasks(root):
    tasks = []
    for yml in sorted(glob.glob(os.path.join(root, "*", "*.yml"))):
        with open(yml) as f:
            data = yaml.safe_load(f)
        verdicts = {}
        for p in data.get("properties", []):
            pf = p.get("property_file", "")
            if "valid-assert" in pf:
                verdicts["assert"] = p.get("expected_verdict")
            elif "no-runtime-exception" in pf:
                verdicts["nre"] = p.get("expected_verdict")
        name = os.path.splitext(os.path.basename(yml))[0]
        src_dir = os.path.join(os.path.dirname(yml), name)
        tasks.append((yml, name, src_dir, verdicts))
    return tasks


def compile_and_run(src_dir, common_dir, runs):
    """Return (outcomes, compile_error). outcomes is a Counter of exception
    class names, with 'OK' for a clean exit."""
    with tempfile.TemporaryDirectory() as out:
        srcs = glob.glob(os.path.join(src_dir, "*.java"))
        srcs += glob.glob(os.path.join(common_dir, "**", "*.java"), recursive=True)
        r = subprocess.run(["javac", "-d", out] + srcs,
                           capture_output=True, text=True)
        if r.returncode != 0:
            return None, r.stderr[:1500]

        outcomes = Counter()
        for _ in range(runs):
            try:
                p = subprocess.run(["java", "-ea", "-cp", out, "Main"],
                                   capture_output=True, text=True, timeout=30)
            except subprocess.TimeoutExpired:
                # Not a harness failure. A deadlock benchmark is *supposed* to
                # hang, and so is any program whose threads never join, so an
                # overrun is an observation about the program like any other.
                # This used to propagate and abort the whole validation run.
                outcomes["HANG"] += 1
                # A hang is a stable observation -- a deadlock benchmark hangs
                # every time -- so repeating it only burns 30s a go. Two are
                # enough to distinguish "hangs" from a one-off scheduling
                # fluke, and without this cap the concurrency suite alone
                # takes 20 x 30s per deadlock benchmark.
                if outcomes["HANG"] >= 2:
                    break
                continue
            # An exception that kills a *spawned* thread does not change
            # main's exit status, so the returncode alone cannot be the test:
            # `ThreadBodyThrows` exits 0 while printing a stack trace for
            # Thread-0. Look at stderr regardless of how the process exited.
            m = re.search(r"Exception in thread \"[^\"]*\" ([\w.$]+)", p.stderr)
            if p.returncode == 0 and not m:
                outcomes["OK"] += 1
            else:
                # Verifier.assume halts via Runtime.halt(1) with no exception:
                # that execution simply did not satisfy the assumption.
                if m:
                    outcomes[m.group(1)] += 1
                else:
                    outcomes["ASSUME_HALT"] += 1
        return outcomes, None


def classify(outcomes):
    """What did the JVM actually demonstrate?"""
    assertion = sum(n for k, n in outcomes.items() if k.endswith("AssertionError"))
    runtime = sum(
        n for k, n in outcomes.items()
        if k.startswith("java.") and not k.endswith("AssertionError")
    )
    return assertion, runtime


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default="benchmarks/ajave")
    ap.add_argument("--runs", type=int, default=200,
                    help="executions per nondeterministic benchmark")
    args = ap.parse_args()

    common = os.path.join(args.dir, "common")
    tasks = load_tasks(args.dir)
    if not tasks:
        print(f"no tasks found under {args.dir}/")
        sys.exit(2)

    print(f"Validating {len(tasks)} benchmarks against a real JVM\n")

    problems = []
    det_checked = 0
    nondet_checked = 0

    for yml, name, src_dir, verdicts in tasks:
        srcs = glob.glob(os.path.join(src_dir, "*.java"))
        text = "".join(open(s).read() for s in srcs)
        nondet = bool(NONDET.search(text)) or bool(CONCURRENT.search(text))
        runs = args.runs if nondet else 1

        outcomes, err = compile_and_run(src_dir, common, runs)
        if err is not None:
            print(f"  COMPILE-FAIL {name}\n{err}")
            problems.append((name, "does not compile"))
            continue

        assertion, runtime = classify(outcomes)
        exp_a = verdicts.get("assert")
        exp_n = verdicts.get("nre")

        if nondet:
            nondet_checked += 1
            # Only contradictions are conclusive here.
            if exp_a is True and assertion > 0:
                problems.append((name, "claims valid-assert TRUE but an execution "
                                       "threw AssertionError"))
            if exp_n is True and runtime > 0:
                offenders = ", ".join(
                    k for k in outcomes
                    if k.startswith("java.") and not k.endswith("AssertionError"))
                problems.append((name, f"claims no-runtime-exception TRUE but an "
                                       f"execution threw {offenders}"))
        else:
            det_checked += 1
            if exp_a is not None:
                observed_false = assertion > 0
                if observed_false != (exp_a is False):
                    problems.append((name,
                        f"valid-assert expects {exp_a} but JVM "
                        f"{'threw' if observed_false else 'did not throw'} AssertionError"))
            if exp_n is not None:
                observed_false = runtime > 0
                if observed_false != (exp_n is False):
                    got = ", ".join(k for k in outcomes if k != "OK") or "nothing"
                    problems.append((name,
                        f"no-runtime-exception expects {exp_n} but JVM threw {got}"))

    print(f"deterministic fully verified: {det_checked}")
    print(f"nondeterministic checked for contradictions ({args.runs} runs each): "
          f"{nondet_checked}\n")

    if problems:
        print(f"{len(problems)} PROBLEM(S) — the benchmark, not the tool, is wrong:")
        for name, why in problems:
            print(f"  {name}: {why}")
        sys.exit(1)

    print("All expected verdicts consistent with real JVM behaviour.")
    sys.exit(0)


if __name__ == "__main__":
    main()
