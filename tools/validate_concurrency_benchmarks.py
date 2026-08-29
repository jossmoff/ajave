#!/usr/bin/env python3
"""Sanity-check the concurrency benchmarks against a real JVM.

This is deliberately *weaker* than `validate_own_benchmarks.py`, and the reason
matters. For a deterministic program, running it establishes ground truth: it
either throws or it does not. For a concurrent one, execution is evidence in
only one direction:

    expected TRUE   a failing run REFUTES it (the program is not safe)
                    a thousand passing runs prove NOTHING (we may simply never
                    have hit the bad interleaving)

    expected FALSE  a failing run CONFIRMS it
                    passing runs prove NOTHING (the racy schedule is usually
                    not the one the JVM picks — an unsynchronised counter
                    prints the right answer nearly every time)

So this script can only ever find *contradictions*. Ground truth lives in the
`justification` comment generated into each `Main.java`, established by
construction from the JLS.

Treating "it passed 1000 times" as confirmation is exactly the reasoning that
makes concurrency bugs ship, and it is worth the script refusing to do it.

Exit code 0 = no contradictions found (which is not the same as "verified").

Usage: python3 tools/validate_concurrency_benchmarks.py [--runs 300]
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

ROOT = "ajave-benchmarks/concurrency"
COMMON = "ajave-benchmarks/common"


def load(yml):
    with open(yml) as f:
        data = yaml.safe_load(f)
    v = {}
    for p in (data.get("properties") or []):
        pf = p.get("property_file", "")
        if "valid-assert" in pf:
            v["assert"] = p.get("expected_verdict")
        elif "no-runtime-exception" in pf:
            v["nre"] = p.get("expected_verdict")
    return v


def run_many(src_dir, runs, timeout=10):
    """Execute repeatedly; return a Counter of observed outcomes."""
    with tempfile.TemporaryDirectory() as out:
        srcs = glob.glob(os.path.join(src_dir, "*.java"))
        srcs += glob.glob(os.path.join(COMMON, "**", "*.java"), recursive=True)
        r = subprocess.run(["javac", "-d", out] + srcs, capture_output=True, text=True)
        if r.returncode != 0:
            return None, r.stderr[:800]

        seen = Counter()
        for _ in range(runs):
            try:
                p = subprocess.run(["java", "-ea", "-cp", out, "Main"],
                                   capture_output=True, text=True, timeout=timeout)
            except subprocess.TimeoutExpired:
                # A hang is the expected outcome for a deadlock benchmark.
                seen["HANG"] += 1
                continue
            # Parse stderr regardless of exit status. An exception that
            # escapes a *non-main* thread is printed by the default handler and
            # kills only that thread — the JVM still exits 0. Keying on the
            # exit code alone therefore reports a provably-throwing program as
            # clean, which is how `ThreadBodyThrows` first showed up as OKx40.
            m = re.search(
                r"Exception in thread \"([^\"]+)\" ([\w.$]*(?:Exception|Error))",
                p.stderr,
            )
            if m:
                # Record which thread, since main vs. worker changes whether
                # this counts as a property violation at all.
                thread, exc = m.group(1), m.group(2)
                seen[f"{exc}@{'main' if thread == 'main' else 'worker'}"] += 1
            elif p.returncode == 0:
                seen["OK"] += 1
            else:
                m2 = re.search(r"([\w.$]*(?:Exception|Error))", p.stderr)
                seen[m2.group(1) if m2 else "FAILED"] += 1
        return seen, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=300)
    args = ap.parse_args()

    ymls = sorted(glob.glob(os.path.join(ROOT, "*.yml")))
    if not ymls:
        print(f"no benchmarks under {ROOT}/")
        sys.exit(2)

    print(f"Running {len(ymls)} concurrency benchmarks x{args.runs} on a real JVM.")
    print("Looking for CONTRADICTIONS only — execution cannot confirm a")
    print("concurrency verdict, only refute one.\n")

    problems = []
    for yml in ymls:
        name = os.path.splitext(os.path.basename(yml))[0]
        verdicts = load(yml)
        seen, err = run_many(os.path.join(ROOT, name), args.runs)
        if err:
            print(f"  COMPILE-FAIL {name}\n{err}")
            problems.append((name, "does not compile"))
            continue

        base = lambda k: k.split("@")[0]
        assertion = sum(n for k, n in seen.items() if base(k).endswith("AssertionError"))
        runtime = sum(n for k, n in seen.items()
                      if base(k).endswith(("Exception", "Error"))
                      and not base(k).endswith("AssertionError"))
        summary = ", ".join(f"{k}x{v}" for k, v in seen.most_common(3))

        flags = []
        if verdicts.get("assert") is True and assertion:
            flags.append(f"claims valid-assert TRUE but {assertion} run(s) threw AssertionError")
        if verdicts.get("nre") is True and runtime:
            offenders = ", ".join(k for k in seen
                                  if k.endswith(("Exception", "Error"))
                                  and not k.endswith("AssertionError"))
            flags.append(f"claims no-runtime-exception TRUE but {runtime} run(s) threw {offenders}")

        if flags:
            for f in flags:
                print(f"  CONTRADICTION {name}: {f}")
                problems.append((name, f))
        else:
            witnessed = []
            if verdicts.get("assert") is False and assertion:
                witnessed.append("saw the assertion fail")
            if verdicts.get("nre") is False and runtime:
                witnessed.append("saw the exception")
            note = f"  [{'; '.join(witnessed)}]" if witnessed else ""
            print(f"  ok  {name:<26s} {summary}{note}")

    print()
    if problems:
        print(f"{len(problems)} contradiction(s) — the benchmark's expected verdict is wrong:")
        for n, why in problems:
            print(f"  {n}: {why}")
        sys.exit(1)

    print("No contradictions. Note this does NOT verify the expected verdicts —")
    print("ground truth is the justification comment in each Main.java, argued")
    print("from the JLS. A racy benchmark that never failed here is expected:")
    print("the JVM rarely picks the bad interleaving on its own.")
    sys.exit(0)


if __name__ == "__main__":
    main()
