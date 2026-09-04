#!/usr/bin/env python3
"""Which unproven tasks are blocked on a fact another engine already has?

The portfolio is eleven engines that mostly do not talk. When a task fails,
*two* engines usually failed on it for different reasons — and sometimes the
reason one of them failed is a fact the other one had. Those are the tasks that
cannot be decided in isolation and can be decided by a pair.

This finds them, by reading what each engine says when it declines. Every
message below is already emitted; nothing here changes behaviour.

    k-induction: step case inconclusive     the inductive hypothesis is too weak
    interval-ai: published N interval hints ... and bounds are what strengthens it

    imc: no bounded obligations to work on  nothing published `Bounded { k }`
    smt-bmc: (explored the body)            ... and it was the one that could

    chc: skipping — heap/array operations   declines the whole body
    smt-bmc: all_paths_complete             ... having already covered part of it

Each pairing is named for the technique it corresponds to, so the output points
at a body of work rather than a hunch:

  ai->kind    k-induction with auxiliary invariants. The step case fails because
              the hypothesis is too weak; interval bounds strengthen it. This is
              the standard combination (Beyer et al., "Boosting k-Induction with
              Continuously-Refined Invariants", CAV 2015) and we have both
              halves already, unconnected.
  bmc->kind   `Bounded { k }` is our one working handoff, and it is published on
              a narrow condition. Tasks where a prover had nothing to work on
              are tasks where widening it would give it something.
  bmc->chc    Conditional model checking. CHC declines a whole body for heap or
              float operations that the BMC has already explored; the residual
              is smaller than the body.
  ai->chc     Interval bounds as candidate invariants — the most valuable hint a
              Horn solver can be given, and CHC currently cannot see them.

Usage:
    python3 tools/pairing_census.py --set sv-comp --property valid-assert --limit 120
"""

import argparse
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402

# What each engine says, and what it means for pairing.
SIGNALS = {
    "kind_step_weak": r"k-induction: step case (?:inconclusive|for .* not inductive)",
    "kind_nothing": r"k-induction: nothing to work on",
    "kind_declined": r"k-induction: encoding of .* is incomplete, declining",
    "imc_nothing": r"imc: no bounded obligations to work on",
    "imc_inconclusive": r"imc: (?:inconclusive|max iterations reached)",
    "chc_heap": r"chc: skipping — reachable methods use heap/array",
    "chc_float": r"chc: skipping — reachable methods use float/double",
    "chc_calls": r"chc: skipping — reachable methods have unresolved library",
    "chc_nothing": r"chc: nothing open",
    "ai_hints": r"interval-ai: published (\d+) interval hints",
    "bmc_incomplete": r"BLOCKER all_paths_complete",
    "bmc_skipped": r"BLOCKER skipped_obligation",
    "bmc_violated": r"BLOCKER violated",
}


def signals_of(stderr):
    out = {}
    for name, pat in SIGNALS.items():
        m = re.search(pat, stderr)
        if m:
            out[name] = int(m.group(1)) if m.groups() else True
    return out


def pairings(sig, shape):
    """Which pair could decide this task, given who said what."""
    out = []
    # The step case failed for want of a stronger hypothesis, and the interval
    # engine computed bounds nobody handed it.
    if sig.get("kind_step_weak") and sig.get("ai_hints"):
        out.append("ai->kind")
    # A prover had nothing to chew on because the one channel that works was
    # not fed.
    if (sig.get("imc_nothing") or sig.get("kind_nothing")) and shape.get("loops"):
        out.append("bmc->kind")
    # CHC refused a whole body the BMC had already partly covered.
    if (sig.get("chc_heap") or sig.get("chc_float")) and sig.get("bmc_incomplete"):
        out.append("bmc->chc")
    # Bounds exist and the Horn solver cannot see them.
    if sig.get("ai_hints") and not (sig.get("chc_nothing") or sig.get("chc_calls")):
        out.append("ai->chc")
    return out


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--set", default="sv-comp")
    ap.add_argument("--property", default=None, choices=list(bench.CLI_PROPERTY.keys()))
    ap.add_argument("--timeout", type=int, default=90)
    ap.add_argument("--limit", type=int, default=120)
    args = ap.parse_args()

    tasks = []
    for task, override in bench.load_set(args.set):
        props = ([args.property] if args.property else
                 ([override] if override else list(task["expected"])))
        for p in props:
            if p in task["expected"]:
                tasks.append((task, p))
    if args.limit and args.limit < len(tasks):
        tasks = tasks[:: len(tasks) // args.limit][: args.limit]

    counts = Counter()
    examples = defaultdict(list)
    scored = unproven = 0

    env_base = dict(os.environ, RUST_LOG="info,ajave_engines=debug")
    for i, (task, prop) in enumerate(tasks, 1):
        cmd = [bench.BINARY, "--property", bench.CLI_PROPERTY[prop]] + task["inputs"]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True,
                               timeout=args.timeout, env=env_base)
        except subprocess.TimeoutExpired:
            continue
        verdict = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "UNKNOWN"
        exp = task["expected"][prop]
        print(f"\r  {i}/{len(tasks)}", end="", file=sys.stderr)
        if (verdict == "TRUE") == exp and verdict != "UNKNOWN":
            scored += 1
            continue
        unproven += 1
        sig = signals_of(r.stderr)
        shape = {}
        m = re.search(r"PROGRAM_SHAPE (.*)", r.stderr)
        if m:
            for pair in m.group(1).split():
                if "=" in pair:
                    k, v = pair.split("=", 1)
                    shape[k] = v == "true"
        name = os.path.basename(task["yml"]).replace(".yml", "")
        found = pairings(sig, shape)
        if not found:
            counts["(no pairing suggested)"] += 1
            continue
        for p in found:
            counts[p] += 1
            examples[p].append((name, exp))
    print("\r" + " " * 30 + "\r", end="", file=sys.stderr)

    print(f"\n{scored + unproven} runs — {scored} scored, {unproven} not\n")
    print(f"{'candidate pair':<22} {'tasks':>6}  {'expected TRUE':>13}  technique")
    print("-" * 84)
    TECH = {
        "ai->kind": "k-induction with auxiliary invariants",
        "bmc->kind": "widen the Bounded{k} channel",
        "bmc->chc": "conditional model checking (residual)",
        "ai->chc": "interval bounds as candidate invariants",
        "(no pairing suggested)": "needs a model or a value, not a pair",
    }
    for p, n in counts.most_common():
        trues = sum(1 for _, e in examples[p] if e)
        print(f"{p:<22} {n:>6}  {trues:>13}  {TECH.get(p, '')}")

    for p in ("ai->kind", "bmc->kind", "bmc->chc", "ai->chc"):
        if examples[p]:
            print(f"\n{p}:")
            for name, e in examples[p][:6]:
                print(f"    {name:<58} expected {'TRUE' if e else 'FALSE'}")

    print("\nA pair only pays where the task is expected TRUE: a proof is what a\n"
          "second engine can contribute. Expected-FALSE tasks in these rows need a\n"
          "replayable witness, which is a model problem, not a cooperation one.")


if __name__ == "__main__":
    main()
