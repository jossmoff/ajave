#!/usr/bin/env python3
"""Why is each unproven task unproven — and which of those causes is *effort*?

The question this answers is the one that has to be settled before committing to
a scheduler: how many points are actually reachable by spending time better,
as against how many need a model or a theory we do not have.

A task can fail to score for reasons that respond to completely different work:

  budget        The BMC truncated its own exploration — depth, forks, block
                visits, unrolling. More effort decides these, so a scheduler
                that reallocates time can convert them. THIS is the scheduling
                ceiling.
  model         Something was left unmodelled: an unresolved call, a havoc that
                might throw. No amount of time helps; only a model of the
                callee does. These are the JDK-lifting bucket.
  theory        The path was tainted by an operation the encoding cannot
                express. Needs a different theory, not a bigger budget.
  timeout       The whole task hit the wall clock. Partly schedulable — an
                anytime engine that reports what it established beats one that
                is killed mid-thought — and partly not.
  no-candidate  Nothing published anything at all.

Reads `smt-bmc: BLOCKER <reason> for <obligation>` at debug, which the engine
already emits, plus the final verdict.

Usage:
    python3 tools/blocker_census.py --set sv-comp --property valid-assert --limit 120
    python3 tools/blocker_census.py --set smoke
"""

import argparse
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402

BLOCKER_RE = re.compile(r"BLOCKER (\S+) for")

# Which kind of work each blocker responds to. The whole point of the tool is
# this mapping, so it is stated once, here, rather than inferred at the call
# site.
KIND = {
    "all_paths_complete": "budget",
    "all_calls_resolved": "model",
    "has_depth_limited_havoc": "model",
    "has_potentially_throwing_havoc": "model",
    "has_unresolved_in_try": "model",
    "has_tainted_paths": "theory",
    # An obligation whose check could not be trusted: the path was tainted, or
    # the solver returned Unknown. A different encoding decides these, not a
    # bigger budget.
    "skipped_obligation": "theory",
    # A violation stands against this obligation. On a task that is *not*
    # scoring, that violation was refuted at replay — and certification runs
    # after the engine loop, so nothing ever reconsidered it. This bucket is
    # the one that responds to feeding refutations back.
    "violated": "refuted",
}


def run_one(task, prop, timeout, binary):
    cmd = [binary, "--property", bench.CLI_PROPERTY[prop]] + task["inputs"]
    env = dict(os.environ, RUST_LOG="ajave_engines::smt_bmc=debug")
    try:
        r = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return "TIMEOUT", []
    verdict = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "UNKNOWN"
    return verdict, BLOCKER_RE.findall(r.stderr)


def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--set", default="smoke")
    ap.add_argument("--property", default=None,
                    choices=list(bench.CLI_PROPERTY.keys()))
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--limit", type=int, default=None,
                    help="sample N tasks spread across the set")
    args = ap.parse_args()

    tasks = []
    for task, override in bench.load_set(args.set):
        if args.property:
            props = [args.property] if args.property in task["expected"] else []
        elif override:
            props = [override] if override in task["expected"] else []
        else:
            props = list(task["expected"])
        for prop in props:
            tasks.append((task, prop))
    if args.limit and args.limit < len(tasks):
        step = len(tasks) // args.limit
        tasks = tasks[::step][: args.limit]

    kinds = Counter()
    reasons = Counter()
    examples = defaultdict(list)
    scored = 0

    for i, (task, prop) in enumerate(tasks, 1):
        verdict, blockers = run_one(task, prop, args.timeout, bench.BINARY)
        expected = task["expected"].get(prop)
        # `expected` is a bool, not a string. Getting this wrong made the
        # first run of this tool report "0 scored out of 150", which is how it
        # was caught.
        correct = (verdict == "TRUE" and expected is True) or \
                  (verdict == "FALSE" and expected is False)
        name = os.path.basename(task["yml"]).replace(".yml", "")
        print(f"\r  {i}/{len(tasks)}", end="", file=sys.stderr)
        if correct:
            scored += 1
            continue
        if verdict == "TIMEOUT":
            kinds["timeout"] += 1
            examples["timeout"].append(name)
            continue
        if not blockers:
            kinds["no-candidate"] += 1
            examples["no-candidate"].append(name)
            continue
        # The dominant blocker is the one that appears most; a task needs every
        # obligation decided, so the commonest refusal is what to attack first.
        top = Counter(blockers).most_common(1)[0][0]
        reasons[top] += 1
        k = KIND.get(top, "other")
        kinds[k] += 1
        examples[k].append(name)
    print("\r" + " " * 30 + "\r", end="", file=sys.stderr)

    total = len(tasks)
    unproven = total - scored
    print(f"\n{total} runs — {scored} scored, {unproven} not\n")
    print(f"{'why not':<16} {'tasks':>6} {'% of unproven':>14}  responds to")
    print("-" * 72)
    RESPONDS = {
        "budget": "scheduling / more effort  <-- the scheduler's ceiling",
        "model":  "modelling the callee (lift java.base)",
        "theory": "a different encoding",
        "refuted": "feeding refutations back into the loop",
        "timeout": "anytime engines, partly",
        "no-candidate": "unknown — nothing published at all",
        "other": "unclassified blocker",
    }
    for k, n in kinds.most_common():
        pct = 100 * n / unproven if unproven else 0
        print(f"{k:<16} {n:>6} {pct:>13.1f}%  {RESPONDS.get(k, '')}")

    if reasons:
        print(f"\n{'dominant blocker':<34} {'tasks':>6}")
        print("-" * 42)
        for r, n in reasons.most_common():
            print(f"{r:<34} {n:>6}")

    for k in ("budget", "theory"):
        if examples[k]:
            print(f"\n{k} examples: " + ", ".join(examples[k][:8]))

    print("\nThe 'budget' row is what a scheduler can convert. Everything below "
          "it needs\na model or a theory, and will not move however the time is "
          "spent.")


if __name__ == "__main__":
    main()
