#!/usr/bin/env python3
"""Every witness the JVM rejected, clustered by the library method it involves.

A refuted witness is the densest bug report this project produces: the solver
found an assignment, we ran it on a real JVM, and reality disagreed. Somewhere
between the model and the machine there is a divergence, and it comes with a
reproduction attached.

Two were chased by hand on 2026-09-04 and both were *class* bugs, not task bugs:

  * `Math.round` was constrained by `|x - r| <= 0.5`, inclusive at both ends,
    so an exact tie admitted both neighbours. The solver is hunting for the
    assignment that violates the assertion, so it picked the wrong neighbour on
    purpose. Fixed by making the relation `r - 0.5 <= x < r + 0.5`, which is
    unique for every input.

  * Witness strings were delivered to the JVM as their own escape text: Z3
    writes non-ASCII as `\\u{...}` and the parser copied it through, so
    `"DF" + U+1B92E` arrived as thirteen ASCII characters. Every witness string
    with a non-ASCII character had been wrong.

Neither was findable by reading the model, because in both cases the model's
*answer* was reasonable and something else was wrong. The refutation is what
pointed at them.

This sweeps the corpus, keeps every task whose witness was refuted, and buckets
them by the library methods their source calls — so a divergence affecting six
tasks shows up as a cluster of six rather than six unrelated failures.

Usage:
    python3 tools/refutation_sweep.py --set sv-comp --property valid-assert
    python3 tools/refutation_sweep.py --set sv-comp --limit 200
"""

import argparse
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402

CENSUS = re.compile(r"REPLAY_CENSUS result=(\w+).*?method=(\S+)")
# Library calls in the task source. Deliberately syntactic: the point is to
# cluster, and a name that appears in the source is a name the task exercises.
CALL = re.compile(
    r"\b(Math|StrictMath|Integer|Long|Double|Float|Character|String|StringBuilder"
    r"|Boolean|Byte|Short|Arrays|Objects)\s*\.\s*([a-zA-Z][a-zA-Z0-9]*)"
)
# Instance-method calls on a String-typed local, which the above misses.
INSTANCE = re.compile(r"\b\w+\s*\.\s*(indexOf|lastIndexOf|substring|trim|replace"
                      r"|startsWith|endsWith|regionMatches|charAt|concat|split"
                      r"|toUpperCase|toLowerCase|equalsIgnoreCase|compareTo)\s*\(")


def calls_in(task):
    """Library methods the task's own sources mention."""
    found = set()
    for inp in task["inputs"]:
        if not os.path.isdir(inp):
            continue
        for root, _, files in os.walk(inp):
            for f in files:
                if not f.endswith(".java"):
                    continue
                try:
                    text = open(os.path.join(root, f)).read()
                except OSError:
                    continue
                for cls, m in CALL.findall(text):
                    found.add(f"{cls}.{m}")
                for m in INSTANCE.findall(text):
                    found.add(f"String.{m}")
    return found


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--set", default="sv-comp")
    ap.add_argument("--property", default="valid-assert",
                    choices=list(bench.CLI_PROPERTY.keys()))
    ap.add_argument("--timeout", type=int, default=90)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    tasks = [t for t, _ in bench.load_set(args.set)
             if args.property in t["expected"]]
    if args.limit and args.limit < len(tasks):
        tasks = tasks[:: len(tasks) // args.limit][: args.limit]

    env = dict(os.environ, RUST_LOG="ajave_core::certify=debug")
    refuted = []
    counts = Counter()
    scored = 0

    for i, t in enumerate(tasks, 1):
        cmd = [bench.BINARY, "--property", bench.CLI_PROPERTY[args.property]] + t["inputs"]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True,
                               timeout=args.timeout, env=env)
        except subprocess.TimeoutExpired:
            counts["timeout"] += 1
            continue
        verdict = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "UNKNOWN"
        exp = t["expected"][args.property]
        print(f"\r  {i}/{len(tasks)}", end="", file=sys.stderr)
        if (verdict == "TRUE") == exp and verdict != "UNKNOWN":
            scored += 1
            continue
        results = CENSUS.findall(r.stderr)
        if any(res == "Refuted" for res, _ in results):
            refuted.append((os.path.basename(t["yml"]).replace(".yml", ""), t, exp))
            counts["refuted"] += 1
        elif results:
            counts["other certification outcome"] += 1
        else:
            counts["no witness produced"] += 1
    print("\r" + " " * 30 + "\r", end="", file=sys.stderr)

    print(f"\n{len(tasks)} tasks — {scored} scored\n")
    for k, n in counts.most_common():
        print(f"  {k:<28} {n}")

    if not refuted:
        print("\nNo refuted witnesses. Nothing for this tool to say.")
        return

    # Cluster. A method appearing across several refuted tasks is one
    # divergence, not several.
    by_method = defaultdict(list)
    for name, t, exp in refuted:
        for m in calls_in(t):
            by_method[m].append(name)

    print(f"\n{len(refuted)} refuted witness(es), by the library method involved")
    print(f"{'method':<34}{'tasks':>6}  examples")
    print("-" * 78)
    for m, names in sorted(by_method.items(), key=lambda kv: -len(kv[1])):
        if len(names) < 2:
            continue
        print(f"{m:<34}{len(names):>6}  {', '.join(sorted(names)[:3])}")

    singles = [m for m, n in by_method.items() if len(n) == 1]
    if singles:
        print(f"\nappearing once: {', '.join(sorted(singles)[:18])}")

    print("\nA method spanning several refuted tasks is one divergence between\n"
          "our model and the JVM. Fixing it is worth the whole cluster, and the\n"
          "witness in each task is the reproduction.")


if __name__ == "__main__":
    main()
