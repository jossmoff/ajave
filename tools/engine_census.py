#!/usr/bin/env python3
"""What each engine costs, and what it pays, by program shape.

Phase 0 of the cooperative-scheduling work. The portfolio currently runs every
engine on every task in a fixed order, and no one has measured which of them
earn their keep — the question has been guessed at repeatedly instead. A
scheduler cannot be built before this table exists, and a scheduler built on a
table keyed by *task name* would be the benchmark overfitting CLAUDE.md warns
about, relocated from the engines into the scheduler.

So the key is the program's **shape**: loops, floats, heap, strings,
transcendentals. Those are properties of a program, and a claim keyed on them is
one that can be checked against code nobody has seen.

Reads two log lines that the binary already emits at INFO:

    PROGRAM_SHAPE property=.. methods=.. blocks=.. loops=.. float=.. ...
    orchestrator: timing step <engine> <ms>ms discharged=N violated=M

Usage:
    python3 tools/engine_census.py --set smoke
    python3 tools/engine_census.py --set sv-comp --property valid-assert
    python3 tools/engine_census.py --set smoke --by-shape float,loops

Reports, per engine: total wall time, how many tasks it published anything on,
and the cost of each obligation it decided. An engine near the top of the time
column and the bottom of the decisions column is the one to look at first.

Two caveats the numbers cannot carry themselves:

  * Discharges are counted **per obligation**, and a task scores only when
    every obligation is decided. `interval-ai` routinely discharges hundreds of
    obligations in milliseconds and still leaves the task UNKNOWN, because the
    one obligation that mattered was not among them. So `ms/decision` ranks
    cheapness, not usefulness — read `tasks` alongside it.
  * An engine that publishes nothing is not necessarily idle. It may be the one
    that would have decided the task had a cheaper engine not closed the
    obligation first, which is exactly the failure `Approximations` was added
    to catch. Ablation (`tools/engine_ablation.py`) answers that question;
    this table only says where the time goes.
"""

import argparse
import os
import re
import subprocess
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402

SHAPE_RE = re.compile(r"PROGRAM_SHAPE (.*)$")
TIMING_RE = re.compile(
    r"timing step (\S+) (\d+)ms discharged=(\d+) violated=(\d+)"
)
# Flags worth bucketing on. Ordered, so a bucket name reads the same every run.
SHAPE_FLAGS = ["loops", "float", "heap", "string", "transcendental"]


def parse_shape(line):
    """`k=v k=v ...` into a dict, with `true`/`false` as bools."""
    out = {}
    for pair in line.split():
        if "=" not in pair:
            continue
        k, v = pair.split("=", 1)
        if v == "true":
            out[k] = True
        elif v == "false":
            out[k] = False
        else:
            try:
                out[k] = int(v)
            except ValueError:
                out[k] = v
    return out


def bucket_of(shape, keys):
    """A stable, human-readable name for this program's shape bucket."""
    on = [k for k in keys if shape.get(k)]
    return "+".join(on) if on else "plain"


def run_one(task, prop, timeout, binary):
    """Run one task with INFO logging and pull the census lines back out."""
    cmd = [binary, "--property", bench.CLI_PROPERTY[prop]] + task["inputs"]
    env = dict(os.environ, RUST_LOG="info")
    try:
        r = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout, env=env
        )
    except subprocess.TimeoutExpired:
        return None, [], "TIMEOUT"
    verdict = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "UNKNOWN"
    shape, timings = None, []
    for line in r.stderr.splitlines():
        m = SHAPE_RE.search(line)
        if m:
            shape = parse_shape(m.group(1))
            continue
        m = TIMING_RE.search(line)
        if m:
            timings.append(
                (m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)))
            )
    return shape, timings, verdict


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--set", default="smoke")
    ap.add_argument("--property", default=None,
                    choices=list(bench.CLI_PROPERTY.keys()),
                    help="override; default is each task's own")
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--by-shape", default=",".join(SHAPE_FLAGS),
                    help="comma-separated shape flags to bucket on")
    args = ap.parse_args()

    keys = [k.strip() for k in args.by_shape.split(",") if k.strip()]

    # `load_set` yields (task, property_override); a task's own yml is the only
    # source for which properties apply to it, so expand the same way bench.py
    # does rather than assuming one property per task.
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
    if args.limit:
        tasks = tasks[: args.limit]

    # (engine, bucket) -> [ms, runs, discharged, violated, tasks_published_on]
    stats = defaultdict(lambda: [0, 0, 0, 0, 0])
    bucket_runs = defaultdict(int)
    skipped = 0

    for i, (task, prop) in enumerate(tasks, 1):
        shape, timings, verdict = run_one(task, prop, args.timeout, bench.BINARY)
        if shape is None:
            skipped += 1
            continue
        b = bucket_of(shape, keys)
        bucket_runs[b] += 1
        for engine, ms, disch, viol in timings:
            s = stats[(engine, b)]
            s[0] += ms
            s[1] += 1
            s[2] += disch
            s[3] += viol
            if disch or viol:
                s[4] += 1
        print(f"\r  {i}/{len(tasks)} {verdict:8s} {b:30s}", end="", file=sys.stderr)
    print("\r" + " " * 60 + "\r", end="", file=sys.stderr)

    # Roll up per engine across all buckets first: the headline question is
    # which engines earn their keep at all.
    per_engine = defaultdict(lambda: [0, 0, 0, 0, 0])
    for (engine, _), s in stats.items():
        e = per_engine[engine]
        for j in range(5):
            e[j] += s[j]

    total_ms = sum(e[0] for e in per_engine.values()) or 1
    n_tasks = sum(bucket_runs.values()) or 1
    print(f"\n{'engine':<18} {'time':>9} {'%':>6} {'ran on':>7} {'paid on':>8} "
          f"{'disch':>7} {'viol':>6} {'ms/decision':>12}")
    print("-" * 82)
    for engine, (ms, runs, disch, viol, paid) in sorted(
        per_engine.items(), key=lambda kv: -kv[1][0]
    ):
        decisions = disch + viol
        per = f"{ms / decisions:,.0f}" if decisions else "—"
        print(f"{engine:<18} {ms/1000:>8.1f}s {100*ms/total_ms:>5.1f}% {runs:>7} "
              f"{paid:>8} {disch:>7} {viol:>6} {per:>12}")
    print(f"{'':<18} {'':>9} {'':>6} {'of ' + str(n_tasks):>7}")

    print(f"\n{'engine':<18} {'shape bucket':<28} {'time':>9} {'disch':>7} {'viol':>6}")
    print("-" * 72)
    for (engine, b), (ms, _runs, disch, viol, _paid) in sorted(
        stats.items(), key=lambda kv: -kv[1][0]
    ):
        if ms < 50 and disch == 0 and viol == 0:
            continue  # noise
        print(f"{engine:<18} {b:<28} {ms/1000:>8.1f}s {disch:>7} {viol:>6}")

    print(f"\nbuckets: " + ", ".join(
        f"{b} ({n})" for b, n in sorted(bucket_runs.items(), key=lambda kv: -kv[1])
    ))
    if skipped:
        print(f"{skipped} task(s) produced no PROGRAM_SHAPE line "
              f"(timeout, or no entry point)")
    print("\nAn engine high in the time column and empty in the decision columns "
          "is\nspending the budget without earning it. That is the finding this "
          "table exists\nto make, and it is a fact about a shape, not about a "
          "benchmark.")


if __name__ == "__main__":
    main()
