#!/usr/bin/env python3
"""Collect everything about a corpus run once; project it many ways.

Nine scripts used to answer "run the corpus, then bucket what failed by some
property": engine_census, blocker_census, pairing_census, refutation_sweep,
open_obligations, heap_survey, blocking_calls, engine_profile, engine_audit.
They differed in the grouping key and the projection, not the mechanism, so
each re-implemented task loading, parallel execution, log parsing and
formatting -- and three acquired the same ProcessPoolExecutor bug separately.

The expensive part is the corpus pass, and each of those scripts decided in
advance what to keep and discarded the rest. A question nobody anticipated
therefore needed a new script *and* another full run.

So: `collect` does one pass and writes the union of what those scripts
derived, one JSON record per (task, property). `report` projects it. A new
question is a new projection over data already on disk, and `--kind raw` dumps
everything for an agent to triage however it likes.

Usage:
    python3 tools/survey.py collect --set smoke --out survey.json
    python3 tools/survey.py report --in survey.json --kind engines
    python3 tools/survey.py report --in survey.json --kind raw > all.json
"""

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402

# Engine activity: `timing step <id> <ms>ms discharged=<n> violated=<n>`.
TIMING = re.compile(r"timing step (\S+) (\d+)ms discharged=(\d+) violated=(\d+)")
# Why an engine declined, as each engine already logs it.
DECLINE = re.compile(r"(\w[\w-]*): (skipping|nothing|no |declin|stalled)[^\n]*")
# What JVM replay made of a witness.
CENSUS = re.compile(r"REPLAY_CENSUS result=(\w+)[^\n]*?method=(\S+)")
# Completeness flags the BMC reports.
COMPLETE = re.compile(r"Completeness \{ ([^}]*) \}")
# Program shape, which the CLI logs once per run.
SHAPE = re.compile(r"PROGRAM_SHAPE ([^\n]*)")
# Library calls the sources mention. Deliberately syntactic: the point is to
# cluster, and a name in the source is a name the task exercises.
CALL = re.compile(
    r"\b(Math|StrictMath|Integer|Long|Double|Float|Character|String|StringBuilder"
    r"|Boolean|Byte|Short|Arrays|Objects|List|Map)\s*\.\s*([a-zA-Z]\w*)"
)


def _sources(task):
    out = []
    for inp in task["inputs"]:
        if not os.path.isdir(inp) or inp.endswith("common"):
            continue
        for root, _, files in os.walk(inp):
            out += [os.path.join(root, f) for f in files if f.endswith(".java")]
    return out


def _one(job):
    """Run one (task, property) and record everything it said."""
    yml, prop, timeout = job
    task = bench.read_yaml_task(yml)
    if task is None or prop not in (task.get("expected") or {}):
        return None
    env = dict(os.environ, RUST_LOG="info,ajave_core::certify=debug")
    cmd = [bench.BINARY, "--property", bench.CLI_PROPERTY[prop]] + task["inputs"]
    import time
    started = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
        verdict = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "UNKNOWN"
        err = r.stderr
    except subprocess.TimeoutExpired:
        verdict, err = "TIMEOUT", ""
    elapsed = round(time.time() - started, 1)

    expected = task["expected"][prop]
    correct = (verdict == "TRUE" and expected) or (verdict == "FALSE" and not expected)
    wrong = verdict in ("TRUE", "FALSE") and not correct

    calls = set()
    for p in _sources(task):
        try:
            text = open(p, errors="ignore").read()
        except OSError:
            continue
        calls |= {f"{c}.{m}" for c, m in CALL.findall(text)}

    # `yml` may be absolute; report it relative to benchmarks/ either way.
    rel = yml.split("benchmarks/", 1)[-1]
    return {
        "task": rel,
        "category": rel.split("/")[1] if rel.count("/") > 1 else "?",
        "property": prop,
        "expected": expected,
        "verdict": verdict,
        "correct": correct,
        "wrong": wrong,
        "points": (2 if expected else 1) if correct else 0,
        "seconds": elapsed,
        # [engine, ms, discharged, violated]
        "engines": [[e, int(ms), int(d), int(v)] for e, ms, d, v in TIMING.findall(err)],
        "declines": sorted({m.group(0)[:90] for m in DECLINE.finditer(err)}),
        "replay": [list(t) for t in CENSUS.findall(err)],
        "completeness": (COMPLETE.search(err).group(1) if COMPLETE.search(err) else ""),
        "shape": (SHAPE.search(err).group(1) if SHAPE.search(err) else ""),
        "calls": sorted(calls),
    }


def collect(args):
    tasks = [t for t, _ in bench.load_set(args.set)]
    jobs = []
    for t in tasks:
        for prop in t["expected"]:
            if args.property in (None, "all", prop):
                jobs.append((t["yml"], prop, args.timeout))
    if args.limit:
        jobs = jobs[:: max(1, len(jobs) // args.limit)][: args.limit]

    rows = []
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        for i, rec in enumerate(ex.map(_one, jobs), 1):
            if rec:
                rows.append(rec)
            print(f"\r  {i}/{len(jobs)}", end="", file=sys.stderr)
    print("\r" + " " * 24 + "\r", end="", file=sys.stderr)

    json.dump(rows, open(args.out, "w"), indent=1)
    scored = sum(r["points"] for r in rows)
    print(f"{len(rows)} records -> {args.out}")
    print(f"  {sum(r['correct'] for r in rows)} correct, "
          f"{sum(r['wrong'] for r in rows)} WRONG, {scored} points")


# --- projections ------------------------------------------------------------

def _unsolved(rows):
    return [r for r in rows if not r["correct"]]


def p_engines(rows):
    """Which engine did the work, and which never contributed."""
    did = Counter()
    ran = Counter()
    for r in rows:
        for e, _ms, d, v in r["engines"]:
            ran[e] += 1
            if d or v:
                did[e] += 1
    print(f"{'engine':<16}{'ran':>7}{'contributed':>13}{'share':>8}")
    for e, n in ran.most_common():
        c = did.get(e, 0)
        print(f"{e:<16}{n:>7}{c:>13}{(100*c//n if n else 0):>7}%")
    idle = [e for e in ran if not did.get(e)]
    if idle:
        print(f"\nnever contributed: {', '.join(sorted(idle))}")


def p_blockers(rows):
    """Why the unsolved tasks were not solved, as the engines themselves said."""
    c = Counter()
    for r in _unsolved(rows):
        if r["verdict"] == "TIMEOUT":
            c["TIMEOUT"] += 1
            continue
        for d in r["declines"] or ["(no decline logged)"]:
            c[d] += 1
    for k, n in c.most_common(25):
        print(f"{n:>5}  {k}")


def p_pairs(rows):
    """Engines that declined on the same task: candidate cooperations."""
    c = Counter()
    for r in _unsolved(rows):
        eng = sorted({d.split(":")[0] for d in r["declines"]})
        for i in range(len(eng)):
            for j in range(i + 1, len(eng)):
                c[(eng[i], eng[j])] += 1
    print(f"{'pair':<34}{'tasks':>7}")
    for (a, b), n in c.most_common(20):
        print(f"{a + ' + ' + b:<34}{n:>7}")


def p_refutations(rows):
    """Witnesses the JVM rejected, clustered by the library method involved."""
    by = defaultdict(list)
    for r in rows:
        if not any(res == "Refuted" for res, _ in r["replay"]):
            continue
        for m in r["calls"]:
            by[m].append(r["task"].split("/")[-1])
    print(f"{'method':<34}{'tasks':>7}  examples")
    for m, names in sorted(by.items(), key=lambda kv: -len(kv[1])):
        if len(names) < 2:
            continue
        print(f"{m:<34}{len(names):>7}  {', '.join(sorted(names)[:3])}")
    print("\nA method spanning several refuted witnesses is one divergence\n"
          "between our model and the JVM, with a reproduction attached.")


def p_obligations(rows):
    """Completeness flags on the unsolved tasks."""
    c = Counter()
    for r in _unsolved(rows):
        for part in r["completeness"].split(","):
            part = part.strip()
            if part.endswith("true"):
                c[part.split(":")[0]] += 1
    for k, n in c.most_common():
        print(f"{n:>5}  {k}")


def p_calls(rows):
    """Library methods appearing in unsolved tasks."""
    c = Counter()
    for r in _unsolved(rows):
        c.update(r["calls"])
    for k, n in c.most_common(30):
        print(f"{n:>5}  {k}")


def p_timings(rows):
    """Where wall time went, per engine and per task."""
    per = Counter()
    for r in rows:
        for e, ms, _d, _v in r["engines"]:
            per[e] += ms
    total = sum(per.values()) or 1
    print(f"{'engine':<16}{'seconds':>10}{'share':>8}")
    for e, ms in per.most_common():
        print(f"{e:<16}{ms/1000:>10.1f}{100*ms//total:>7}%")
    print("\nslowest tasks:")
    for r in sorted(rows, key=lambda r: -r["seconds"])[:10]:
        print(f"  {r['seconds']:>7.1f}s  {r['verdict']:<8} {r['task']}")


def p_raw(rows):
    json.dump(rows, sys.stdout, indent=1)


KINDS = {
    "engines": p_engines, "blockers": p_blockers, "pairs": p_pairs,
    "refutations": p_refutations, "obligations": p_obligations,
    "calls": p_calls, "timings": p_timings, "raw": p_raw,
}


def report(args):
    rows = json.load(open(getattr(args, "in")))
    fn = KINDS.get(args.kind)
    if not fn:
        sys.exit(f"unknown kind {args.kind!r}; choose from {', '.join(KINDS)}")
    if args.kind != "raw":
        n = len(rows)
        u = len(_unsolved(rows))
        print(f"{n} records, {n - u} correct, {u} unsolved "
              f"({sum(r['wrong'] for r in rows)} WRONG)\n")
    fn(rows)


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("collect", help="one corpus pass, everything recorded")
    c.add_argument("--set", default="smoke")
    c.add_argument("--property", default=None,
                   help="valid-assert, no-runtime-exception, or all (default: all)")
    c.add_argument("--out", default="survey.json")
    c.add_argument("--timeout", type=int, default=300)
    c.add_argument("--jobs", type=int, default=4)
    c.add_argument("--limit", type=int)
    c.set_defaults(fn=collect)

    r = sub.add_parser("report", help="project a collected survey")
    r.add_argument("--in", default="survey.json")
    r.add_argument("--kind", default="engines",
                   help=", ".join(KINDS))
    r.set_defaults(fn=report)

    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
