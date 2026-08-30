#!/usr/bin/env python3
"""One benchmark runner for ajave: sets, scoring, regression gating.

Replaces the overlapping harnesses that grew one per need — `smoke_test.py`,
`score_full.py`, `score_own.py` and the Rust corpus test each re-implemented
task discovery, property selection and verdict comparison, and disagreed on all
three. The property mismatch in #54 was possible only because one of them
inferred the property instead of reading it.

    # fast gate before scoring
    tools/bench.py --set smoke

    # full corpus, one property, competition scoring
    tools/bench.py --set sv-comp --property valid-assert

    # our own suite, both properties, fail on any regression
    tools/bench.py --set ajave --check

    # record the current outcome as the baseline
    tools/bench.py --set ajave --update-baseline

Ground truth always comes from the task's own `.yml`. This runner never decides
what a task *should* answer, which is the invariant that keeps a gate honest.
"""

import argparse
import glob
import os
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from procguard import install_signal_handlers, run_guarded, sweep  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "benchmarks")
SETS = os.path.join(BENCH, "sets")
BINARY = os.path.join(ROOT, "target/release/ajave")

# Property file substring -> ajave's --property value.
PROPERTIES = {
    "valid-assert": "valid-assert",
    "assert": "valid-assert",
    "no-runtime-exception": "no-runtime-exception",
    "no-deadlock": "no-deadlock",
}
# ajave's CLI spells valid-assert as "assert".
CLI_PROPERTY = {
    "valid-assert": "assert",
    "no-runtime-exception": "no-runtime-exception",
    "no-deadlock": "no-deadlock",
}
# SV-COMP scoring. A wrong answer costs eight correct TRUEs.
POINTS = {("TRUE", True): 2, ("FALSE", False): 1,
          ("TRUE", False): -16, ("FALSE", True): -32}

TIMING_RE = re.compile(
    r"orchestrator: timing (?:init|step) (\S+) (\d+)ms"
    r"(?: discharged=(\d+))?(?: violated=(\d+))?"
)


# --------------------------------------------------------------------------
# Task discovery
# --------------------------------------------------------------------------

def read_yaml_task(path):
    """Read input_files and per-property expected verdicts from a task yml.

    Deliberately a line scanner rather than a YAML dependency: task files are
    generated and uniform, and the runner must work from a bare checkout.
    """
    try:
        text = open(path).read()
    except OSError:
        return None
    d = os.path.dirname(path)
    inputs, props = [], {}
    in_inputs = False
    pending = None
    for line in text.splitlines():
        t = line.strip()
        if t.startswith("input_files:"):
            in_inputs = True
            rest = t.split(":", 1)[1].strip()
            if rest:
                inputs.append(os.path.normpath(os.path.join(d, rest.strip('"\''))))
                in_inputs = False
            continue
        if in_inputs:
            if t.startswith("- "):
                inputs.append(os.path.normpath(
                    os.path.join(d, t[2:].strip().strip('"\''))))
                continue
            if t and not t.startswith("#"):
                in_inputs = False
        if "property_file:" in t:
            pf = t.split("property_file:", 1)[1].strip()
            pending = next((v for k, v in PROPERTIES.items() if k in pf), None)
        elif "expected_verdict:" in t and pending:
            v = t.split("expected_verdict:", 1)[1].strip()
            props[pending] = (v == "true")
            pending = None
    if not inputs or not props:
        return None
    return {"yml": path, "inputs": inputs, "expected": props}


def load_set(name):
    """Expand a set file into (task, property_override) pairs."""
    path = name if os.path.exists(name) else os.path.join(SETS, f"{name}.set")
    if not os.path.exists(path):
        sys.exit(f"no such set: {name} (looked in {SETS})")
    out, seen = [], set()
    for line in open(path):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split()
        pattern, override = parts[0], (parts[1] if len(parts) > 1 else None)
        matches = glob.glob(os.path.join(BENCH, pattern), recursive=True)
        if not matches:
            print(f"  warning: no tasks match {pattern}", file=sys.stderr)
        for m in sorted(matches):
            if (m, override) in seen:
                continue
            seen.add((m, override))
            task = read_yaml_task(m)
            if task:
                out.append((task, override))
    return out


# --------------------------------------------------------------------------
# Execution
# --------------------------------------------------------------------------

def run_one(args):
    task, prop, timeout, collect_timing = args
    cmd = [BINARY, "--property", CLI_PROPERTY[prop]] + task["inputs"]
    env = dict(os.environ, RUST_LOG="info") if collect_timing else dict(os.environ)

    # run_guarded, not subprocess.run: ajave spawns a solver and a JVM, and
    # killing only the parent orphans both. Leaked solvers and JVMs from
    # timed-out tasks are what exhausted this machine's memory and froze it.
    r = run_guarded(cmd, timeout=timeout, env=env)
    if r.timed_out:
        verdict, log = "TIMEOUT", ""
    elif r.returncode < 0:
        verdict, log = "ERROR", ""
    else:
        verdict = (r.stdout.strip().split("\n")[-1]
                   if r.stdout.strip() else "ERROR")
        log = (r.stdout + r.stderr) if collect_timing else ""
    t0 = time.time() - r.elapsed
    timing = {}
    for eng, ms, disch, viol in TIMING_RE.findall(log):
        cur = timing.get(eng, (0, 0, 0))
        timing[eng] = (cur[0] + int(ms),
                       cur[1] + (int(disch) if disch else 0),
                       cur[2] + (int(viol) if viol else 0))
    return {
        "yml": task["yml"], "property": prop,
        "expected": task["expected"][prop],
        "verdict": verdict, "elapsed": time.time() - t0, "timing": timing,
    }


def outcome_of(r):
    """correct | unproven | WRONG. A timeout is never wrong, only unproven."""
    want = "TRUE" if r["expected"] else "FALSE"
    if r["verdict"] == want:
        return "correct"
    if r["verdict"] in ("TRUE", "FALSE"):
        return "WRONG"
    return "unproven"


def rel(p):
    return os.path.relpath(p, BENCH)


def category_of(path):
    parts = rel(path).split(os.sep)
    return "/".join(parts[:2]) if len(parts) > 2 else parts[0]


# --------------------------------------------------------------------------
# Baselines
# --------------------------------------------------------------------------

def baseline_path(set_name):
    return os.path.join(SETS, f"{os.path.basename(set_name)}.baseline")


def read_baseline(set_name):
    p = baseline_path(set_name)
    if not os.path.exists(p):
        return {}
    out = {}
    for line in open(p):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        f = line.split("\t")
        if len(f) >= 3:
            out[(f[0], f[1])] = f[2]
    return out


def write_baseline(set_name, results):
    p = baseline_path(set_name)
    with open(p, "w") as fh:
        fh.write(
            "# Outcome ajave achieves on each task today.\n"
            f"# Regenerate: tools/bench.py --set {set_name} --update-baseline\n"
            "#\n"
            "# A task moving correct -> unproven fails --check. Improving one to\n"
            "# correct is expected to update this file in the same commit.\n"
            "# Format: <task>\\t<property>\\t<outcome>\\t<verdict>\n"
        )
        for r in sorted(results, key=lambda r: (r["yml"], r["property"])):
            fh.write(f"{rel(r['yml'])}\t{r['property']}\t"
                     f"{outcome_of(r)}\t{r['verdict']}\n")
    return p


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------

def report(results, args, elapsed):
    counts = Counter(outcome_of(r) for r in results)
    wrong = [r for r in results if outcome_of(r) == "WRONG"]

    score = 0
    cats = defaultdict(lambda: Counter())
    for r in results:
        cats[category_of(r["yml"])][outcome_of(r)] += 1
        score += POINTS.get((r["verdict"], r["expected"]), 0)

    load, cores = machine_load()
    free = free_memory_gb()
    if load is not None:
        mem = f", {free:.1f}GB free" if free is not None else ""
        print(f"\nmachine: load {load:.1f} on {cores} cores, "
              f"{args.jobs} workers{mem}")
    print(f"\n{len(results)} runs in {elapsed:.0f}s — "
          f"{counts['correct']} correct, {counts['unproven']} unproven, "
          f"{counts['WRONG']} WRONG")
    if any(r["verdict"] == "TIMEOUT" for r in results):
        n = sum(1 for r in results if r["verdict"] == "TIMEOUT")
        print(f"  ({n} timeouts — counts are contention-sensitive; "
              f"use an idle machine)")
    print(f"SV-COMP score: {score}")

    if args.by_category:
        print(f"\n{'category':<38}{'ok':>6}{'unproven':>10}{'WRONG':>7}")
        for c in sorted(cats):
            k = cats[c]
            print(f"  {c:<36}{k['correct']:>6}{k['unproven']:>10}"
                  f"{k['WRONG']:>7}")

    if args.timing:
        agg = defaultdict(lambda: [0, 0, 0])
        for r in results:
            for eng, (ms, d, v) in r["timing"].items():
                a = agg[eng]
                a[0] += ms
                a[1] += d
                a[2] += v
        if agg:
            tot = sum(a[0] for a in agg.values()) or 1
            print("\nEngine attribution (completed runs only — a timed-out run")
            print("emits no timing line, so a hung engine is under-counted):")
            print(f"  {'engine':<16}{'sec':>9}{'%':>7}"
                  f"{'discharged':>12}{'violated':>10}")
            for eng, a in sorted(agg.items(), key=lambda kv: -kv[1][0]):
                print(f"  {eng:<16}{a[0]/1000:>9.1f}{100*a[0]/tot:>6.1f}%"
                      f"{a[1]:>12}{a[2]:>10}")

    if args.slowest:
        print(f"\nSlowest {args.slowest}:")
        for r in sorted(results, key=lambda r: -r["elapsed"])[:args.slowest]:
            print(f"  {r['elapsed']:6.1f}s  {r['verdict']:<8} "
                  f"{rel(r['yml'])} [{r['property']}]")

    if wrong:
        print(f"\n{len(wrong)} WRONG — a wrong TRUE costs -16, a wrong "
              f"FALSE -32:")
        for r in wrong:
            want = "TRUE" if r["expected"] else "FALSE"
            print(f"  {rel(r['yml'])} [{r['property']}]: "
                  f"said {r['verdict']}, expected {want}")
    return counts, wrong


def machine_load():
    """(1-minute load average, core count), or (None, None) if unavailable."""
    try:
        return os.getloadavg()[0], os.cpu_count() or 1
    except (OSError, AttributeError):
        return None, None


def free_memory_gb():
    """Free + inactive memory in GB, or None if it cannot be determined.

    Memory, not CPU, is what actually took this machine down: each concurrent
    run holds an ajave, a solver and a JVM, and leaked ones never released it.
    Cleanup is fixed, but a run should still refuse to start more workers than
    the machine can feed.
    """
    try:
        if sys.platform == "darwin":
            out = subprocess.run(["vm_stat"], capture_output=True, text=True,
                                 timeout=5).stdout
            page = 4096
            m = re.search(r"page size of (\d+) bytes", out)
            if m:
                page = int(m.group(1))
            free = inactive = 0
            for line in out.splitlines():
                if line.startswith("Pages free:"):
                    free = int(line.split(":")[1].strip().rstrip("."))
                elif line.startswith("Pages inactive:"):
                    inactive = int(line.split(":")[1].strip().rstrip("."))
            return (free + inactive) * page / 1e9
        with open("/proc/meminfo") as fh:
            for line in fh:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) * 1024 / 1e9
    except (OSError, ValueError, subprocess.SubprocessError):
        return None
    return None


# Peak resident set of one run: ajave plus its solver plus a JVM for replay.
# Conservative — exceeding it is what froze the machine.
GB_PER_WORKER = 1.5


def check_machine_idle(jobs, require_idle):
    """Warn — or refuse — when the machine is too busy to time anything.

    Timeout counts are the single largest term in the score and they are
    contention-sensitive: the same build measured 89 timeouts on a loaded
    machine and 43 on an idle one, a ~20 point difference that looked exactly
    like a code regression and was investigated as one (#64).

    A run whose load is already high before it starts cannot produce a
    comparable number, so say so loudly rather than emit a plausible one.
    """
    free = free_memory_gb()
    if free is not None and free < jobs * GB_PER_WORKER:
        safe = max(1, int(free / GB_PER_WORKER))
        print(f"  WARNING: only {free:.1f}GB free — {jobs} workers need about "
              f"{jobs * GB_PER_WORKER:.1f}GB.", file=sys.stderr)
        print(f"  Reduce with --jobs {safe}, or run tools/cleanup.sh if an "
              f"earlier run left processes behind.", file=sys.stderr)
        if require_idle:
            sys.exit("Refusing to run: not enough free memory.")

    load, cores = machine_load()
    if load is None:
        return
    headroom = cores - load
    if headroom >= jobs * 0.75:
        return
    msg = (f"machine is busy: load {load:.1f} on {cores} cores, "
           f"{jobs} workers requested")
    if require_idle:
        sys.exit(f"{msg}\nRefusing to run: timing and timeout counts would not "
                 f"be comparable.\nWait for the machine to settle, or pass "
                 f"--allow-busy to measure verdicts only.")
    print(f"  WARNING: {msg}", file=sys.stderr)
    print("  Timeout counts will be inflated and are not comparable to a "
          "quiet-machine run.", file=sys.stderr)


def main():
    ap = argparse.ArgumentParser(
        description="Run an ajave benchmark set.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__.split("Ground truth")[0].split("\n", 2)[2])
    ap.add_argument("--set", default="smoke",
                    help="set name in benchmarks/sets, or a path (default: smoke)")
    ap.add_argument("--property", choices=["valid-assert",
                                           "no-runtime-exception",
                                           "no-deadlock", "all"],
                    help="override the property; default is each task's own")
    ap.add_argument("--jobs", type=int, default=6,
                    help="parallel workers (default 6). Kept below core count: "
                         "each run spawns a solver child, and oversubscribing "
                         "turns slow tasks into timeouts")
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--limit", type=int,
                    help="sample N tasks spread across the set")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 on any WRONG or any regression vs the baseline")
    ap.add_argument("--update-baseline", action="store_true")
    ap.add_argument("--timing", action="store_true",
                    help="per-engine attribution (needs RUST_LOG=info)")
    ap.add_argument("--by-category", action="store_true")
    ap.add_argument("--slowest", type=int, metavar="N")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--require-idle", action="store_true",
                    help="refuse to run unless the machine is idle. Use for "
                         "any run whose timings or timeout counts you intend "
                         "to compare against another run")
    ap.add_argument("--allow-busy", action="store_true",
                    help="suppress the busy-machine warning")
    ap.add_argument("--repeat", type=int, metavar="N",
                    help="run every task N times and fail if any task returns "
                         "more than one distinct verdict. A verifier whose "
                         "answer varies between identical runs makes every "
                         "baseline and score delta meaningless (#66)")
    ap.add_argument("--sweep", action="store_true",
                    help="kill leftover ajave/solver/JVM processes and remove "
                         "stale temp dirs before starting")
    args = ap.parse_args()

    if not args.allow_busy:
        check_machine_idle(args.jobs, args.require_idle)

    if not os.path.exists(BINARY):
        sys.exit(f"binary not found: {BINARY}\nBuild first: cargo build --release")

    # Ctrl-C must not leave solvers and JVMs behind.
    install_signal_handlers()

    if args.sweep:
        print("sweeping strays from earlier runs...", file=sys.stderr)
        sweep()

    entries = load_set(args.set)
    if args.limit and len(entries) > args.limit:
        step = max(1, len(entries) // args.limit)
        entries = entries[::step][:args.limit]

    # Expand each task into one run per property it declares. A task's yml is
    # the only source for which properties apply to it.
    work = []
    for task, override in entries:
        if args.property and args.property != "all":
            props = [args.property] if args.property in task["expected"] else []
        elif override:
            props = [override] if override in task["expected"] else []
        elif args.property == "all":
            props = list(task["expected"])
        else:
            props = list(task["expected"])
        for p in props:
            work.append((task, p, args.timeout,
                         args.timing or args.update_baseline))

    if not work:
        sys.exit("no runs to perform — check the set and --property")

    if args.repeat and args.repeat > 1:
        work = [w for w in work for _ in range(args.repeat)]
        print(f"determinism check: {args.repeat} repeats per task")

    print(f"{len(work)} runs from set '{args.set}' ({args.jobs} workers)")
    t0 = time.time()
    results = []
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        for r in ex.map(run_one, work):
            results.append(r)
            if not args.quiet:
                o = outcome_of(r)
                sym = {"correct": "+", "unproven": ".", "WRONG": "X"}[o]
                print(f"  {sym} {rel(r['yml']):<52} {r['property']:<21} "
                      f"{r['verdict']}", flush=True)

    # Whatever happened above, leave nothing behind.
    sweep(verbose=False)

    if args.repeat and args.repeat > 1:
        seen = defaultdict(set)
        for r in results:
            seen[(rel(r["yml"]), r["property"])].add(r["verdict"])
        varying = {k: v for k, v in seen.items() if len(v) > 1}
        print(f"\ndeterminism: {len(seen)} task(s) x {args.repeat} runs")
        if varying:
            print(f"  {len(varying)} task(s) returned more than one verdict:")
            for (task, prop), verdicts in sorted(varying.items()):
                print(f"    {task} [{prop}]: {', '.join(sorted(verdicts))}")
            print("\n  A verdict that varies between identical runs makes every"
                  "\n  baseline unreliable and every score delta unreadable.")
            return 1
        print("  all verdicts stable")
        return 0

    if args.update_baseline:
        p = write_baseline(args.set, results)
        print(f"\nbaseline written: {os.path.relpath(p, ROOT)} "
              f"({len(results)} runs)")
        return 0

    counts, wrong = report(results, args, time.time() - t0)

    if not args.check:
        return 0

    baseline = read_baseline(args.set)
    regressed = [r for r in results
                 if outcome_of(r) != "correct"
                 and baseline.get((rel(r["yml"]), r["property"])) == "correct"]
    if regressed:
        print(f"\n{len(regressed)} regressed from correct:")
        for r in regressed:
            print(f"  {rel(r['yml'])} [{r['property']}]: "
                  f"now {outcome_of(r)} ({r['verdict']})")
    if wrong or regressed:
        print("\nFAIL")
        return 1
    print("\nPASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
