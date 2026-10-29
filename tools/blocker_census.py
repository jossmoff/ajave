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

Reads three things the engines already emit:

  `smt-bmc: BLOCKER <reason> for <ObligationRef ..>`   per obligation, debug
  `smt-bmc: BLOCKER all_paths_complete ... (outer gate)` one line for ALL of
                                                         them, debug
  `orchestrator: N obligation(s) still open — <kinds>`   the ground truth for
                                                         how many are open, info

The outer-gate line matters for counting. When the BMC truncates before it
reaches the discharge loop, it refuses *every* obligation in one line, so a
regex over BLOCKER lines sees one refusal where the task has thirty. Obligation
counts therefore come from the orchestrator's own open-set, and the blockers
only say *why*; the two are reconciled per task and disagreements are reported
rather than averaged away.

What this tool does NOT see: it attributes to the BMC's refusal, because the
BMC is the engine that discharges most obligations. An obligation is open only
if *every* Over engine failed on it, so "model" here means "the BMC wanted a
model" — the AI or CHC may have declined the same obligation for a different
reason. Read the buckets as "what would unblock the dominant discharger".

Usage:
    python3 tools/blocker_census.py --set sv-comp --property valid-assert --jobs 6
    python3 tools/blocker_census.py --set smoke
    python3 tools/blocker_census.py --set /path/to/subset.set --dump out.tsv
"""

import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402

# Per-obligation refusal: `BLOCKER <reason> for ObligationRef { .. }`.
BLOCKER_RE = re.compile(r"BLOCKER (\S+) for (?!every)")
# The aggregate: one line covering every open obligation at once.
OUTER_RE = re.compile(
    r"BLOCKER all_paths_complete for every obligation \(outer gate\); "
    r"open in (\d+) method\(s\), truncated in (\d+) method\(s\), (\d+) open")
# The orchestrator's own count of what is still open, and of what kind.
OPEN_RE = re.compile(r"(\d+) obligation\(s\) still open — (.*)$", re.M)
RESIDUAL_RE = re.compile(r"residual from (\S+) \((\w+)\): (.*)$", re.M)
# An obligation an engine *violated* is not open -- it is closed, wrongly. The
# task still scores zero when replay refuses the witness, so the open-set alone
# is the wrong denominator for "what is unproven". This was found by a control
# run: TCAS_prop1 reported open=0 and still scored nothing.
DOWNGRADE_RE = re.compile(r"downgrading FALSE to UNKNOWN")
REPLAY_RE = re.compile(r"jvm-replay: (\w+) for ")
SCHED_RE = re.compile(r"schedule-replay: (confirmed|could not reproduce)")

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


def run_one(args):
    """One task-property pair. Returns a record, never raises.

    Runs with both log targets on: the BMC's blockers say *why*, the
    orchestrator's open-set says *how many*. Asking one process for both keeps
    them describing the same run -- two runs could disagree, and reconciling
    counts across runs is exactly the error this tool exists to avoid.
    """
    task, prop, timeout, binary = args
    # --trace makes the certifier say *why* it refused each witness, which is
    # the other half of the triage: a refuted witness scores zero exactly like
    # an unproven obligation, and needs completely different work.
    cmd = [binary, "--trace", "--property", bench.CLI_PROPERTY[prop]] + task["inputs"]
    env = dict(os.environ,
               RUST_LOG="ajave_engines::smt_bmc=debug,ajave_core::orchestrator=debug")
    rec = {"name": os.path.basename(task["yml"]).replace(".yml", ""),
           "yml": task["yml"], "prop": prop,
           "expected": task["expected"].get(prop),
           "verdict": "UNKNOWN", "blockers": [], "outer": None,
           "open_n": None, "open_kinds": "", "residuals": [],
           "downgraded": False, "replay": []}
    try:
        r = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        rec["verdict"] = "TIMEOUT"
        return rec
    except OSError as e:
        rec["verdict"] = f"ERROR({e.errno})"
        return rec
    if r.returncode < 0:
        # A signal, not a verdict. CLAUDE.md: under load the harness's own
        # kills terminate tasks, and scoring that as a verdict change is how a
        # contended run gets mistaken for a regression.
        rec["verdict"] = f"KILLED({-r.returncode})"
        return rec
    out = r.stdout.strip().splitlines()
    rec["verdict"] = out[-1] if out else "UNKNOWN"
    rec["blockers"] = BLOCKER_RE.findall(r.stderr)
    for m in OUTER_RE.finditer(r.stderr):
        rec["outer"] = tuple(int(x) for x in m.groups())
    for m in OPEN_RE.finditer(r.stderr):
        rec["open_n"], rec["open_kinds"] = int(m.group(1)), m.group(2).strip()
    rec["residuals"] = [m.group(3) for m in RESIDUAL_RE.finditer(r.stderr)]
    rec["downgraded"] = bool(DOWNGRADE_RE.search(r.stderr))
    rec["replay"] = REPLAY_RE.findall(r.stderr) + \
        [("schedule-" + m) for m in SCHED_RE.findall(r.stderr) if m != "confirmed"]
    return rec


def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--set", default="smoke")
    ap.add_argument("--property", default=None,
                    choices=list(bench.CLI_PROPERTY.keys()))
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--jobs", type=int, default=1,
                    help="parallel workers. Default 1: the timeout bucket is "
                         "contention-sensitive, so a parallel census must "
                         "either be read without that row or be run on a set "
                         "whose tasks are already known not to time out")
    ap.add_argument("--limit", type=int, default=None,
                    help="sample N tasks spread across the set")
    ap.add_argument("--dump", default=None,
                    help="write one TSV row per unproven task-property pair")
    args = ap.parse_args()
    self_test()

    tasks = []
    for task, override in bench.load_set(args.set):
        if args.property:
            props = [args.property] if args.property in task["expected"] else []
        elif override:
            props = [override] if override in task["expected"] else []
        else:
            props = list(task["expected"])
        for prop in props:
            tasks.append((task, prop, args.timeout, bench.BINARY))
    if args.limit and args.limit < len(tasks):
        step = len(tasks) // args.limit
        tasks = tasks[::step][: args.limit]

    print(f"machine: load {os.getloadavg()[0]:.1f}, {args.jobs} worker(s), "
          f"{len(tasks)} runs", file=sys.stderr)

    records = []
    if args.jobs > 1:
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
            for i, rec in enumerate(ex.map(run_one, tasks), 1):
                records.append(rec)
                print(f"\r  {i}/{len(tasks)}", end="", file=sys.stderr)
    else:
        for i, t in enumerate(tasks, 1):
            records.append(run_one(t))
            print(f"\r  {i}/{len(tasks)}", end="", file=sys.stderr)
    print("\r" + " " * 30 + "\r", end="", file=sys.stderr)

    report(records, args.dump)


# Sample log lines, verbatim from a real run. The regexes above are the whole
# instrument, and a regex that matches nothing reports a table of zeros rather
# than an error -- which is indistinguishable from a real finding of "no
# obligations are open". `$` without re.M did exactly that once, and the only
# reason it was caught is that a control run was demanded before the numbers
# were believed. So the patterns are pinned.
SELF_TEST = [
    (BLOCKER_RE, "smt-bmc: BLOCKER has_tainted_paths for ObligationRef "
                 "{ method: Main.foo, id: ObligationId(3) }", ["has_tainted_paths"]),
    (OUTER_RE, "smt-bmc: BLOCKER all_paths_complete for every obligation "
               "(outer gate); open in 4 method(s), truncated in 2 method(s), "
               "1 open method(s) were never truncated", [("4", "2", "1")]),
    (OPEN_RE, "orchestrator: 2 obligation(s) still open \u2014 Assertion=2\n"
              "orchestrator: done, verdict=Unknown", [("2", "Assertion=2")]),
    (DOWNGRADE_RE, "downgrading FALSE to UNKNOWN: witness did not replay "
                   "on a real JVM", None),
    (REPLAY_RE, "jvm-replay: Refuted for Main.foo#3", ["Refuted"]),
]


def self_test():
    """Refuse to run if any pattern has stopped matching what engines emit."""
    bad = []
    for rx, sample, expect in SELF_TEST:
        if expect is None:
            if not rx.search(sample):
                bad.append(rx.pattern)
            continue
        got = rx.findall(sample)
        if got != expect:
            bad.append(f"{rx.pattern}  (got {got!r}, want {expect!r})")
    # The outer-gate line also contains "BLOCKER ... for every obligation", and
    # BLOCKER_RE must NOT claim it: counting it as a per-obligation refusal is
    # how one line covering thirty obligations gets counted as one.
    outer = ("smt-bmc: BLOCKER all_paths_complete for every obligation "
             "(outer gate); open in 1 method(s), truncated in 1 method(s), 0 open")
    if BLOCKER_RE.findall(outer):
        bad.append("BLOCKER_RE matches the aggregate outer-gate line")
    if bad:
        print("blocker_census: the log format has changed; these patterns no "
              "longer match what the engines emit:", file=sys.stderr)
        for b in bad:
            print(f"  {b}", file=sys.stderr)
        sys.exit(2)


def classify(rec):
    """(bucket, dominant blocker, obligation count) for one unproven record.

    The obligation count is the orchestrator's, not a count of BLOCKER lines:
    the outer gate refuses every obligation in a single line, so counting
    lines would report one where the task has thirty.
    """
    n = rec["open_n"]
    if rec["verdict"] == "TIMEOUT":
        return "timeout", "(killed at the wall clock)", n
    if rec["verdict"].startswith("KILLED") or rec["verdict"].startswith("ERROR"):
        return "killed", "(signal, not a verdict)", n
    if rec["downgraded"]:
        # Ordered before the blocker case deliberately. Such a task usually
        # *also* has blockers -- the obligations nobody violated are still
        # unproven -- but the witness is the proximate reason this task scores
        # nothing, and it is the one that responds to different work.
        why = Counter(rec["replay"]).most_common(1)
        return "refuted-witness", \
            f"replay {why[0][0]}" if why else "replay refused (reason not logged)", n
    if rec["blockers"]:
        top = Counter(rec["blockers"]).most_common(1)[0][0]
        return KIND.get(top, "other"), top, n
    if rec["outer"] is not None:
        # The BMC never reached its discharge loop. Its own accounting of
        # where the open obligations live is the finding: obligations open in
        # a method that was never truncated cannot be explained by depth.
        _open_m, _trunc_m, elsewhere = rec["outer"]
        if elsewhere:
            return "budget", "all_paths_complete (outer gate, but open elsewhere)", n
        return "budget", "all_paths_complete (outer gate)", n
    return "no-candidate", "(nothing published)", n


def report(records, dump=None):
    total = len(records)
    scored = [r for r in records
              if (r["verdict"] == "TRUE" and r["expected"] is True)
              or (r["verdict"] == "FALSE" and r["expected"] is False)]
    wrong = [r for r in records
             if r["verdict"] in ("TRUE", "FALSE") and r not in scored]
    unproven = [r for r in records if r not in scored and r not in wrong]

    kinds, reasons = Counter(), Counter()
    ob_kinds, ob_by_bucket = Counter(), Counter()
    # Two disjoint populations of unfinished work, and reporting only the first
    # understates the second to zero:
    #   open      nobody closed the obligation
    #   refuted   an engine closed it with a violation the JVM would not
    #             reproduce, so it is closed *wrongly* and scores nothing
    refuted_ob = Counter()
    examples = defaultdict(list)
    counted, uncounted = 0, 0
    for r in unproven:
        bucket, top, n = classify(r)
        kinds[bucket] += 1
        reasons[top] += 1
        examples[bucket].append(r["name"])
        if n:
            ob_by_bucket[bucket] += n
            counted += n
            for part in r["open_kinds"].split():
                if "=" in part:
                    k, _, v = part.partition("=")
                    ob_kinds[k] += int(v)
        else:
            uncounted += 1
        refuted_ob[bucket] += len([x for x in r["replay"] if x != "Confirmed"])

    print(f"\n{total} runs — {len(scored)} scored, {len(wrong)} WRONG, "
          f"{len(unproven)} unproven")
    refuted_total = sum(refuted_ob.values())
    print(f"{counted} obligation(s) left open across them, and "
          f"{refuted_total} closed by a witness replay would not reproduce "
          f"({uncounted} run(s) reported no open-set)\n")
    # A table of zeros is not a finding, it is a broken instrument. Distinguish
    # the two: if runs that *did* reach the end of the orchestrator loop all
    # report no open-set, the parse is wrong, not the corpus.
    reached_end = [r for r in unproven
                   if r["verdict"] not in ("TIMEOUT",)
                   and not r["verdict"].startswith(("KILLED", "ERROR"))]
    if reached_end and counted == 0:
        print("!! every run that finished reported no open obligations. That is\n"
              "!! almost certainly a parse failure, not a corpus in which nothing\n"
              "!! is open -- the obligation columns below mean nothing. Check\n"
              "!! OPEN_RE against a real log before reading them.\n")

    RESPONDS = {
        "budget": "scheduling / more effort  <-- the scheduler's ceiling",
        "model":  "modelling the callee (lift java.base)",
        "theory": "a different encoding",
        "refuted": "feeding refutations back into the loop",
        "refuted-witness": "witness construction / replay fidelity (#25)",
        "timeout": "anytime engines, partly",
        "killed": "nothing — contention artefact, re-run on an idle machine",
        "no-candidate": "unknown — nothing published at all",
        "other": "unclassified blocker",
    }
    print(f"{'why not':<16} {'tasks':>6} {'% tasks':>8} {'open':>6} {'refuted':>8}"
          f"  responds to")
    print("-" * 94)
    for k, n in kinds.most_common():
        tp = 100 * n / len(unproven) if unproven else 0
        print(f"{k:<16} {n:>6} {tp:>7.1f}% {ob_by_bucket[k]:>6} "
              f"{refuted_ob[k]:>8}  {RESPONDS.get(k, '')}")

    print(f"\n{'dominant blocker':<52} {'tasks':>6}")
    print("-" * 60)
    for r, n in reasons.most_common():
        print(f"{r:<52} {n:>6}")

    if ob_kinds:
        print(f"\n{'open obligation kind':<32} {'count':>7}")
        print("-" * 41)
        for k, n in ob_kinds.most_common():
            print(f"{k:<32} {n:>7}")

    res = Counter(note for r in unproven for note in r["residuals"])
    if res:
        print(f"\n{'residual (found a path, could not use it)':<52} {'runs':>6}")
        print("-" * 60)
        for k, n in res.most_common(10):
            print(f"{k[:52]:<52} {n:>6}")

    for k in ("budget", "theory", "no-candidate", "refuted-witness"):
        if examples[k]:
            print(f"\n{k} examples: " + ", ".join(sorted(set(examples[k]))[:8]))

    if dump:
        with open(dump, "w") as f:
            f.write("name\tproperty\texpected\tverdict\tbucket\tblocker"
                    "\topen\tkinds\n")
            for r in unproven:
                bucket, top, n = classify(r)
                f.write(f"{r['name']}\t{r['prop']}\t{r['expected']}\t"
                        f"{r['verdict']}\t{bucket}\t{top}\t{n if n else ''}\t"
                        f"{r['open_kinds']}\n")
        print(f"\nwrote {len(unproven)} rows to {dump}")

    print("\nThe 'budget' row is what a scheduler can convert. Everything "
          "below it needs\na model or a theory, and will not move however the "
          "time is spent.")


if __name__ == "__main__":
    main()
