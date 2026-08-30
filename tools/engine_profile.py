#!/usr/bin/env python3
"""Attribute wall-clock and discharges to engines across a benchmark set.

Answers "which engine is eating the timeouts" with measurement rather than
inference. Reads the `orchestrator: timing ...` lines emitted at INFO.

Usage:
    python3 tools/engine_profile.py --property valid-assert [--limit N]
    python3 tools/engine_profile.py --tasks file-with-one-yml-per-line
"""
import argparse, collections, glob, os, re, subprocess, sys, yaml

TIMING = re.compile(r"orchestrator: timing (init|step) (\S+) (\d+)ms(?: discharged=(\d+))?")

def resolve(yml):
    d = yaml.safe_load(open(yml))
    if not d or "input_files" not in d:
        return None
    inp = d["input_files"]
    inp = [inp] if isinstance(inp, str) else inp
    return [os.path.join(os.path.dirname(yml), i) for i in inp]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--property", default="assert")
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--limit", type=int)
    ap.add_argument("--tasks")
    a = ap.parse_args()

    if a.tasks:
        ymls = [l.strip() for l in open(a.tasks) if l.strip()]
    else:
        ymls = sorted(glob.glob("sv-benchmarks/**/*.yml", recursive=True))
    if a.limit:
        ymls = ymls[:: max(1, len(ymls) // a.limit)][: a.limit]

    ms = collections.Counter()
    disch = collections.Counter()
    timeouts = []
    env = dict(os.environ, RUST_LOG="info")
    for y in ymls:
        files = resolve(y)
        if not files:
            continue
        try:
            r = subprocess.run(
                ["./target/release/ajave", "--property", a.property] + files,
                capture_output=True, text=True, timeout=a.timeout, env=env)
        except subprocess.TimeoutExpired:
            timeouts.append(y)
            continue
        for kind, eng, t, d in TIMING.findall(r.stdout + r.stderr):
            ms[eng] += int(t)
            if d:
                disch[eng] += int(d)

    total = sum(ms.values()) or 1
    print(f"{len(ymls)} tasks, {len(timeouts)} timed out\n")
    print(f"{'engine':<16}{'ms':>10}{'%':>7}{'discharged':>12}")
    for eng, t in ms.most_common():
        print(f"{eng:<16}{t:>10}{100*t/total:>6.1f}%{disch.get(eng,0):>12}")
    if timeouts:
        print("\ntimeouts:")
        for t in timeouts[:25]:
            print("  ", t)

main()
