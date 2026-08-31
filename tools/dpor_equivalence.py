#!/usr/bin/env python3
"""DPOR must agree with the unreduced baseline wherever the baseline decides.

A reduction that changes an answer is unsound. Exhaustive may return UNKNOWN
where DPOR decides — that is the reduction paying off — but the two must never
*disagree* on a decided verdict.

This exists because DPOR was genuinely unsound for no-deadlock and it took a
manual observation to notice: it explored 236 states of LockOrderInversion and
reported no deadlock, a wrong TRUE. The cause was structural. DPOR justifies its
reduction over *enabled* transitions, and a deadlock is the absence of enabled
transitions, so a blocking transition carried no accesses, no dependency was
seen, and the backtrack point that would try the other acquire order was never
created. Fixed by making Step::Blocked carry its monitor and feeding that to the
dependency test as an Access::Monitor.

Run this after any change to the explorer, the dependency relation, or the
backtrack computation. Exit code 1 if the strategies disagree anywhere.

    python3 tools/dpor_equivalence.py
"""
import glob, os, sys, subprocess
sys.path.insert(0,'tools')
from bench import read_yaml_task
PROP={"valid-assert.prp":"assert","no-runtime-exception.prp":"no-runtime-exception","no-deadlock.prp":"no-deadlock"}
bad=0
for y in sorted(glob.glob("benchmarks/ajave/concurrency/*.yml")):
    d=read_yaml_task(y)
    if not d: continue
    for prop, exp in d["expected"].items():
        cli={"valid-assert":"assert","no-runtime-exception":"no-runtime-exception","no-deadlock":"no-deadlock","no-data-race":"no-data-race"}[prop]
        out={}
        for mode in ("1","0"):
            env=dict(os.environ, AJAVE_DEADLOCK_EXHAUSTIVE=mode)
            try:
                r=subprocess.run(["./target/release/ajave","--property",cli]+d["inputs"],
                                 capture_output=True,text=True,timeout=60,env=env)
                out[mode]=r.stdout.strip().split("\n")[-1] if r.stdout.strip() else "ERROR"
            except subprocess.TimeoutExpired: out[mode]="TIMEOUT"
        ex, dp = out["1"], out["0"]
        decided = lambda v: v in ("TRUE","FALSE")
        disagree = decided(ex) and decided(dp) and ex != dp
        want = "TRUE" if exp else "FALSE"
        flag = "DISAGREE" if disagree else ("dpor-better" if decided(dp) and not decided(ex) else "")
        if disagree: bad+=1
        print(f"  {os.path.basename(y)[:-4]:<26}{prop:<22} exhaustive={ex:<8} dpor={dp:<8} want={want:<6}{flag}")
print(f"\n  strategies disagree on {bad} run(s)  <- must be 0")
sys.exit(1 if bad else 0)
