#!/usr/bin/env bash
# Run a scoring pass, waiting for the machine to go idle first.
#
# Why this exists: `bench.py` exits 1 whenever the run contains a wrong answer,
# and valid-assert always contains one (the ReverseInterpolator benchmark
# defect, #72). A retry loop written as `bench.py ... && break` therefore never
# breaks -- it re-runs the whole corpus up to N times, and launching a second
# such loop while the first is still going puts two scoring runs on the machine
# at once. That happened: a valid-assert run took 9,865s instead of 1,078s at
# load 7.6, and three tasks "changed" to TIMEOUT purely from contention.
#
# Retry only on the idle refusal, which is the only condition a retry can fix.
set -u
prop="$1"; out="$2"
for _ in $(seq 1 60); do
    python3 tools/bench.py --set sv-comp --property "$prop" --jobs 4 --require-idle > "$out" 2>&1
    grep -q "machine is busy" "$out" || break
    sleep 120
done
