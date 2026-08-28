#!/usr/bin/env python3
"""For benchmarks we answer UNKNOWN, report WHICH obligations stay Open.

Runs ajave --trace, keeps only tasks whose verdict is UNKNOWN, and buckets the
remaining Open obligations by kind (NullDeref / ArrayBounds / NegArraySize /
Assertion / ...) and by the method they live in. This tells us what to build
next far more directly than guessing at engine features.

Usage: python3 tools/open_obligations.py [property] [per_category_limit]
"""

import glob
import os
import re
import subprocess
import sys
import yaml
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed

AJAVE = "./target/release/ajave"
SV = "sv-benchmarks"
SET_FILE = os.path.join(SV, "ReachSafety-Java.set")

OPEN_RE = re.compile(r"^\s+(\S+?)#(\d+) -> Open\s*$", re.M)
# `--ir` prints e.g. `check #2 ArrayBounds requires v15`
CHECK_RE = re.compile(r"check #(\d+) (\w+)")
METHOD_RE = re.compile(r"^method (\S+) \{$", re.M)


def resolve(yml_path):
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None, None
    d = os.path.dirname(yml_path)
    inputs = [os.path.join(d, i) for i in data["input_files"]]
    verdicts = {}
    for p in data.get("properties", []):
        pf = p.get("property_file", "")
        if "valid-assert" in pf:
            verdicts["assert"] = p.get("expected_verdict")
        elif "no-runtime-exception" in pf:
            verdicts["no-runtime-exception"] = p.get("expected_verdict")
    return inputs, verdicts


def find_all_tasks():
    tasks = []
    with open(SET_FILE) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                tasks.extend(sorted(glob.glob(os.path.join(SV, line))))
    return tasks


def category_of(p):
    parts = os.path.relpath(p, SV).split(os.sep)
    if len(parts) >= 3 and parts[0] == "java-ranger-regression":
        return f"{parts[0]}/{parts[1]}"
    return parts[0] if len(parts) >= 2 else "other"


def obligation_kinds(inputs):
    """Map 'Method#id' -> kind by parsing the IR dump."""
    try:
        r = subprocess.run([AJAVE, "--ir"] + inputs,
                           capture_output=True, text=True, timeout=60)
    except Exception:
        return {}
    ir = r.stdout
    marks = [(m.start(), m.group(1)) for m in METHOD_RE.finditer(ir)]
    kinds = {}
    for i, (pos, sig) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(ir)
        for cid, kind in CHECK_RE.findall(ir[pos:end]):
            kinds[f"{sig}#{cid}"] = kind
    return kinds


def run_one(arg):
    yml, prop, timeout = arg
    inputs, verdicts = resolve(yml)
    if inputs is None or verdicts.get(prop) is None:
        return None
    try:
        r = subprocess.run([AJAVE, "--trace", "--property", prop] + inputs,
                           capture_output=True, text=True, timeout=timeout)
    except Exception:
        return None
    # The verdict is the last line of stdout; `--trace` goes to stderr.
    verdict = r.stdout.strip().split("\n")[-1] if r.stdout.strip() else "ERROR"
    if verdict != "UNKNOWN":
        return None

    opens = [f"{m}#{i}" for m, i in OPEN_RE.findall(r.stderr)]
    if not opens:
        return yml, Counter({"<none-open>": 1}), Counter()

    kinds = obligation_kinds(inputs)
    kc = Counter()
    mc = Counter()
    for o in opens:
        kc[kinds.get(o, "<unknown-kind>")] += 1
        mname = o.rsplit("#", 1)[0]
        short = mname.split("(")[0]
        mc[short.split("/")[-1]] += 1
    return yml, kc, mc


def main():
    prop = sys.argv[1] if len(sys.argv) > 1 else "no-runtime-exception"
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    timeout = 60

    by_cat = defaultdict(list)
    for t in find_all_tasks():
        by_cat[category_of(t)].append(t)
    sample = []
    for cat, ts in by_cat.items():
        sample.extend(ts[:limit])

    print(f"property={prop}  sampling {len(sample)} tasks; keeping only UNKNOWN\n")

    kinds_by_cat = defaultdict(Counter)
    methods = Counter()
    n_unknown = Counter()

    with ProcessPoolExecutor(max_workers=8) as ex:
        futs = [ex.submit(run_one, (t, prop, timeout)) for t in sample]
        for f in as_completed(futs):
            res = f.result()
            if res is None:
                continue
            yml, kc, mc = res
            cat = category_of(yml)
            n_unknown[cat] += 1
            kinds_by_cat[cat].update(kc)
            methods.update(mc)

    allkinds = Counter()
    for c in kinds_by_cat.values():
        allkinds.update(c)

    print("Open-obligation kinds among UNKNOWN tasks:")
    total = sum(allkinds.values()) or 1
    for k, v in allkinds.most_common():
        print(f"  {k:<20s} {v:6d}  ({100*v/total:4.1f}%)")

    print("\nPer category (UNKNOWN count, then top kinds):")
    for cat in sorted(kinds_by_cat):
        top = ", ".join(f"{k}={v}" for k, v in kinds_by_cat[cat].most_common(3))
        print(f"  {cat:<40s} n={n_unknown[cat]:3d}  {top}")

    print("\nMethods most often holding Open obligations:")
    for m, v in methods.most_common(20):
        print(f"  {m:<50s} {v:5d}")


if __name__ == "__main__":
    main()
