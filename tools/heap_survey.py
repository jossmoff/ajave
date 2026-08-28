#!/usr/bin/env python3
"""Survey heap-operation usage PER METHOD to size the CHC/AI heap model.

Whole-program counting is useless here: every benchmark has `main(String[])`
and every enum has a synthetic `$values()` that news an array, so a
program-level "uses arrays" flag is true for ~100% of tasks.

What actually matters is the granularity the engines work at: a *method*.
CHC/CEGAR/AI bail per-method, so we classify each method as:
  none   - no heap ops at all (already analyzable)
  field  - instance/static field access only (unlocked by flat field model)
  array  - any array load/store/alloc (needs array theory)

We also report how many methods carry obligations, since a method with no
obligations costs nothing if we can't analyze it.
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

# Synthetic / boilerplate methods that are never the interesting target.
SKIP_METHOD_RE = re.compile(r"\.(\$values|values|valueOf|<clinit>)\(")

METHOD_RE = re.compile(r"^method (\S+) \{$", re.M)


def resolve_inputs(yml_path):
    with open(yml_path) as f:
        data = yaml.safe_load(f)
    if not data or "input_files" not in data:
        return None
    task_dir = os.path.dirname(yml_path)
    return [os.path.join(task_dir, inp) for inp in data["input_files"]]


def find_all_tasks():
    tasks = []
    with open(SET_FILE) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            tasks.extend(sorted(glob.glob(os.path.join(SV, line))))
    return tasks


def category_of(yml_path):
    rel = os.path.relpath(yml_path, SV)
    parts = rel.split(os.sep)
    if len(parts) >= 2:
        cat = parts[0]
        if len(parts) >= 3 and parts[0] in ("java-ranger-regression",):
            cat = f"{parts[0]}/{parts[1]}"
        return cat
    return "other"


def split_methods(ir):
    """Yield (method_signature, body_text) for each method in the IR dump."""
    marks = [(m.start(), m.group(1)) for m in METHOD_RE.finditer(ir)]
    for i, (pos, sig) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(ir)
        yield sig, ir[pos:end]


def classify_method(text):
    has_array = bool(
        re.search(r"=\s*\S+\[\S+\]\s*$", text, re.M)      # ArrayLoad
        or re.search(r"^\s*\S+\[\S+\]\s*=\s", text, re.M)  # ArrayStore
        or re.search(r"new\s+\S+\[", text)                 # NewArray
    )
    has_field = bool(
        re.search(r"^\s*\S+\.\w+\s*=\s", text, re.M)       # PutField/PutStatic
        or re.search(r"=\s*\S+\.\w+\s*$", text, re.M)      # GetField/GetStatic
    )
    if has_array:
        return "array"
    if has_field:
        return "field"
    return "none"


def survey_one(yml_path):
    inputs = resolve_inputs(yml_path)
    if inputs is None:
        return None
    try:
        r = subprocess.run(
            [AJAVE, "--ir"] + inputs,
            capture_output=True, text=True, timeout=60,
        )
    except Exception:
        return None

    c = Counter()
    for sig, text in split_methods(r.stdout):
        if SKIP_METHOD_RE.search("." + sig):
            continue
        kind = classify_method(text)
        has_ob = "check #" in text
        c[kind] += 1
        if has_ob:
            c[f"{kind}_ob"] += 1
    return yml_path, c


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    tasks = find_all_tasks()

    by_cat = defaultdict(list)
    for t in tasks:
        by_cat[category_of(t)].append(t)

    sample = []
    for cat, ts in by_cat.items():
        sample.extend(ts[:limit])

    print(f"Surveying {len(sample)} benchmarks across {len(by_cat)} categories")
    print("Counting METHODS (excluding enum/clinit boilerplate)\n")

    agg = defaultdict(Counter)
    with ProcessPoolExecutor(max_workers=8) as ex:
        futs = [ex.submit(survey_one, t) for t in sample]
        for fut in as_completed(futs):
            res = fut.result()
            if res is None:
                continue
            path, c = res
            agg[category_of(path)].update(c)

    hdr = (f"{'Category':<40s} {'none':>6s} {'field':>6s} {'array':>6s} "
           f"| {'noneOb':>7s} {'fldOb':>6s} {'arrOb':>6s}")
    print(hdr)
    print("-" * len(hdr))
    tot = Counter()
    for cat in sorted(agg):
        c = agg[cat]
        print(f"{cat:<40s} {c['none']:6d} {c['field']:6d} {c['array']:6d} "
              f"| {c['none_ob']:7d} {c['field_ob']:6d} {c['array_ob']:6d}")
        tot.update(c)
    print("-" * len(hdr))
    print(f"{'TOTAL':<40s} {tot['none']:6d} {tot['field']:6d} {tot['array']:6d} "
          f"| {tot['none_ob']:7d} {tot['field_ob']:6d} {tot['array_ob']:6d}")

    ob = tot['none_ob'] + tot['field_ob'] + tot['array_ob']
    if ob:
        print(f"\nOf {ob} obligation-bearing methods:")
        print(f"  {tot['none_ob']:5d} ({100*tot['none_ob']/ob:4.1f}%) analyzable today")
        print(f"  {tot['field_ob']:5d} ({100*tot['field_ob']/ob:4.1f}%) unlocked by flat field model (phase 1)")
        print(f"  {tot['array_ob']:5d} ({100*tot['array_ob']/ob:4.1f}%) need array theory (phase 2)")


if __name__ == "__main__":
    main()
