#!/usr/bin/env python3
"""
Runs roast against tracked tasks (tasks/verdicts.txt) and detects regressions.

Regression = any change that makes results worse:
  - a previously-correct verdict (TRUE/FALSE matching expected) becomes UNKNOWN or wrong
  - a previously-UNKNOWN verdict becomes the wrong answer (new soundness bug)

Improvements (UNKNOWN -> correct expected verdict) are reported and, with
--update, written back to verdicts.txt.

Exit code: 0 if no regressions, 1 otherwise.
"""
import argparse
import os
import subprocess
import sys

VERDICTS_FILE = "tasks/verdicts.txt"
ROAST_CANDIDATES = ["./target/release/ajave", "./target/debug/roast"]


def find_roast():
    override = os.environ.get("ROAST")
    if override:
        return override
    for candidate in ROAST_CANDIDATES:
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


def resolve_inputs(yml_path):
    import yaml
    task_dir = os.path.dirname(yml_path)
    with open(yml_path) as f:
        d = yaml.safe_load(f)
    paths = []
    for rel in d.get("input_files", []):
        abs_p = os.path.normpath(os.path.join(task_dir, rel))
        if os.path.exists(abs_p):
            paths.append(abs_p)
    return paths


def run_roast(roast, inputs, timeout=30):
    try:
        r = subprocess.run(
            [roast] + inputs,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        lines = [l.strip() for l in r.stdout.strip().splitlines() if l.strip()]
        return lines[-1] if lines else "TIMEOUT"
    except subprocess.TimeoutExpired:
        return "TIMEOUT"


def parse_verdicts(path):
    """Returns list of (snapped, expected, yml) and the raw header lines."""
    entries = []
    header = []
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("#") or line.strip() == "":
                header.append(line)
                continue
            parts = line.split()
            if len(parts) >= 3:
                snapped, expected, yml = parts[0], parts[1], parts[2]
                entries.append((snapped, expected, yml))
    return header, entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true",
                        help="Overwrite verdicts.txt with current results")
    args = parser.parse_args()

    os.chdir(os.path.dirname(os.path.abspath(__file__)) + "/..")

    roast = find_roast()
    if not roast:
        print("roast binary not found; run 'cargo build' first", file=sys.stderr)
        sys.exit(1)

    header, entries = parse_verdicts(VERDICTS_FILE)

    total = ok = improved = regressed = wrong_new = 0
    regressions = []
    improvements = []
    new_entries = []

    for snapped, expected, yml in entries:
        inputs = resolve_inputs(yml)
        if not inputs:
            print(f"SKIP (no inputs resolved): {yml}")
            new_entries.append((snapped, expected, yml))
            continue

        verdict = run_roast(roast, inputs)
        total += 1

        snapped_correct = snapped.lower() == expected
        verdict_correct = verdict.lower() == expected

        if verdict == snapped:
            ok += 1
            new_entries.append((snapped, expected, yml))
        elif snapped_correct and not verdict_correct:
            # Was right, now worse.
            regressed += 1
            regressions.append(
                f"  REGRESSION  was={snapped} now={verdict} expected={expected}  {yml}"
            )
            new_entries.append((snapped, expected, yml))  # keep old on regression
        elif not snapped_correct and not verdict_correct and verdict not in ("UNKNOWN", "TIMEOUT"):
            # Was UNKNOWN/timeout, now actively wrong.
            wrong_new += 1
            regressions.append(
                f"  WRONG       was={snapped} now={verdict} expected={expected}  {yml}"
            )
            new_entries.append((verdict, expected, yml))
        else:
            # Improvement or neutral change.
            improved += 1
            improvements.append(
                f"  IMPROVED    was={snapped} now={verdict} expected={expected}  {yml}"
            )
            new_entries.append((verdict, expected, yml))

    print(f"corpus: {total} tasks — {ok} unchanged, {improved} improved, "
          f"{regressed} regressed, {wrong_new} new wrong")

    if improvements:
        print("\nIMPROVEMENTS:")
        for line in improvements:
            print(line)

    if regressions:
        print("\nREGRESSIONS:")
        for line in regressions:
            print(line)

    if args.update:
        with open(VERDICTS_FILE, "w") as f:
            for h in header:
                f.write(h + "\n")
            for snapped, expected, yml in new_entries:
                f.write(f"{snapped:<8}{expected:<8}{yml}\n")
        print("verdicts.txt updated")

    if regressed > 0 or wrong_new > 0:
        if not args.update:
            sys.exit(1)

    if regressed == 0 and wrong_new == 0:
        print("no regressions")


if __name__ == "__main__":
    main()
