#!/usr/bin/env python3
"""Expected-verdict corrections applied to the upstream corpus.

`benchmarks/sv-comp/` is **gitignored** — it is fetched, not tracked. So a
label corrected by hand lives only in a working copy, and a re-clone or a
corpus refresh silently reverts it. That is a score moving for a reason no
record explains, which is the failure mode `CLAUDE.md`'s measurement-discipline
section exists to prevent, so the corrections live here as tracked data and are
re-applied rather than remembered.

    python3 tools/corpus_corrections.py --check    # exit 1 if not applied
    python3 tools/corpus_corrections.py --apply    # idempotent

`--check` distinguishes three states, because they call for different actions:

  applied    the corrected verdict is in place — nothing to do
  missing    the upstream verdict is in place — run --apply
  diverged   neither — upstream changed this task, so the correction's
             justification must be re-verified before it is re-applied

A correction is only legitimate with a **JVM-reproducible witness**: a concrete
input, the exact stub, and an observed non-zero exit. Disagreeing with a label
is not sufficient. Editing an expected verdict is the most direct form of
benchmark overfitting available, so the bar is deliberately higher than for
anything in the engine.
"""
import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BENCH = ROOT / "benchmarks"

# Each entry: the task, the property whose verdict is wrong, what upstream
# says, what it should be, and why -- in a form someone can re-run.
CORRECTIONS = [
    {
        "task": "sv-comp/argv-tasks/ReverseInterpolator_true.yml",
        "property": "valid-assert",
        "upstream": "true",
        "corrected": "false",
        "issue": "gh #72",
        "witness": (
            "Stub Verifier.nondetFloat() to return "
            "Float.intBitsToFloat(1099087158) (~16.38, an ordinary finite "
            "float), compile the task's own sources against it, run with -ea: "
            "exit 1, java.lang.AssertionError. The usual zero-returning stub "
            "exits 0, which is why the mislabel survives casual checking. "
            "ajave reports FALSE and jvm-replay confirms it by executing the "
            "program with that witness."
        ),
        "worth": "-32 becomes +1, a 33-point swing on valid-assert",
    },
]

PROP_FILE = {
    "valid-assert": "valid-assert.prp",
    "no-runtime-exception": "no-runtime-exception.prp",
    "no-data-race": "no-data-race.prp",
    "no-deadlock": "no-deadlock.prp",
}


def verdict_of(text, prop):
    """The declared verdict for one property, or None if not declared.

    A line scanner rather than a YAML dependency, matching `bench.py`: these
    files are generated and uniform, and the tooling must work from a bare
    checkout. Comment lines cannot match, because a `#` line has neither
    marker at the start of its stripped form.
    """
    want = PROP_FILE[prop]
    pending = False
    for line in text.splitlines():
        t = line.strip()
        if t.startswith("#"):
            continue
        if t.startswith("- property_file:") or t.startswith("property_file:"):
            pending = want in t
        elif pending and "expected_verdict:" in t:
            return t.split("expected_verdict:", 1)[1].strip()
    return None


def set_verdict(text, prop, value):
    want = PROP_FILE[prop]
    out, pending = [], False
    for line in text.splitlines(keepends=True):
        t = line.strip()
        if t.startswith("#"):
            out.append(line)
            continue
        if t.startswith("- property_file:") or t.startswith("property_file:"):
            pending = want in t
            out.append(line)
            continue
        if pending and "expected_verdict:" in t:
            out.append(re.sub(r"(expected_verdict:\s*)\S+", r"\g<1>" + value, line))
            pending = False
            continue
        out.append(line)
    return "".join(out)


def classify(c):
    path = BENCH / c["task"]
    if not path.exists():
        return "absent", None
    got = verdict_of(path.read_text(), c["property"])
    if got == c["corrected"]:
        return "applied", got
    if got == c["upstream"]:
        return "missing", got
    return "diverged", got


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true",
                   help="report state; exit 1 unless every correction is applied")
    g.add_argument("--apply", action="store_true", help="apply them (idempotent)")
    args = ap.parse_args()

    bad = 0
    for c in CORRECTIONS:
        state, got = classify(c)
        label = f"{c['task']} [{c['property']}]"
        if state == "applied":
            print(f"  applied   {label}: {c['corrected']} ({c['issue']})")
            continue
        if state == "absent":
            print(f"  ABSENT    {label}: task not found — corpus not fetched?")
            bad += 1
            continue
        if state == "diverged":
            print(f"  DIVERGED  {label}: found {got!r}, upstream was "
                  f"{c['upstream']!r} and we correct to {c['corrected']!r}.")
            print("            Upstream changed this task. Re-verify the witness "
                  "before re-applying:")
            print(f"            {c['witness']}")
            bad += 1
            continue
        # missing
        if args.apply:
            path = BENCH / c["task"]
            path.write_text(set_verdict(path.read_text(), c["property"], c["corrected"]))
            print(f"  APPLIED   {label}: {c['upstream']} -> {c['corrected']} ({c['issue']})")
        else:
            print(f"  MISSING   {label}: upstream {c['upstream']!r} in place; "
                  f"corrected value is {c['corrected']!r} ({c['issue']})")
            print(f"            worth: {c['worth']}")
            print("            run: python3 tools/corpus_corrections.py --apply")
            bad += 1

    if args.check and bad:
        print(f"\n{bad} correction(s) not applied. Scores from this corpus are "
              "not comparable to previously recorded ones.", file=sys.stderr)
        return 1
    if args.check:
        print(f"\nall {len(CORRECTIONS)} correction(s) applied. Note that our "
              "valid-assert score is +33 against stock sv-benchmarks; subtract "
              "it before any external comparison.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
