#!/usr/bin/env python3
"""Static contract checks for the seams between engines.

Workstream E of docs/plans/codebase-health.md. These run in CI's toolchain-free
`quick` job, alongside check-boundaries.sh and check-strategy-docs.sh, and take
about a second.

They exist because one session (2026-10-26) surfaced roughly eight instances of
a single shape: a mechanism that exists, is correct, and is never reached. An
engine that could not run; an escalation pass that retired before its input
existed; an interest declared for an artifact kind nobody produces, while
omitting the kind it needed; four flags dead by their own measured criteria;
and two tests that passed because their premise was unsatisfiable.

That is the failure mode of a portfolio where everything communicates
indirectly through a blackboard. Reviewing harder does not scale against it —
it recurred twice in the same session that documented it. These checks attack
the rate rather than the instances.

EACH CHECK IS DEMONSTRATED AGAINST ITS MOTIVATING BUG. See `demonstrations` at
the bottom: reverting the named fix must make the named check fail. A check
that does not catch what it was written for is itself an instance of the class
it detects.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CRATES = ROOT / "crates"


def rust_files(skip_tests=True):
    """Every .rs file, with `#[cfg(test)]` modules stripped when asked.

    Test code constructs artifacts and calls engines freely; counting it as a
    producer or consumer would make every check pass vacuously, which is the
    exact defect these checks exist to find.
    """
    for p in sorted(CRATES.glob("*/src/**/*.rs")):
        text = p.read_text()
        if skip_tests:
            text = strip_test_modules(text)
        yield p, text


def strip_test_modules(text):
    out, i = [], 0
    for m in re.finditer(r"#\[cfg\(test\)\]\s*mod \w+ \{", text):
        if m.start() < i:
            continue
        out.append(text[i : m.start()])
        depth, j = 0, m.end() - 1
        for j in range(m.end() - 1, len(text)):
            if text[j] == "{":
                depth += 1
            elif text[j] == "}":
                depth -= 1
                if depth == 0:
                    break
        i = j + 1
    out.append(text[i:])
    return "".join(out)


def rel(p):
    return str(p.relative_to(ROOT))


# ── E1 ──────────────────────────────────────────────────────────────────────
def e1_interest_has_producer():
    """Every `Interest` bit an engine declares must name a kind something produces.

    A bit naming a kind nobody publishes is a dependency on a message nobody
    sends: the engine declares it will wake for something that cannot arrive.
    """
    failures = []

    # Interest bit <- artifact variant, read from artifact.rs's own match.
    artifact_rs = (CRATES / "ajave-core/src/artifact.rs").read_text()
    bit_of_variant = dict(
        re.findall(r"Artifact::(\w+)\([^)]*\)\s*=>\s*Interest::(\w+)", artifact_rs)
    )
    if not bit_of_variant:
        failures.append(
            "E1: could not parse the Artifact -> Interest mapping from "
            "artifact.rs. The check is inert until this is fixed."
        )
        return failures

    produced_bits = set()
    for p, text in rust_files():
        if p.name == "artifact.rs":
            continue  # the enum's own definition is not a producer
        for variant, bit in bit_of_variant.items():
            if re.search(r"Artifact::" + variant + r"\s*[({]", text):
                produced_bits.add(bit)

    # ANY/NOTHING are compositions, not kinds; they need no single producer.
    composite = {"ANY", "NOTHING"}

    for p, text in rust_files():
        if p.name == "artifact.rs":
            continue  # `Artifact::interest()` is the mapping, not a declaration
        for m in re.finditer(r"fn interest\(&self\) -> Interest \{", text):
            depth, j = 0, m.end() - 1
            for j in range(m.end() - 1, len(text)):
                if text[j] == "{":
                    depth += 1
                elif text[j] == "}":
                    depth -= 1
                    if depth == 0:
                        break
            body = text[m.end() : j]
            body = re.sub(r"//[^\n]*", "", body)  # declarations, not prose
            for bit in set(re.findall(r"Interest::(\w+)", body)):
                if bit in composite or bit in produced_bits:
                    continue
                failures.append(
                    f"E1: {rel(p)} declares Interest::{bit}, which no engine "
                    f"produces. Either publish that kind or stop waiting for it."
                )
    return failures


# ── E4 ──────────────────────────────────────────────────────────────────────
def e4_defaulted_methods_are_varied():
    """A defaulted trait method no implementor overrides is not a configuration point.

    It is a decision wearing a parameter's clothes, and its doc comment is
    unverified by construction — `Cpa::prec` was documented as "the hook CEGAR
    lives in" while CEGAR refined from outside it.
    """
    failures = []
    files = list(rust_files())
    for p, text in files:
        for tm in re.finditer(r"^(?:pub )?trait (\w+)[^{\n]*\{", text, re.M):
            name = tm.group(1)
            depth, j = 0, tm.end() - 1
            for j in range(tm.end() - 1, len(text)):
                if text[j] == "{":
                    depth += 1
                elif text[j] == "}":
                    depth -= 1
                    if depth == 0:
                        break
            body = text[tm.end() - 1 : j]
            for fm in re.finditer(r"\n    fn (\w+)\s*\([^;{]*\)?[^;{]*?([;{])", body):
                meth, term = fm.group(1), fm.group(2)
                if term != "{":
                    continue  # required, not defaulted
                overrides = 0
                for p2, t2 in files:
                    for im in re.finditer(
                        r"impl(?:<[^>]*>)?\s+(?:\w+::)*" + name + r"(?:<[^>]*>)?\s+for\s",
                        t2,
                    ):
                        k = t2.find("{", im.end())
                        if k < 0:
                            continue
                        d2, q = 0, k
                        for q in range(k, len(t2)):
                            if t2[q] == "{":
                                d2 += 1
                            elif t2[q] == "}":
                                d2 -= 1
                                if d2 == 0:
                                    break
                        if re.search(r"\bfn " + meth + r"\b", t2[k:q]):
                            overrides += 1
                if overrides == 0:
                    failures.append(
                        f"E4: {name}::{meth} has a default body and is "
                        f"overridden by nothing ({rel(p)}). Delete it, or "
                        f"document it as fixed rather than configurable."
                    )
    return failures


# ── E5 ──────────────────────────────────────────────────────────────────────
def e5_domains_check_their_laws():
    """Implementing `Lattice` is not the same as satisfying it.

    `fixpoint::laws` ships `check_lattice_laws` and `check_merge_policy` as
    library functions precisely so a domain added later inherits the contract.
    Nothing forces a new one to call them, so this does.
    """
    failures = []
    for p, text in rust_files(skip_tests=False):
        if not re.search(r"impl\s+(?:\w+::)*AbstractDomain\s+for\s+(\w+)", text):
            continue
        if "check_lattice_laws" not in text:
            who = re.findall(r"impl\s+(?:\w+::)*AbstractDomain\s+for\s+(\w+)", text)
            failures.append(
                f"E5: {rel(p)} implements AbstractDomain for {', '.join(who)} "
                f"but never calls laws::check_lattice_laws. The laws are in "
                f"ajave_core::fixpoint::laws; call them from this file's tests."
            )
    return failures


CHECKS = [
    ("E1 every declared Interest has a producer", e1_interest_has_producer),
    ("E4 every defaulted trait method is varied", e4_defaulted_methods_are_varied),
    ("E5 every abstract domain checks its laws", e5_domains_check_their_laws),
]


def main():
    failed = 0
    for label, fn in CHECKS:
        problems = fn()
        if problems:
            failed += 1
            print(f"FAIL  {label}")
            for p in problems:
                print(f"        {p}")
        else:
            print(f"ok    {label}")
    if failed:
        print(f"\n{failed} contract check(s) failed.")
        return 1
    print("\nall contract checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())

# ── Demonstrations ──────────────────────────────────────────────────────────
#
# Run on 2026-10-26 against commit 9dd728a. Reverting each fix must make the
# named check fail; if it does not, the check is inert and must be fixed before
# it is trusted.
#
# E1  Reintroduced #37 by changing `smt_bmc/mod.rs:613` back to
#       let base = Interest::LEMMA.union(Interest::PRECISION);
#     ->  FAIL  E1: smt_bmc/mod.rs declares Interest::PRECISION, which no
#               engine produces.
#
#     Note: the first attempt at this demonstration *passed*, because the sed
#     pattern no longer matched the (since-refactored) line and the bug was
#     never actually reintroduced. The check was fine; the demonstration was
#     vacuous. Which is the whole argument for requiring demonstrations — and
#     for reading their output rather than their exit code.
#
# E4  Reintroduced `Cpa::prec` as a defaulted method on `AbstractDomain`.
#     ->  FAIL  E4: AbstractDomain::prec has a default body and is overridden
#               by nothing.
#
# E5  Removed the `laws::check_lattice_laws(&samples())` call from
#     `interval.rs`'s test module.
#     ->  FAIL  E5: interval.rs implements AbstractDomain for IntervalCpa but
#               never calls laws::check_lattice_laws.
#
# Two bugs were also found in E1 itself on its first run, both of which made it
# report false positives rather than miss real ones: the Artifact -> Interest
# regex only matched `(..)` match arms and so missed `(_)` ones, and
# `artifact.rs`'s own `Artifact::interest()` mapping function was scanned as
# though it were an engine declaring an interest.
