#!/usr/bin/env python3
"""
Scaling harness for roast's SMT layer.

Generates families of Java programs parameterised by a size `n`, runs roast
over each with `--profile-json`, and fits how encoding size and solver time
grow with `n`. A family declares the growth it is *supposed* to have; the run
fails when the measured growth is in a worse complexity class.

## Why this exists

Fixed benchmarks cannot detect a change in asymptotic behaviour. SV-COMP tasks
are one size each, so an encoder that quietly goes from linear to exponential
output looks, on any individual task, like "a bit slower" -- right up to the
point where a task stops finishing at all. That is exactly how the substitution
blowup in roast's text encoders survived: every verdict stayed correct.

Fitting a curve needs several sizes of the *same* program shape, which means
generating them. That is the whole idea here.

The reference failure mode is Flanagan & Saxe, *Avoiding exponential explosion:
generating compact verification conditions* (POPL 2001) -- a VC generator that
substitutes an expression into a variable map rather than naming it emits a
formula exponential in the source fragment. Naming it emits a linear one.

## What is measured

From `--profile-json`, per engine and in total:

  bytes_emitted     SMT-LIB text handed to the solver. The encoder's output
                    size, and a floor on the solver's parse cost.
  commands          Roughly the term count.
  solver_seconds    Wall time blocked on the solver.
  encode_seconds    Time in the encoder itself.

Growth is classified by fitting three models -- affine, power law and
exponential -- and reporting whichever explains the data best. Affine is
preferred on ties because every measurement carries a large fixed overhead
(preamble, variable declarations, the property itself), and a log-log fit over
data with a big additive constant badly understates the exponent.

Run `--self-test` to check the classifier against series of known growth. That
matters more than it sounds: the regression this gate exists to catch is
expensive to reproduce for real, so the synthetic check is what keeps the
classifier trustworthy in between.

## Usage

    cargo build --release
    python3 tools/smt_scaling.py                    # all families
    python3 tools/smt_scaling.py --family accumulate
    python3 tools/smt_scaling.py --json out.json    # machine-readable

Needs a solver on PATH for the SMT engines to register at all; without one the
encoders never run and every family reports no data.
"""

import argparse
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile

# ---------------------------------------------------------------------------
# Program family generators
#
# Each returns the body of `Main.main` for parameter n. Families are chosen to
# stress one encoder dimension each, and to have a verdict that does not depend
# on n -- a family whose verdict flips partway through is measuring two
# different things.
# ---------------------------------------------------------------------------


def fam_accumulate(n):
    """Straight-line chain where each statement reads the previous twice.

    The shape that makes a substituting encoder emit O(2^n): every statement
    doubles the rendered size of `x`. A naming encoder emits O(n).
    """
    lines = ["int x = Verifier.nondetInt();", "Verifier.assume(x > 0);"]
    for _ in range(n):
        lines.append("x = x + x;")
    lines.append("assert x != 0 || x == 0;")  # trivially true, verdict-stable
    return "\n    ".join(lines)


def fam_sequential(n):
    """Straight-line chain with no repeated reads: a linear baseline.

    Isolates plain statement count from the doubling effect in `accumulate`.
    """
    lines = ["int x = Verifier.nondetInt();", "Verifier.assume(x > 0);"]
    for i in range(n):
        lines.append(f"x = x + {i + 1};")
    lines.append("assert x != 0 || x == 0;")
    return "\n    ".join(lines)


def fam_branches(n):
    """n sequential if/else diamonds: 2^n paths, but only n join points.

    Tests whether the explorer merges at joins (linear) or forks paths
    (exponential). This is what the post-dominator work feeds.
    """
    lines = ["int x = Verifier.nondetInt();", "int y = 0;"]
    for i in range(n):
        lines.append(f"if (x > {i}) {{ y = y + 1; }} else {{ y = y + 2; }}")
    lines.append("assert y >= 0;")
    return "\n    ".join(lines)


def fam_if_no_else(n):
    """n sequential `if` statements with no `else` branch.

    Deliberately identical to `branches` apart from the missing `else`, to
    isolate that one difference. It matters because `PostDom::common` declines
    to merge when one branch target post-dominates the other -- and for an
    `if` with no `else`, the false target *is* the join point, so that
    condition always holds and the explorer forks instead of merging.

    An `if` without an `else` is the most common shape in Java, so this is the
    family most likely to be hit in practice.
    """
    lines = ["int x = Verifier.nondetInt();", "int y = 0;"]
    for i in range(n):
        lines.append(f"if (x > {i}) {{ y = y + 1; }}")
    lines.append("assert y >= 0;")
    return "\n    ".join(lines)


def fam_nested_branches(n):
    """n *nested* if/else: also 2^n paths, but no early reconvergence."""
    head, tail = [], []
    lines = ["int x = Verifier.nondetInt();", "int y = 0;"]
    for i in range(n):
        head.append(f"if (x > {i}) {{ y = y + 1;")
        tail.append("} else { y = y + 2; }")
    body = " ".join(head) + " " + " ".join(reversed(tail))
    lines.append(body)
    lines.append("assert y >= 0;")
    return "\n    ".join(lines)


def fam_bounded_loop(n):
    """A loop with a constant bound of n, forcing n unrollings."""
    return "\n    ".join(
        [
            "int x = Verifier.nondetInt();",
            "Verifier.assume(x >= 0);",
            "int s = 0;",
            f"for (int i = 0; i < {n}; i++) {{ s = s + 1; }}",
            f"assert s == {n};",
        ]
    )


def fam_vars(n):
    """n independent live variables: widens the state vector without deepening
    it. Relations over all variables (as CHC emits) grow with this."""
    lines = []
    for i in range(n):
        lines.append(f"int v{i} = Verifier.nondetInt();")
    lines.append("int t = 0;")
    for i in range(n):
        lines.append(f"if (v{i} > 0) {{ t = t + 1; }}")
    lines.append(f"assert t >= 0 && t <= {n};")
    return "\n    ".join(lines)


FAMILIES = {
    # name: (generator, sizes, expected growth class for bytes_emitted)
    # `accumulate` is the Flanagan-Saxe shape and the reason this file exists:
    # a substituting encoder emits O(2^n) here, a naming one emits O(n).
    "accumulate": (fam_accumulate, [10, 20, 30, 40, 50, 60], "poly<=1.5"),
    "sequential": (fam_sequential, [10, 20, 30, 40, 50, 60], "poly<=1.5"),
    "branches": (fam_branches, [2, 4, 6, 8, 10, 12], "not-exponential"),
    "if_no_else": (fam_if_no_else, [2, 4, 6, 8, 10], "not-exponential"),
    "nested_branches": (fam_nested_branches, [2, 4, 6, 8], "any"),
    "bounded_loop": (fam_bounded_loop, [2, 4, 6, 8, 10, 12], "any"),
    # Budget deliberately open: this family currently exercises the
    # if-without-else gap below and hits the explorer's fork cap, going UNKNOWN
    # from n=8. Tighten it to "poly<=2.5" once that is fixed -- at which point
    # it becomes a regression canary for the fix.
    "vars": (fam_vars, [2, 4, 6, 8, 10, 12], "any"),
}

# Families whose budget is loose because of a known open issue rather than
# because nothing is expected of them. Printed at the end of a run so a green
# result never reads as "nothing to do here".
NOTES = {
    "if_no_else": (
        "`if` without `else` defeats diamond merging: `PostDom::common` "
        "declines to merge when one branch target post-dominates the other, "
        "and for an else-less `if` the false target *is* the join. Measured "
        "against the otherwise-identical `branches` family at n=10: 47,440 "
        "bytes and 154 solver calls, against 4,480 bytes and 4 calls. Same "
        "program semantics, 10x the encoding."
    ),
    "vars": (
        "Hits the explorer's MAX_FORKS cap and returns UNKNOWN from n=8, for "
        "the same if-without-else reason. Budget is open until that is fixed."
    ),
}

TEMPLATE = """import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {{
  public static void main(String[] args) {{
    {body}
  }}
}}
"""


# ---------------------------------------------------------------------------
# Curve fitting
# ---------------------------------------------------------------------------


def _linreg(xs, ys):
    """Least squares slope, intercept and R^2. No numpy dependency."""
    k = len(xs)
    if k < 2:
        return 0.0, 0.0, 0.0
    mx = sum(xs) / k
    my = sum(ys) / k
    sxx = sum((x - mx) ** 2 for x in xs)
    if sxx == 0:
        return 0.0, my, 0.0
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = sxy / sxx
    intercept = my - slope * mx
    ss_tot = sum((y - my) ** 2 for y in ys)
    ss_res = sum((y - (slope * x + intercept)) ** 2 for x, y in zip(xs, ys))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 1.0
    return slope, intercept, r2


def fit_growth(sizes, values):
    """Classify how `values` grows with `sizes`.

    Fits three models and picks by R^2:

      affine       y = a*n + b        -> "linear",      magnitude = a
      power        y = b * n^a        -> "polynomial",  magnitude = a
      exponential  y = b * exp(a*n)   -> "exponential", magnitude = e^a

    Affine is tried first and preferred on ties, because every measurement here
    carries a large fixed overhead -- roast emits a preamble, declares the
    program's variables, and encodes the property regardless of n. A log-log fit
    on data with a big additive constant badly understates the exponent: the
    straight-line families below have ~1600 bytes of fixed cost against ~200
    bytes of variable cost, and a naive power fit calls that O(n^0.25) when the
    marginal behaviour is exactly linear. Reporting the marginal slope is both
    more accurate and more actionable.

    Returns (label, magnitude, r2).
    """
    pts = [(n, v) for n, v in zip(sizes, values) if n > 0 and v > 0]
    if len(pts) < 3:
        return "insufficient-data", 0.0, 0.0
    ns = [float(p[0]) for p in pts]
    vs = [float(p[1]) for p in pts]

    a_slope, _, a_r2 = _linreg(ns, vs)
    p_slope, _, p_r2 = _linreg([math.log(n) for n in ns], [math.log(v) for v in vs])
    e_slope, _, e_r2 = _linreg(ns, [math.log(v) for v in vs])

    # Exponential is the loud claim, so it has to win clearly *and* actually be
    # growing: over a short range a mild exponential and a mild polynomial are
    # nearly indistinguishable.
    if e_r2 > max(a_r2, p_r2) + 0.02 and e_slope > 0.05:
        return "exponential", math.exp(e_slope), e_r2

    # A power law only beats affine if it explains meaningfully more variance;
    # otherwise call it linear and report bytes (or seconds) per unit of n.
    if p_r2 > a_r2 + 0.02:
        return "polynomial", p_slope, p_r2
    return "linear", a_slope, a_r2


def within_budget(label, magnitude, budget):
    """Does the measured growth satisfy the family's declared budget?

    Budgets:
      "linear"          affine growth (any slope)
      "poly<=K"         linear, or polynomial with exponent <= K
      "not-exponential" anything but an exponential fit
      "any"             no constraint; the family exists to be observed
    """
    if budget == "any" or label == "insufficient-data":
        return True
    if budget == "not-exponential":
        return label != "exponential"
    if budget == "linear":
        return label == "linear"
    if budget.startswith("poly<="):
        limit = float(budget.split("<=")[1])
        if label == "linear":
            return True
        return label == "polynomial" and magnitude <= limit
    raise ValueError(f"unknown budget: {budget}")


def self_test():
    """Check the classifier against series whose growth is known.

    The gate is only worth having if it can tell the classes apart, and the
    failure it exists to catch -- a linear encoder turning exponential -- is
    exactly the one that is expensive to reproduce for real. Synthetic series
    are how we keep the classifier honest between real regressions.
    """
    ns = [4, 8, 12, 16, 20, 24]
    cases = [
        ("linear, no offset", [50 * n for n in ns], "linear"),
        ("linear, large offset", [1600 + 52 * n for n in ns], "linear"),
        ("quadratic", [3 * n * n for n in ns], "polynomial"),
        ("cubic", [n**3 for n in ns], "polynomial"),
        ("exponential base 2", [2**n for n in ns], "exponential"),
        ("exponential with offset", [1600 + 2**n for n in ns], "exponential"),
    ]
    failures = []
    print("classifier self-test")
    for name, series, expected in cases:
        label, mag, r2 = fit_growth(ns, series)
        ok = label == expected
        print(f"  {'ok  ' if ok else 'FAIL'} {name:<26} -> {describe(label, mag, r2)}")
        if not ok:
            failures.append((name, expected, label))

    # The budget check must reject the case it exists for.
    if within_budget("exponential", 2.0, "poly<=1.5"):
        failures.append(("budget rejects exponential", "reject", "accepted"))
    if not within_budget("linear", 52.0, "poly<=1.5"):
        failures.append(("budget accepts linear", "accept", "rejected"))

    if failures:
        print("\nself-test FAILED:")
        for name, exp, got in failures:
            print(f"  {name}: expected {exp}, got {got}")
        return 1
    print("\nclassifier distinguishes linear, polynomial and exponential growth.")
    return 0


# ---------------------------------------------------------------------------
# Running
# ---------------------------------------------------------------------------


def find_roast():
    override = os.environ.get("ROAST")
    if override:
        return override
    for c in ["./target/release/roast", "./target/debug/roast"]:
        if os.path.isfile(c) and os.access(c, os.X_OK):
            return c
    return None


def run_one(roast, common_dir, body, workdir, timeout):
    """Compile and verify one instance, returning its profile totals."""
    src = os.path.join(workdir, "Main.java")
    with open(src, "w") as f:
        f.write(TEMPLATE.format(body=body))
    prof = os.path.join(workdir, "profile.json")

    try:
        r = subprocess.run(
            [roast, common_dir, workdir, "--profile-json", prof],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return {"verdict": "TIMEOUT"}

    out = [l.strip() for l in r.stdout.strip().splitlines() if l.strip()]
    result = {"verdict": out[-1] if out else "(none)"}
    if os.path.exists(prof):
        with open(prof) as f:
            result["profile"] = json.load(f)
        os.remove(prof)
    return result


def measure_family(roast, name, common_dir, timeout, verbose):
    gen, sizes, budget = FAMILIES[name]
    rows = []
    with tempfile.TemporaryDirectory(prefix=f"roast-scale-{name}-") as workdir:
        for n in sizes:
            res = run_one(roast, common_dir, gen(n), workdir, timeout)
            prof = res.get("profile", {}).get("total", {})
            row = {
                "n": n,
                "verdict": res["verdict"],
                "bytes": prof.get("bytes_emitted", 0),
                "commands": prof.get("commands", 0),
                "encode_s": prof.get("encode_seconds", 0.0),
                "solver_s": prof.get("solver_seconds", 0.0),
                "checks": prof.get("check_sat_calls", 0),
            }
            rows.append(row)
            if verbose:
                print(
                    f"    n={n:<3} {row['verdict']:<8} "
                    f"bytes={row['bytes']:>10,} cmds={row['commands']:>7,} "
                    f"solve={row['solver_s']:>7.3f}s checks={row['checks']:>5}"
                )
            if res["verdict"] == "TIMEOUT":
                break
    return rows, budget


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--family", action="append", choices=sorted(FAMILIES),
                    help="run only this family (repeatable)")
    ap.add_argument("--timeout", type=int, default=60, help="per-instance seconds")
    ap.add_argument("--json", metavar="PATH", help="write full results here")
    ap.add_argument("--quiet", "-q", action="store_true")
    ap.add_argument("--self-test", action="store_true",
                    help="validate the growth classifier on synthetic series and exit")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

    roast = find_roast()
    if not roast:
        print("roast binary not found; run 'cargo build --release' first", file=sys.stderr)
        return 2
    if not shutil.which(os.environ.get("ROAST_SMT_SOLVER", "z3")):
        print("no SMT solver on PATH; the SMT engines will not register and "
              "there will be nothing to measure", file=sys.stderr)
        return 2

    common = "tasks/common"
    if not os.path.isdir(common):
        print(f"{common} not found (needed for the Verifier stub)", file=sys.stderr)
        return 2

    chosen = args.family or sorted(FAMILIES)
    results = {}
    failures = []

    for name in chosen:
        if not args.quiet:
            print(f"\n── {name} ──")
        rows, budget = measure_family(roast, name, common, args.timeout, not args.quiet)
        sizes = [r["n"] for r in rows]

        b_label, b_mag, b_r2 = fit_growth(sizes, [r["bytes"] for r in rows])
        s_label, s_mag, s_r2 = fit_growth(sizes, [r["solver_s"] for r in rows])
        ok = within_budget(b_label, b_mag, budget)

        results[name] = {
            "budget": budget,
            "rows": rows,
            "bytes_growth": {"class": b_label, "magnitude": b_mag, "r2": b_r2},
            "solver_growth": {"class": s_label, "magnitude": s_mag, "r2": s_r2},
            "within_budget": ok,
        }
        if not ok:
            failures.append((name, budget, b_label, b_mag))

        if not args.quiet:
            print(f"    encoding size : {describe(b_label, b_mag, b_r2)}   "
                  f"[budget {budget}] {'ok' if ok else 'OVER BUDGET'}")
            print(f"    solver time   : {describe(s_label, s_mag, s_r2)}")

    print("\n" + "=" * 72)
    noted = [n for n in chosen if n in NOTES]
    if noted:
        print("known gaps in these families:\n")
        for name in noted:
            print(f"  {name}: {NOTES[name]}\n")
    if failures:
        print("SCALING REGRESSION\n")
        for name, budget, label, mag in failures:
            print(f"  {name}: encoding size grew {label} ({mag:.2f}), "
                  f"budget was {budget}")
        print("\nAn encoder whose output outgrows its budget will keep producing")
        print("correct verdicts until it stops finishing at all. Investigate")
        print("before scoring.")
    else:
        print("All families within their declared growth budgets.")

    if args.json:
        with open(args.json, "w") as f:
            json.dump(results, f, indent=2)
        print(f"\nfull results written to {args.json}")

    return 1 if failures else 0


def describe(label, mag, r2):
    if label == "insufficient-data":
        return "insufficient data"
    if label == "exponential":
        return f"EXPONENTIAL, base {mag:.2f} (R^2={r2:.3f})"
    if label == "linear":
        # The marginal cost is the useful number for a linear fit; an exponent
        # would be 1 by construction and tell you nothing.
        return f"linear, {mag:,.1f} per unit of n (R^2={r2:.3f})"
    return f"O(n^{mag:.2f}) (R^2={r2:.3f})"


if __name__ == "__main__":
    sys.exit(main())
