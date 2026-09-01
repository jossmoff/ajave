"""Metamorphic test: making a library contract more conservative must not flip a verdict.

Contracts form a refinement order (`Contract::at_least_as_conservative_as`).
Moving *up* it -- claiming more preconditions, a wider effect -- can only cost
precision, so every consumer of `contract_of` is supposed to be monotone: a
TRUE may become UNKNOWN, and nothing else may change.

That property is what makes the order worth having, and it is not checkable by
reading the table. This perturbs one contract at a time to the most conservative
one and looks for a verdict that changed to a *different verdict* rather than to
UNKNOWN. A flip means some consumer is not monotone -- the defect class behind
#48, where 22 wrongly-allowlisted methods accumulated because being wrong in the
expensive direction looked exactly like being wrong in the cheap one.

Usage:  python3 tools/contract_monotonicity.py [tasks] [signatures]
"""
import os
import sys
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, "tools")
import bench
from procguard import run_guarded

BIN = "./target/release/ajave"

# Signatures the smoke set actually consults, measured with
# AJAVE_REPORT_UNCONTRACTED rather than guessed. That distinction is the whole
# reason this list exists: the first version was chosen by plausibility --
# String.length, StringBuilder.append -- and every one of them was inert,
# because those are answered by the string encoder and never reach a contract.
# A metamorphic test over signatures nothing consults proves nothing.
SIGNATURES = [
    "java/lang/Math:pow", "java/lang/Math:abs", "java/lang/Math:floor",
    "java/lang/Double:isNaN", "java/lang/Integer:compare",
    "java/lang/Character:isDigit",
]


def run(task, prop, env_extra=None):
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)
    cmd = [BIN, "--property", bench.CLI_PROPERTY[prop]] + task["inputs"]
    r = run_guarded(cmd, timeout=60, env=env)
    if r.timed_out or r.returncode < 0:
        return None
    return (r.stdout.strip().splitlines() or ["?"])[-1].strip()


def main():
    ntasks = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    sigs = SIGNATURES[: int(sys.argv[2])] if len(sys.argv) > 2 else SIGNATURES

    # The `contracts` set, not `smoke`: every task there rests its verdict on
    # exactly one library contract, so a perturbation is guaranteed to bite.
    # Sampling ordinary benchmarks was tried first and every perturbation came
    # out inert -- their verdicts rarely depend on any single contract, so the
    # test passed while proving nothing.
    tasks = [(t, prop) for t, prop in bench.load_set("contracts")][:ntasks]

    print(f"  baseline over {len(tasks)} task(s)")
    with ThreadPoolExecutor(max_workers=5) as ex:
        base = list(ex.map(lambda tp: run(tp[0], tp[1]), tasks))

    flips, weakened = [], 0
    # A perturbation that changes nothing has tested nothing. Counting them is
    # what stops a vacuous run reporting success -- the signature may simply be
    # unused by these tasks, or handled somewhere that never consults
    # `contract_of` at all, which is the bypass problem #67 names.
    ineffective = []
    for sig in sigs:
        with ThreadPoolExecutor(max_workers=5) as ex:
            got = list(ex.map(
                lambda tp: run(tp[0], tp[1], {"AJAVE_PERTURB_CONTRACT": sig}), tasks))
        moved = 0
        for (t, prop), b, g in zip(tasks, base, got):
            if b is None or g is None or b == g:
                continue
            moved += 1
            name = os.path.relpath(t["yml"], "benchmarks")
            # Losing precision is the permitted direction.
            if g == "UNKNOWN" and b in ("TRUE", "FALSE"):
                weakened += 1
            else:
                flips.append((sig, name, prop, b, g))
        if moved == 0:
            ineffective.append(sig)

    print(f"  perturbed {len(sigs)} signature(s)")
    print(f"  verdicts weakened to UNKNOWN (allowed): {weakened}")
    if ineffective:
        print(f"  {len(ineffective)}/{len(sigs)} signature(s) changed NOTHING, so tested nothing:")
        for sig in ineffective:
            print(f"    {sig}")
        print("  Either unused by these tasks, or answered without consulting")
        print("  contract_of -- the bypasses #67 asks to close.")
    if not flips and len(ineffective) == len(sigs):
        print("\n  VACUOUS: every perturbation was inert. This run proves nothing.")
        return 2
    if flips:
        print(f"\n  {len(flips)} MONOTONICITY VIOLATION(S) — a more conservative")
        print("  contract changed a verdict rather than weakening it:")
        for sig, name, prop, b, g in flips[:20]:
            print(f"    {sig:34s} {name} [{prop}]: {b} -> {g}")
        return 1
    print("  no monotonicity violations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
