# IMC (interpolation-based model checking)

**Direction:** Over
**Tier:** 3
**Status:** working
**Source:** `roast-engines/src/imc.rs`

## What it proves or finds

Turns a bounded "no bug within `k` steps" result into an unbounded proof,
without needing the property to be `k`-inductive the way
`docs/strategies/kinduction.md` does.

The loop, after McMillan (CAV 2003): unroll to depth `k` and check. On UNSAT,
cut the refutation proof one step from the initial states and extract a Craig
interpolant `I` — by construction an over-approximation of the states
reachable in one step that still cannot reach the error. Accumulate
`F ← F ∨ I` and repeat from `F` instead of from the initial states. When a
freshly computed interpolant is already implied by `F`, `F` is an inductive
invariant strong enough to exclude the error, and every obligation in the
body is discharged. Capped at `MAX_ITERATIONS = 50`.

The body is encoded as linear integer arithmetic by
`interpolation::encode_body_lia`.

## What it assumes / where it's unsound if the assumption breaks

Two assumptions, in order of how much they cost if wrong:

1. **The havoc guard.** As with every proving engine, the LIA encoding models
   integer arithmetic and nothing else, so bodies containing field access,
   `instanceof`, unresolved calls or explicit `Havoc` are skipped via
   `body_uses_havoced_ops`. Without it, UNSAT over an encoding that ignored
   the heap would read as a proof.
2. **LIA rather than bitvectors.** Unlike CHC, this encoding uses mathematical
   integers, so Java's wraparound on overflow is not modelled. A program whose
   only bug requires an `int` to overflow is provable-safe under this encoding
   and is not safe in fact. The interpolation solver interface is the reason
   (interpolation support is far better developed for LIA than for
   bitvectors), but it is a real gap rather than a conservative
   approximation — treat any TRUE from this engine on overflow-sensitive
   arithmetic with suspicion.

## Known incompleteness

- Bodies with heap operations, unresolved calls or floating point.
- Requires an interpolation-capable solver: Z3 4.12+ (`get-interpolant`) or
  SMTInterpol, probed by `interpolation::find_interpolation_solver`. Absent
  one, the engine reports itself unavailable and is never registered.
- Divergence: the interpolant sequence may never reach a fixpoint, in which
  case the iteration cap ends it with no conclusion.

## How it's certified

Not independently certified. The accumulated `F` is exactly the inductive
invariant a certifier would want to re-check — it is computed and then
discarded rather than published as an `Artifact::Invariant`. See
`docs/strategies/README.md` § "Certification status".
