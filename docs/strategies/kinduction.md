# k-induction

**Direction:** Over
**Tier:** 3
**Status:** working
**Source:** `roast-engines/src/kinduction.rs`

## What it proves or finds

Proves that an obligation can never be violated, by strengthening a bounded
result into an unbounded one. Two halves:

- **Base case.** Consumed rather than computed: the SMT BMC engine publishes
  `Status::Bounded { k }` meaning "no violation is reachable within `k`
  steps". k-induction reads that off the blackboard instead of re-deriving it.
- **Step case.** Encode `k` *generic* consecutive states linked by the
  transition relation and ask: if the safety condition holds at each of the
  first `k`, must it hold at state `k+1`? An UNSAT answer means the property
  is inductive, and the obligation is discharged as
  `ProofKind::KInduction { k }`.

For a loop-free body `k = 0` suffices — there is no cycle left to unroll, so
the base case already covers every reachable state. `body_has_loops` decides
which case applies.

## What it assumes / where it's unsound if the assumption breaks

The step case is encoded by `smt_encode::encode_body`, which models integer
and long arithmetic as bitvectors and **havocs everything else** — field
reads, `instanceof`, unresolved calls. An unconstrained value satisfies more
formulas than the real one does, so an UNSAT result over a havoced encoding
would prove nothing while looking like a proof. The guard is
`body_uses_havoced_ops`: any body containing such an operation is skipped
outright rather than encoded imprecisely. That guard is the single load-bearing
soundness assumption here — see `docs/strategies/README.md` on why it is
shared with CHC, IMC and CEGAR rather than reimplemented per engine.

The base case is trusted from the blackboard. `Status::Bounded` may only be
published by an engine that genuinely explored to depth `k`; the direction
discipline does not police this, because `Bounded` is neither a discharge nor
a violation.

## Known incompleteness

- Any body with heap operations, unresolved calls, or floating point.
- Properties that are true but not *k*-inductive for the `k` the BMC engine
  reached. There is no invariant strengthening: if the step case comes back
  SAT, the engine stalls rather than trying to find an auxiliary invariant.
- Requires an SMT solver binary on `PATH` (via `SmtLibFactory::from_env`); with
  none, the engine is never registered.

## How it's certified

Not independently certified today. `ProofKind::KInduction { k }` records the
depth so a future certifier can re-run the step case, but no such certifier
exists — see `docs/strategies/README.md` § "Certification status" for what
that means for TRUE verdicts generally.
