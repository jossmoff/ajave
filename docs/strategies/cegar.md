# CEGAR (counterexample-guided abstraction refinement)

**Direction:** Over
**Tier:** 4
**Status:** working
**Source:** `roast-engines/src/cegar.rs`

## What it proves or finds

Drives the predicate abstraction domain (`docs/strategies/predicate.md`)
through the shared `reachability()` fixpoint, and grows its precision whenever
the abstraction turns out to be too coarse.

The loop:

1. Run `reachability` with the current predicate precision (initially empty).
2. If no abstract state reaches an error location, every obligation in the
   body is discharged — at this precision the error is unreachable, and since
   the domain over-approximates, it is unreachable in fact.
3. Otherwise extract the abstract trace that got there and check it against
   the concrete semantics via `encode_body_lia`. If it is feasible, this
   engine cannot say anything (it is `Over` and may not publish a violation),
   so it stops.
4. If it is infeasible — a spurious counterexample — compute a Craig
   interpolant along the trace, turn it into new predicates via
   `predicates_from_interpolant`, add them to the precision and go to 1.

Capped at `MAX_REFINEMENTS = 20` iterations and `MAX_STATES = 10_000` abstract
states per run.

## What it assumes / where it's unsound if the assumption breaks

- **The havoc guard.** `body_uses_havoced_ops` skips any body with field
  access, `instanceof`, unresolved calls or explicit `Havoc`, for the same
  reason as every other proving engine: the LIA feasibility check would treat
  an unmodelled operation as unconstrained, and an infeasibility verdict over
  that encoding means nothing.
- **The `complete` flag.** A discharge is only valid if `reachability`
  actually converged. Hitting `MAX_STATES` returns `complete = false`, and the
  engine must not read "no error state reached" off a truncated search — that
  is the exact shape of the false TRUE described in `cpa::Cpa::stop`'s doc
  comment.
- **Refinement progress is not guaranteed.** Nothing proves each round adds a
  predicate that excludes the current trace, so the loop can revisit the same
  spurious trace; the iteration cap is what terminates it, not a progress
  argument.

## Known incompleteness

- Bodies with heap operations, unresolved calls or floating point.
- Requires an interpolation-capable solver (Z3 4.12+ or SMTInterpol). Without
  one the engine reports itself unavailable and is never registered.
- The predicate language is comparisons only, so a property needing e.g. a
  linear combination of three variables is not expressible however many
  refinement rounds run.
- A feasible counterexample is detected and then dropped. It is exactly the
  material a falsifier wants, and the blackboard has an `Artifact::Trace`
  variant for it — publishing it is the obvious first real use of the
  artifact-exchange design (see `docs/architecture.md`).

## How it's certified

Not independently certified. See `docs/strategies/README.md`
§ "Certification status".
