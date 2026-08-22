# CHC (Constrained Horn Clauses)

**Direction:** Over
**Tier:** 5 (escape hatch)
**Status:** working
**Source:** `roast-engines/src/chc.rs`

## What it proves or finds

Translates a method body into a set of Constrained Horn Clauses and hands the
whole thing to a Horn solver, which is then responsible for discovering the
loop invariants itself. This is the escape hatch: instead of choosing an
abstract domain, roast states the verification condition and lets a
specialised engine find whatever inductive invariant it needs.

The encoding is one uninterpreted relation per basic block —
`block_N(v0, …, vK)` over every variable in the method — plus one clause per
CFG edge encoding that edge's transfer semantics, plus a query asking whether
`error` is reachable. `unsat` means no error state is reachable and every
obligation in the body is discharged.

Operands and rvalues are rendered through `smt_text` with `BitvectorTheory`,
so Java's wrapping integer semantics are modelled exactly rather than as
mathematical integers.

Solver: Z3 in CHC mode by default; override with `ROAST_CHC_SOLVER`
(Eldarica and Golem both read the same dialect). If the binary is absent the
engine reports itself unavailable and is never registered.

## What it assumes / where it's unsound if the assumption breaks

Same havoc assumption as every other proving engine: the encoding covers
integer and long arithmetic and nothing else, so a body containing field
access, `instanceof`, an unresolved call or an explicit `Havoc` is skipped via
`body_uses_havoced_ops`. Without that guard an `unsat` over an encoding that
simply omitted the heap would read as a proof.

The clause set is generated per body with no interprocedural edges, so a
called method's behaviour is not modelled — which is precisely why bodies
containing calls are excluded rather than approximated.

## Known incompleteness

- Bodies with heap operations, unresolved calls or floating point.
- `sat` and `unknown` are both treated as "no information". A `sat` answer
  would be a genuine counterexample trace, but this engine is `Over` and may
  not publish a violation, so the trace is currently discarded rather than
  handed to a falsifier.
- Solver timeouts surface as `unknown`.

## How it's certified

Not independently certified. The obligation is discharged on the Horn
solver's authority. A CHC solver can emit its inductive invariant, which
would be the natural certificate to re-check — that is not wired up.
