# presolve

**Direction:** Over
**Tier:** 0 (syntactic, pre-analysis)
**Status:** working
**Source:** `roast-engines/src/presolve.rs`

## What it proves or finds

Discharges any obligation whose safety condition is a literal non-zero
integer constant — the case where the check can never fire regardless of what
the rest of the program does. This is the cheapest possible pass: no state
exploration, one linear scan over open obligations, run exactly once at the
start of the schedule (`Orchestrator::Phase::Presolve`).

## What it assumes / where it's unsound if the assumption breaks

Only trusts `Operand::Const(Const::Int(v))` where `v != 0`. Everything else —
including a constant `0` (which means "always violated if reached", the
`Assertion` obligation shape) — is deliberately left alone rather than
reasoned about. There is no unsoundness surface here: the check is a single
pattern match with no approximation to get wrong.

## Known incompleteness

Anything that isn't a bare non-zero integer constant. In particular it does
**not** try to fold `v3 > 3` style comparisons even when both operands happen
to be constants after inlining elsewhere — that's the interval domain's job
(`docs/strategies/interval.md`), which subsumes this case entirely once it
runs. Presolve exists to catch the trivial case for free before anything
heavier starts, not to be a mini constant-folder.

## How it's certified

Not independently certified. A `Discharged` result here needs no certifier
because there's nothing to get wrong: the safety condition literally cannot
be false, by construction of the pattern match. (Contrast with the interval
domain, where "provably safe" depends on a fixpoint having actually
converged, and *is* worth an eventual inductive-invariant check.)
