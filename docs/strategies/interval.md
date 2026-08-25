# interval (domain: `IntervalCpa`, engine: `AiEngine`)

**Direction:** Over
**Tier:** 1
**Status:** working
**Source:** `ajave-engines/src/interval.rs` (the `Cpa` domain), `ajave-engines/src/ai.rs` (the engine that runs it)

## What it proves or finds

Tracks `[lo, hi]` per integer-typed variable, narrows both operands of a
comparison at branch edges, and runs to a fixpoint via `ajave_core::cpa::reachability`.
An obligation is discharged if every reached state at its `Check` point proves
the safety condition non-zero — including obligations the search never
visits at all, which counts as a proof (not silence) once the search has
*converged*: see "Known incompleteness" below for why that qualifier matters.

This is what proves `assume(x > 5) => assert(x > 3)`. javac never reifies a
comparison as a boolean register — `x > 5` always lowers to a branch pushing a
literal `0` or `1` — so narrowing has to happen at the branch that produced
the boolean, not at the `Verifier.assume` call site that consumes it. See the
long comment at the top of `interval.rs` for the full walkthrough; it's
exactly the kind of thing that's obvious once written down and easy to get
backwards otherwise.

## What it assumes / where it's unsound if the assumption breaks

- **No widening.** Relies on `Cpa`'s default `merge_sep`/`stop_sep` — states
  stay separate rather than being joined. Sound, but only terminates on
  loop-free/diamond-shaped code. A genuine loop hits `reachability`'s state
  cap, which is handled correctly (see below), not unsoundly.
- **Overflow widens to Top, never narrows.** Java `int` wraps; rather than
  model wraparound precisely, any arithmetic whose result could leave the
  `i32` range collapses to the fully unconstrained interval. A wrong *narrow*
  bound would be unsound; a wrong *wide* one only costs precision. This trade
  is made explicitly, every time, in `Interval::clamp`.
- **Only plain integer arithmetic and comparisons are modelled.** Bitwise
  ops, shifts, and anything on `Ref`/`Long` collapse to Top. Sound, just
  uninformative — the domain never claims to know something it doesn't.

## Known incompleteness

- Any obligation past a `Diverge` region, since `AiEngine::step` refuses to
  run at all on a body that isn't fully lifted (`Body::is_fully_lifted`).
- Anything needing a loop invariant. No widening means no proof through an
  unbounded loop — that's the gap Tier 3 (k-induction, not yet built) is
  meant to close, using this domain's invariants as the step-case assumption
  (`docs/architecture.md` §6, combination A).
- Boundary-exact bugs the domain can't rule out but also can't prove safe
  (e.g. `i > 1000` when `i` could be exactly `1000`) correctly stay `UNKNOWN`
  rather than being wrongly discharged — see the postmortem below.

## How it's certified

Not yet wired to an independent certifier. `Status::Discharged { proof:
ProofKind::Invariant(id), .. }` records that an invariant *was* used, but
nothing currently re-checks it inductively — `core::certify::InductiveCheck`
is stubbed (`CertResult::Inconclusive` unconditionally). This is the
highest-priority certification gap in the tool: an `Over`-direction engine's
`TRUE` currently rests entirely on this engine's own fixpoint being correct,
which is exactly the kind of single-point-of-trust the certifier layer exists
to remove for `FALSE`.

## Postmortem: the `stop_sep` bug

Worth recording here rather than only in a commit message, because it's the
best illustration of why this domain needed a doc at all. The default
`stop_sep` implementation checked `state.leq(reached_state)` against *every*
previously reached state, regardless of program location. Since an empty
variable map reads as Top everywhere, the very first state explored (an empty
map, at the entry point) was `leq`-comparable to almost anything — so nearly
every later state, at unrelated program points, was judged "already covered"
and dropped before being added to `reached`. Exploration silently truncated
far short of the obligations that mattered.

This produced 12 confirmed wrong `TRUE` verdicts on the `jbmc-regression`
corpus before it was caught by measuring against ground truth rather than
trusting four hand-picked test cases. The fix — location-aware subsumption —
landed in `ajave_core::cpa`'s default `stop`, not in this domain, because the
bug was general to *any* `Cpa` implementation riding the shared substrate,
not specific to intervals. Correctness went from "51 correct, 12 wrong" to
"32 correct, 0 wrong" — a lower headline number and a strictly better tool.
