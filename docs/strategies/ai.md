# ai (engine wrapper for `IntervalCpa`)

**Direction:** Over
**Tier:** 1
**Status:** working
**Source:** `ajave-engines/src/ai.rs`

This file is the `Engine` implementation that drives the abstract domain —
see [`interval.md`](interval.md) for what's actually being proved, the
soundness argument, and the `stop_sep` postmortem. What belongs here instead
is `ai.rs`'s own job, which is narrower than the domain itself:

## What it's responsible for that the domain isn't

- **Scope.** Runs `ajave_core::cpa::reachability` starting at `prog.entry`
  only — no interprocedural reasoning. A call the frontend couldn't lift
  diverges the body first, so this is a consequence of the frontend's own
  scope, not an independent limitation. Extending across method boundaries
  is a `Cpa` composition exercise (`ajave_core::cpa::Product`), not a rewrite
  of this file.
- **Refusing to run on an unlifted body.** `Body::is_fully_lifted` is checked
  before anything else — an over-approximating engine cannot see past a
  `Diverge` region, so it reports `Stalled` rather than silently proving
  things about a program it only partially understands.
- **Turning "never reached" into a proof, not silence.** Every obligation
  starts `safe = true` and is only falsified by an actual sighting where the
  condition could be zero. An obligation the converged search never visits at
  all counts as discharged — that's the correct reading of a sound
  over-approximation (if the abstract search never reaches it, no concrete
  execution can either), but it was also the site of a second real bug during
  development: the engine originally only recorded obligations it *saw*,
  so a provably-unreachable check (behind a branch the domain proved
  infeasible) silently stayed `Open` forever instead of counting as proved.
  Fixed by pre-seeding every obligation in the body to `true`.
- **Respecting the `complete` flag.** `reachability` returns whether the
  search actually converged or was cut off by the state cap. A truncated
  search reports `Stalled`, never `Discharged` — silence from an incomplete
  search is not a proof of anything, however tempting it is to treat it as
  one.

## How it's certified

See `interval.md` — not yet wired to `InductiveCheck`. This is tracked there,
not duplicated here, since the certification gap is about the domain's
fixpoint being trustworthy, not about anything specific to how this file
drives it.
