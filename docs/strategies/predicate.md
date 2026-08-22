# Predicate abstraction domain

**Direction:** Over
**Tier:** 4
**Status:** working
**Source:** `roast-engines/src/predicate.rs`

## What it proves or finds

A `Cpa` implementation, not an `Engine` — it supplies the abstract domain that
`docs/strategies/cegar.md` drives. It is listed here because the CPA substrate
treats a domain as a technique in its own right: swap the domain, change the
technique, touch nothing else.

The abstract state is a vector of three-valued truth assignments (`Some(true)`,
`Some(false)`, `None` for unknown) to the predicates in the current precision,
where a predicate is a comparison between two variables or a variable and a
constant. The precision — which predicates are tracked — is not fixed: CEGAR
grows it between reachability runs.

`transfer` computes the strongest postcondition available at this precision.
After `v := rv` it re-evaluates each predicate mentioning `v`; along a branch
edge it consults `find_defining_bin` to recover the comparison javac erased
into a branch, and sets any matching predicate directly.

`merge` is `merge_join`: states at the same program point are joined rather
than kept apart, which is what keeps the reached set bounded when the
precision is coarse.

## What it assumes / where it's unsound if the assumption breaks

The three-valued encoding is what makes this sound at any precision.
`None` means "this predicate's truth value is not known here", and every
consumer must treat it as "could be either" — never as false. A transfer
function that wrote `Some(_)` where it should have written `None` would claim
knowledge it does not have, and since this domain is `Over`, that becomes a
false TRUE. Every case in `evaluate_predicate_after_assign` that cannot
determine a value therefore returns `None` explicitly rather than falling
through to a default.

Joining is likewise conservative: a predicate joins to `Some(x)` only when
both sides agree, `None` otherwise.

## Known incompleteness

- Predicates are limited to comparisons of a variable against a variable or
  an integer constant. No arithmetic inside a predicate, no disjunction.
- Only assignment and branch edges refine anything; heap writes and calls
  leave the state untouched, which is sound but uninformative.
- Precision quality is entirely CEGAR's problem — with an empty precision this
  domain proves nothing at all.

## How it's certified

Not independently certified; see `docs/strategies/cegar.md`, which owns the
discharge.
