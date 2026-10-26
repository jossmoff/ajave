# Separating the abstract domain from the merge policy

Plan, 2026-10-26. Follows the seam census in `docs/contracts.md` Part II.

## Why

`ajave_core::cpa` is named after the CPA framework (Beyer/Henzinger/Theoduloz)
and parameterises a fixpoint by five operators. Measured 2026-10-26, across all
three implementors in the workspace:

| impl | `initial` | `transfer` | `merge` | `stop` | `prec` |
|---|---|---|---|---|---|
| `IntervalCpa` | ✓ | ✓ | default `Sep` | default | default |
| `WideningIntervalCpa` | ✓ delegates | ✓ delegates | ✓ widen | default | default |
| `PredicateCpa` | ✓ | ✓ | ✓ `merge_join` | default | default |

Three findings follow.

1. **`prec` is dead.** Nothing overrides it. Its doc comment calls it "the hook
   CEGAR lives in", which is false: CEGAR refines from *outside*, re-entering
   `reachability` with a larger `Prec` in a candidates loop (`cegar.rs:345`).
   That is eager outer-loop refinement, not lazy abstraction. Sixth instance of
   the live-but-vacuous class, and this one carries a false soundness-shaped
   claim in core.
2. **`stop` is never overridden either**, so the module header's promise of
   `stop_join` describes a configuration that does not exist. Of its three
   advertised configurations, none is what any implementor does.
3. **The one real axis is `merge`**, and it is orthogonal to the domain.
   `WideningIntervalCpa` proves it: `initial` and `transfer` are pure
   delegations to `self.base`, so an entire second `Cpa` impl exists to change
   one operator.

Separately, **90 of `cpa.rs`'s 227 lines are `successors()`**, which is not CPA
at all — it is the IR's CFG edge semantics, carrying three documented bug fixes
and zero tests. It is the load-bearing code in the file and it is misfiled.

## What changes

```
ajave-core/src/cpa.rs  (227 lines, 0 tests)
   │
   ├──▶ cfg.rs        successors() — IR CFG edge semantics       + 9 tests
   └──▶ fixpoint.rs   AbstractDomain, MergePolicy, explore()     + 13 tests
```

### The two traits

```rust
/// What the abstraction means and how it steps. Says nothing about how
/// exploration combines states.
pub trait AbstractDomain {
    type State: Lattice + HasLocation;
    /// Read-only configuration. Not adjusted during exploration — a caller
    /// wanting more precision re-enters `explore` with a larger one, which is
    /// what CEGAR does.
    type Prec: Clone;
    fn initial(&self, prog: &Program, at: &ProgramPoint) -> Self::State;
    fn transfer(&self, state, prog, edge, to, prec) -> Vec<Self::State>;
}

/// How exploration combines a new state with one already reached.
/// Orthogonal to the domain: one domain under two policies is two techniques.
pub trait MergePolicy<D: AbstractDomain> {
    fn merge(&self, new: &D::State, reached: &D::State, prec: &D::Prec)
        -> MergeResult<D::State>;
}
```

`explore(domain, policy, prog, start, prec, max_states)` replaces
`reachability(cpa, ...)`. The loop body is copied **verbatim** — this refactor
must not move a single verdict, so no opportunity to improve it is taken here.

### The policies

| Policy | Lives in | Replaces |
|---|---|---|
| `Sep` | core | `Cpa::merge`'s default; `IntervalCpa`'s behaviour |
| `Join` | core | `PredicateCpa::merge`, generically over any `Lattice` |
| `WidenAtLoopHeaders` | `interval.rs` | the whole `WideningIntervalCpa` struct |

`Join` is generic because `PredicateCpa::merge`'s guard
`joined.values != reached.values` is *equivalent* to `!joined.leq(reached)` on
that lattice: `join` keeps only agreeing predicates, so the result differs from
`reached` exactly when some predicate disagreed, which is exactly when
`reached` has knowledge the join dropped — the `(None, Some)` case that makes
`leq` false. Test 11 pins that equivalence rather than trusting the derivation.

`WidenAtLoopHeaders` keeps its own state (`join_counts`, thresholds,
`loop_headers`, `widen_delay`) and stays beside the domain whose widening it
calls. That is the correct boundary: the *trait* is generic, generic policies
are in core, domain-specific policies ship with their domain.

## The contract, stated

Written into the trait docs, with one test per clause.

**`Lattice`** — `leq` is a preorder, `join` is an upper bound in it.

**`MergePolicy::merge`** — two clauses, and both are load-bearing:

1. **Soundness.** `Joined(j)` requires `new.leq(j) && reached.leq(j)`. The
   explorer overwrites `reached` with `j` and drops `new`, so a `j` not covering
   both silently loses states — and a lost state is an unexamined obligation,
   which is discharged as vacuously safe. This is the −16 direction.
2. **Progress.** `Joined(j)` requires `!j.leq(reached)`. The explorer skips its
   `stop` check whenever a merge fires, so a `j` already covered re-enqueues
   forever. `WideningIntervalCpa::merge` documents having hit exactly this and
   guards it by hand; the clause makes it a law.

**`AbstractDomain::transfer`** — may return any number of states; returning
none means the edge is infeasible. (Unchanged, now written down.)

**`explore`** — `complete = false` means the state cap truncated the search, and
a caller claiming a proof on an incomplete search is the silent unsoundness the
design exists to prevent. (Unchanged, already documented, now has a test.)

## Expected behaviour tests

### `cfg.rs` — 9 tests, pinning three previously-untested bug fixes

| # | Test | Asserts |
|---|---|---|
| 1 | `an_assign_has_only_a_fallthrough_edge` | an `Assign` in a block *with* handlers yields exactly one `Edge::Stmt`. Emitting exceptional edges from non-`Check` positions let pre-assume states reach handlers and made dead catch blocks look live |
| 2 | `a_check_emits_every_exceptional_edge` | `Stmt::Check` with two handlers yields fallthrough + 2 `Edge::Term` |
| 3 | `a_call_emits_exceptional_edges_too` | a callee can propagate, so a handler guarding a call site is reachable. Omitting this edge made an obligation inside the handler discharge without being examined |
| 4 | `a_terminator_does_not_re_emit_check_handlers` | a `Goto` block with handlers yields exactly one edge — no duplicate exceptional edges at the terminator |
| 5 | `a_throw_emits_its_handlers` | `Terminator::Throw` is the one terminator that does |
| 6 | `a_branch_yields_both_sides_tagged` | exactly two edges, `Some(true)` and `Some(false)` |
| 7 | `a_switch_yields_the_default_and_every_case` | `1 + cases.len()` edges |
| 8 | `diverge_is_indistinguishable_from_return` | both yield exactly one `Edge::Exit`. Soundness rests elsewhere on `Body::is_fully_lifted` noticing, not on the CFG hiding it |
| 9 | `an_unknown_method_has_no_successors` | missing body yields empty, not a panic |

### `fixpoint.rs` — 13 tests

Lattice laws run as one generic helper instantiated on both domains, over
hand-built state sets (Top/empty, one narrow var, two vars, conflicting
nullness, a float var, an array length; and for predicates: all-unknown, one
known, two conflicting).

| # | Test | Asserts |
|---|---|---|
| 10 | `leq_is_reflexive` / `_for_predicates` | `a.leq(a)` for every sample |
| 11 | `join_is_an_upper_bound_of_both` / `_for_predicates` | `a.leq(a.join(b)) && b.leq(a.join(b))` over all pairs |
| 12 | `join_is_idempotent_up_to_leq` | `a.join(a).leq(a) && a.leq(a.join(a))` |
| 13 | `join_is_commutative_up_to_leq` | `a.join(b)` and `b.join(a)` are mutually `leq` |
| 14 | `bottom_is_below_everything` | `is_bottom()` implies `leq` all samples |
| 15 | `the_join_policy_is_equivalent_to_the_old_predicate_merge` | for all sample pairs, `joined.values != reached.values` ⟺ `!joined.leq(reached)`. Pins the derivation that licenses making `Join` generic |
| 16 | `a_joined_state_is_an_upper_bound_of_both_inputs` | contract clause 1, over all three policies × all sample pairs |
| 17 | `a_policy_never_joins_to_something_already_reached` | contract clause 2, same coverage. Pins the comment in `WideningIntervalCpa::merge` to a test |
| 18 | `sep_never_joins` | `Sep` returns `Sep` for every pair, including identical states |
| 19 | `the_join_policy_keeps_different_locations_apart` | same state, two locations → `Sep` |
| 20 | `widening_is_delayed_and_then_fires` | with `widen_delay = 2`: merges 1–2 return a plain join, merge 3 widens. Pins the delay, which is a fitted constant |
| 21 | `widening_reaches_a_fixpoint_in_bounded_steps` | repeatedly merging a growing interval at a loop header stabilises (`Sep`) within `widen_delay + 4` merges. The termination law, currently untested |
| 22 | `an_incomplete_search_is_reported_incomplete` | `explore` with `max_states = 1` on a two-state program returns `complete = false` |

### Behaviour preservation

| # | Test | Asserts |
|---|---|---|
| 23 | `explore_narrows_a_known_loop_exactly_as_before` | the interval domain under `WidenAtLoopHeaders` on a counted loop reaches the same bound (`i ∈ [0, 10]`) and the same reached-set size as `reachability` did. Golden, guards the move |

Plus the existing suites: `cegar::ask_on_decline_tests` must still pass
unchanged, since `prec`'s deletion must not touch refinement.

## Verification gate

This is a pure refactor. The bar is *no change*, not improvement.

1. `cargo test --workspace` — green, and 22 new tests present.
2. `cargo build --release`, then `python3 tools/bench.py --set smoke --check` —
   **identical to the baseline recorded before any edit**. Exit 0.
3. `tools/bench.py --set smoke --repeat 2` — determinism, because the refactor
   touches iteration over `reached`.

No corpus run. Nothing here changes what is explored; if smoke moves, the
refactor is wrong and gets reverted rather than re-baselined.

## Out of scope, deliberately

* The `reached.iter_mut()` merge loop folds the running join into *every*
  matching reached state, leaving earlier entries over-approximated. Sound for
  an Over analysis, possibly imprecise. Copied verbatim; filed, not fixed.
* `PredState::is_bottom` always returns `false` and `is_consistent` always
  `true`. No law is broken (bottom is simply not representable) and the tests
  will say so, but it means the predicate domain cannot detect infeasibility.
  Filed, not fixed.
* Renaming the `Cpa` *concept* out of the engine docs. The literature
  traceability is worth keeping; what gets fixed is the claims around it.
