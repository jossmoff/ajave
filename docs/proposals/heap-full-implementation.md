# Full heap modelling: checkpoints to completion

Plan, 2026-10-27. Successor to `docs/proposals/heap-theory.md`, which scoped
arrays-and-fields and parked shape. This plan carries it to completion,
including linked structures.

Done already: `AllocSite` in the IR (#98), array contents in both CHC encoders
and the checker's LIA encoder, `Expr::Select`, and `invariant_check` able to
state and check an array fact.

**Concern, stated once.** Part E is new theory rather than an extension of an
existing encoding, and it is where schedule risk concentrates. It is scoped
below in small enough checkpoints that the risk is visible per checkpoint
rather than hidden in a single "shape analysis" line.

---

## The model, decided up front

All field work uses the **Burstall field-as-array** encoding, because
`smt_bmc` already does and it is the better choice:

```
one SMT array per FieldKey, indexed by the receiver reference
o.f   ==>  (select arr_f o)
o.f=v ==>  arr_f' = (store arr_f o v)
```

Aliasing then falls out of the solver — `o.f` and `p.f` are the same cell
exactly when `o = p` — so **no points-to analysis is needed for fields at
all**. This is strictly better than the per-`(site, field)` cells the previous
proposal assumed, and it is why Part A is cheaper than it looks.

Arrays keep the per-site model already built: identity comes from `AllocSite`,
which a reference cannot supply for an array because the IR has no array-ref
sort.

---

# Part A — Fields

## A1 · `Expr::Field`, and the certifier able to state a field fact

**Change.** `core::term::Expr` gains:

```rust
Field { field: FieldKey, obj: Box<Expr> },
```

`obj` is an `Expr`, not an `AllocSite`, because field-as-array is indexed by
the reference. `invariant_check::render` emits `(select fld_<class>_<name> <obj>)`,
matching whatever the encoder names it — the same producer/consumer naming
discipline `Expr::Select` already follows.

**Contract change.** `Expr`'s doc gains the rule that a `Field` claim is about
*one* receiver, where a `Select` claim is about *every* array from a site. Those
are different strengths and a consumer must not confuse them.

**Key tests.** In `invariant_check`:
- `a_field_invariant_can_be_confirmed` — control. `o.f = 7; check(o.f)` with
  `inv: o.f == 7` confirms. **Without this the negatives below are vacuous.**
- `a_field_invariant_contradicted_by_the_store_is_refuted`
- `a_field_fact_about_one_receiver_does_not_prove_another` — `o.f = 7; p.f = 0`
  then `inv: o.f == 7` must not discharge a check on `p.f`. This is the
  aliasing test and the reason the model was chosen.

**Gate.** Unit tests only. Smoke byte-identical (no engine publishes one yet).

## A2 · Fields in the checker's LIA encoder

**Change.** `interpolation.rs`: declare `fld_<class>_<name>` and its post-state
per `FieldKey` the body touches; `GetField` → `select`, `PutField` → `store`.
Thread into `mk_assign` exactly as the arrays are. A `PutField` through an
operand the encoder cannot name invalidates that field's array only — not all
of them, since a write to `o.f` cannot alter `o.g`.

**Contract change.** None. `invariant_check`'s module doc drops the sentence
saying a heap invariant is always `Inconclusive`.

**Key tests.** Promote A1's three from "render correctly" to "check correctly"
against a real transition relation. Plus:
- `a_field_write_through_an_unknown_receiver_invalidates_only_that_field`

**Gate.** Unit tests. Smoke byte-identical.

## A3 · Fields in both CHC encoders

**Change.** Same model, in `encode_chc_interproc` and `encode_chc_single`.
Field arrays become relation arguments, appended uniformly per method exactly
as the site arrays are. `PutField` gets the arm it has never had — it is
currently dropped outright, like `ArrayStore` was before tonight.

**Contract change.** `Approximations::HEAP_NO_CONTENTS` **gets its first real
producer**: a CHC discharge over a body whose fields the encoder could not name
declares it. That retires its `Parked` note.

**Key tests.** `encoder_conformance` gains, and both must be asserted
per-encoder because a fix to one silently leaves the other exposed:
- `safe_field_value` / `unsafe_field_value` corpus entries
- `the_interproc_encoder_proves_a_field_property`
- `the_bitvector_encoder_proves_a_field_property`
- `neither_encoder_proves_a_false_field_property`
- `neither_encoder_confuses_two_receivers_of_one_field`

**Gate.** Both properties, full corpus. First checkpoint that can move a score.
A *fall* means the field arrays made the queries too large for Spacer, which is
a real outcome and is why this is measured rather than assumed.

---

# Part B — The interval AI (the engine that discharges)

The highest-value and highest-risk part: 55 of 57 discharges on the sampled
corpus. There is **no escalation safety net** — #99 established that nothing is
currently unsound, so a cell read too narrow is a straight wrong TRUE. The
certifier is the only mechanism that would catch one, which is why A1–A2 come
first.

## B1 · `Scope` on artifacts

**Change.** `enum Scope { Execution, Method(MethodKey), Point(ProgramPoint), Heap }`
on `Invariant`. This is the field `docs/contracts.md` Part I identified as
missing and never got; it gets a producer in B2.

**Contract change.** The one `Invariant`'s doc already warns about informally:
a `VarId` is relative to one `Body`, a heap fact is global, and a consumer
reading the wrong one is the defect class that cost 32 points once.

**Key tests.** A heap-scoped invariant is not returned by a method-scoped
query, and vice versa.

**Gate.** Unit tests. Byte-identical.

## B2 · Site-indexed field cells, with the fallback that carries the soundness

**Change.** `fields: BTreeMap<FieldKey, Interval>` →
`BTreeMap<(AllocSite, FieldKey), Interval>`, **plus a merged cell per
`FieldKey`** used whenever the receiver's site is unknown. `FieldPrec::may_update_strongly`
becomes "the receiver's site is known and singular" rather than "the class has
one instance".

**The whole soundness argument is the fallback.** The flat abstraction is safe
*because* it merges; a site-indexed one is safe only if an unknown receiver
reads the merged cell. That needs a test named after it.

**Key tests.** Benchmarks **before** the change, per CLAUDE.md:
- `benchmarks/ajave/heap/TwoObjectsDistinctFieldValues` — two sites, different
  values, flat must join and site-indexed must not
- `benchmarks/ajave/heap/UnknownReceiverReadsTheMergedCell` — a receiver from a
  havoced call; reading it must give the join, not either site
- existing `TwoInstancesOneAllocationSite` must still answer FALSE

Unit: `an_unknown_receiver_falls_back_to_the_merged_cell`.

**Gate.** Both properties, full corpus, **plus `AJAVE_CERTIFY_TRUE=1`**, plus
metamorphic and ablation on the checked profile. Expected **+20 to +50**. A
fall is a wrong-TRUE risk, not a precision loss, and reverts.

## B3 · Array element intervals

**Change.** An interval per `(AllocSite, index)` for constant indices, and a
single joined cell per site for non-constant ones. Replaces `:1608`'s "element
values are not modelled (only lengths)".

**Key tests.** `benchmarks/ajave/heap/ArrayElementWrittenThenRead`, and a
non-constant-index case that must read the joined cell.

**Gate.** Both properties. Expected smaller than B2 — most array reasoning in
the corpus is about bounds, which lengths already cover.

---

# Part C — Interprocedural heap

## C1 · Heap through CHC summary relations

**Change.** Summary relations are `(declare-fun {mid}_s (Int … Int) Bool)` with
arity `params + 1`. They gain the field arrays and the callee's array sites, so
a heap effect crosses a call instead of being clobbered. Removes the write-set
approximation added tonight.

**Contract change.** `HEAP_NO_CONTENTS` stops being declared for
cross-procedural reads.

**Key tests.** `a_field_written_in_a_callee_is_visible_to_the_caller`, and the
converse — a callee that writes nothing must not invalidate anything.

**Gate.** Both properties. The risk is encoding size: `docs/` records 234
binders per clause once producing `unknown` in 90ms. Measure clause count and
bytes, not just the score.

---

# Part D — Quantified invariants

The gate tonight's work actually hit. `aastore_aaload1` needs
`∀j. 0 ≤ j < size → select(arr, j) ≠ null`, synthesised from one loop and used
in another. Contents made that *expressible*; it is not the proof.

## D1 · Spacer quantified generalisation

**Change.** Pass `fp.spacer.q3.use_qgen=true` and
`fp.spacer.ground_pobs=false` on the CHC invocation, behind
`AJAVE_CHC_QGEN`, default off until measured.

**Key tests.** `the_interproc_encoder_proves_a_quantified_array_property` over
a store-then-assert loop — the `aastore_aaload1` shape reduced to a fixture.
This is the checkpoint whose test is allowed to *start* red.

**Gate.** Both properties, flag on and off. The honest expectation is that
this is where #95's ~+7 and part of #60's `algorithms` ceiling live. A
timeout increase is the likely cost and must be measured.

## D2 · Template invariants, if D1 is insufficient

**Change.** For a loop writing `a[i]` under a guard, propose
`∀j. 0 ≤ j < i → P(select(a, j))` for `P` drawn from the obligation itself
(non-null, bounded, equal-to-constant) and let the solver check it. A proposed
invariant that fails to verify is discarded, so this costs precision only.

**Key tests.** The same fixture as D1, plus a fixture where the template is
*wrong* and must be rejected rather than assumed.

**Gate.** Both properties. Report which template fired per task.

---

# Part E — Shape: linked structures

The genuinely new theory. Target: `BinaryTreeSearch-MemSat01`,
`BinaryTreeSearch-MemUnsat02` and the `objects` tasks that build lists.

Scoped as three checkpoints so each is independently useful and independently
abandonable.

## E1 · Ghost depth, and acyclicity from it

The cheapest shape property worth having, and it needs no new theory.

**Change.** A ghost `depth` per reference, maintained like the ghost array
lengths already are: `new` sets depth 0; `o.next = p` sets
`depth(o) = depth(p) + 1` when `p` is non-null. Then **acyclicity is
`depth` being well-founded**, which the existing integer machinery proves.

**Contract change.** `Expr` gains `Depth { obj: Box<Expr> }`. `HEAP_NO_SHAPE`
gets its first producer: an engine that reasons about depth but not
disjointness declares it still.

**Key tests.**
- `benchmarks/ajave/heap/AcyclicListTerminates` — a traversal whose
  termination follows from decreasing depth
- `benchmarks/ajave/heap/CyclicListIsNotProvenAcyclic` — `o.next = o` must not
  be provable acyclic. **The soundness case.**
- unit: `a_null_tail_has_depth_zero`, `a_cycle_makes_depth_unsatisfiable`

**Gate.** Both properties. Expected: the list-traversal tasks in `objects`.

## E2 · Reachability as a derived relation

**Change.** A Horn relation `reach_f(x, y)` per reference field, defined by the
usual two clauses (`x = y`, and `reach(x, z) ∧ z.f = y`). Spacer handles
recursive relations natively — this is what CHC is *for*, and it is why shape
is cheaper here than in an abstract-interpretation setting.

**Contract change.** `Expr::Reach { field, from, to }`. The certifier must
check it, which means `invariant_check` gains the same two clauses.

**Key tests.**
- `reachability_is_reflexive_and_transitive` (unit, over the clauses)
- `benchmarks/ajave/heap/ReachableFromHeadAfterInsert`
- `benchmarks/ajave/heap/UnreachableAfterUnlink` — the soundness case: after
  `o.next = o.next.next`, the skipped node must **not** be provably reachable,
  and must not be provably *un*reachable either if it is aliased elsewhere.

**Gate.** Both properties. Watch encoding size — a recursive relation per field
per method is the obvious blow-up and C1's measurement discipline applies.

## E3 · Disjointness, and the tree tasks

**Change.** `Expr::Disjoint { field, a, b }`, defined from `reach`: no node is
reachable from both. A tree insert preserves it; this is what
`BinaryTreeSearch` needs.

**Contract change.** `HEAP_NO_SHAPE` is retired — every producer either
reasons about shape or declines.

**Key tests.**
- `benchmarks/ajave/heap/TreeSubtreesAreDisjoint`
- `benchmarks/ajave/heap/SharedSubtreeIsNotDisjoint` — soundness
- the two `BinaryTreeSearch` tasks become the acceptance test

**Gate.** Both properties. This is the checkpoint that either reaches #60's
remaining ceiling or demonstrates that these tasks need separation logic
proper rather than reachability predicates — and *that* is a legitimate
outcome to discover here rather than assume now.

---

# Part F — CEGAR (optional, recommend skipping)

`body_uses_havoced_ops` is a **soundness** guard: predicate abstraction over an
unconstrained heap value collapses to Top, and a Top state makes the safety
check trivially succeed. Relaxing it needs the domain to handle Top correctly,
and `predicate.rs` cannot represent infeasibility at all (#42,
`is_bottom` hardwired `false`).

The engine census measured `cegar` running on **0 of 121** tasks and concluded
that unlocking it *competes* with `interval` rather than adding. Recommend
skipping unless B2 shows `interval` saturating.

---

# Sequencing and isolation

```
A1 → A2 → A3        fields, each independently shippable
B1 → B2 → B3        the interval AI; B2 needs A1+A2 for its safety net
C1                  independent of B, needs A3
D1 → D2             independent of everything above
E1 → E2 → E3        E1 independent; E2 needs A2; E3 needs E2
```

Parallelisable: A, D and E1 touch disjoint files. B must not run concurrently
with A2, both touching `invariant_check`.

**Corpus runs needed:** A3, B2, B3, C1, D1, D2, E1, E2, E3 — nine, plus a
baseline before each. Everything else validates in unit tests.

**Two rules carried from tonight, both earned:**

1. **Every capability checkpoint asserts the positive case explicitly.** Adding
   a fixture to a corpus proves nothing; `both_encoders_actually_answer` only
   exercises `assert false` and the precision test reports rather than fails.
   Three bugs shipped past eight green tests tonight before an explicit
   `ChcOutcome::Safe` assertion caught them.
2. **A malformed query reports `unknown`, not an error.** In Horn mode `sat`
   means safe and `unsat` means unsafe, so an arity or sort mistake looks like
   the solver giving up. Every checkpoint that changes a relation signature
   must dump one encoding and run the solver on it directly.
