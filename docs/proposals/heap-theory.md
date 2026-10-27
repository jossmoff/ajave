# Heap theory: proposal and implementation plan

Proposal, 2026-10-27. Written after the 2026-10-26/27 soundness work, with the
corpus at valid-assert 877 / no-runtime-exception 1182.

Issues: #60 (algorithms and objects need a heap theory), #95 (CHC heap contents).

---

# Part 1 — There is no heap theory. There are five heap approximations.

Surveyed 2026-10-27. Nothing is shared between them.

| engine | representation | array contents | field contents | object identity |
|---|---|---|---|---|
| `interval` / `ai` | `fields: BTreeMap<FieldKey, Interval>` — **one cell per `(class, name, desc)`, receiver ignored** | **not modelled at all** (lengths only) | flat, strong update only for statics or proven-singleton classes (`FieldPrec`) | none |
| `smt_bmc` | `array_map: Vec<(ref_term, arr_term, len_term)>` — per-reference SMT arrays with a ghost length, plus `field_arrays`, `str_array_map` | **yes**, SMT array theory | per-reference | the reference term itself |
| `chc` | ghost array lengths | **no** — unconstrained reads | **no** — unconstrained reads | none |
| `cegar` / `predicate` | none | n/a | n/a | n/a — declines the body |
| `concurrent_exec` | `heap: BTreeMap<(ObjId, String), (bool, i64)>`, concrete, reference-ness tagged | n/a (concrete) | per-object | `ObjId(u32)` |

Plus the lifter's synthetic fields, which are a sixth de-facto heap:
`$$coll_size`, `$$coll_last`, `$cap`, `$value`, `$lambda`, `$ordinal`.

**The BMC has the only real heap.** Everything that discharges at scale —
`interval`, which produced 55 of 57 discharges on the sampled corpus — either
ignores the receiver or ignores contents entirely.

## What that costs, measured

From #60, the `algorithms` category alone:

| property | ok TRUE | ok FALSE | UNK | TO | score |
|---|---|---|---|---|---|
| valid-assert | 5 | 6 | 22 | 7 | 16 |
| no-runtime-exception | 4 | 2 | 27 | 7 | 10 |

Combined ceiling roughly **+97**, and `objects` has the same character. Against
a current total of 2059 that is a ~5% swing from one capability.

From #95, the cost of CHC's retreat to unconstrained contents was **valid-assert
867 → 860**, and the losses were *not* timeouts — they were `unsat` answers that
stopped being provable: `aastore_aaload1`, `StrictLineReader`, both on
`ArrayLoad`.

---

# Part 2 — The missing primitive is object identity in the IR

`Rvalue::New(String)` carries a **class name and nothing else**. There is no
allocation site, no object id, no abstract address. `NewArray` is the same.

So every engine that wants heap state must invent identity for itself, and the
table above is what that produced: the BMC keys on an SMT term, the concurrent
executor on an `ObjId` counter, the interval AI gave up and went flat, CHC and
CEGAR gave up entirely.

**This is why there are five heaps rather than one.** It is also why the flat
abstraction exists: with no identity, "the field `n` of *this* object" is
inexpressible, so the only sound choice is to merge every instance into one
cell — which is what `interval.rs` does, and which is exact only when a class
has a single live instance (hence `FieldPrec::singleton_classes`).

Supplying identity in the IR is the enabling change, it is cheap, and it changes
no semantics. Everything else in this proposal depends on it.

---

# Part 3 — Two problems, not one. Only the first is in scope.

**(a) Arrays and non-recursive fields.** `a[i] = v; … = a[j]`, `o.f = v; … =
p.f`. Tractable with SMT array theory plus an aliasing decision, which is what
the BMC already does. This is where the `algorithms` array-heavy loops and most
of `objects` live.

**(b) Linked and recursive structures.** `BinaryTreeSearch-MemSat01`,
`BinaryTreeSearch-MemUnsat02` and friends need reasoning about *unbounded*
shape — "this list is acyclic", "this tree's left subtree is disjoint from its
right". That is shape analysis or separation logic, not array theory, and the
useful literature is Infer's bi-abduction and TVLA-style shape graphs.

**Only (a) is proposed here.** (b) is a separate multi-month effort and
pretending otherwise is how a plan stops being believable. (b) is listed as H6,
parked, with its prerequisite named.

---

# Part 4 — What each engine needs

| engine | blocker today | needs | risk if done wrong |
|---|---|---|---|
| `interval` | no identity, so fields are flat and arrays are absent | allocation sites; site-indexed field cells; array element intervals | **high — this is the engine that discharges.** A field read that returns a too-narrow interval is a wrong TRUE |
| `chc` | contents are unconstrained reads | heap state threaded through the Horn clauses as an SMT array argument (#95) | **high.** The previous attempt used an uninterpreted predicate in a clause *body*, which the solver may read as empty, making the read path vacuously safe — two wrong TRUEs |
| `smt_bmc` | already has a heap | nothing structural; should *publish* what it approximates | low |
| `cegar` | `body_uses_havoced_ops` declines any `GetField`/`PutField`/`GetStatic` | heap-aware predicates, which need identity first | **high.** Predicate abstraction over an unconstrained heap value collapses to Top, and a Top state makes the safety check trivially succeed |
| `kinduction` | inherits `smt_encode`'s heap handling | whatever `smt_encode` gains | medium |
| `concurrent_exec` | has a concrete heap | should share the identity scheme rather than its own `ObjId` | low |

The asymmetry to hold onto: **the engine with the best heap discharges the
least, and the engine that discharges the most has the worst heap.** Improving
the BMC's heap buys little; improving the interval AI's buys the most and is the
most dangerous.

---

# Part 5 — Changes to the contract

This is the part that must land *before* engine work, for the reason the
2026-10-26/27 session demonstrated at cost.

## 5.1 `HEAP_ALIASING` is declared and has no producer

`Approximations::HEAP_ALIASING` exists (`artifact.rs:65`), has a display name
(`"heap-aliasing"`), and **no engine sets it**. Verified 2026-10-27.

So today, when `interval` discharges an obligation using its flat field
abstraction — receiver ignored, every instance merged — it publishes through
`bb.publish`, which hardcodes `Approximations::EXACT`. The obligation is closed
as faithfully modelled. `open_for(HEAP_ALIASING)` would return it to an engine
that models aliasing properly, and nothing ever calls that because nothing ever
declares it.

**This is the #48 shape exactly.** Last night the bitvector BMC was discharging
float obligations it had modelled as bit-pattern arithmetic; the escalation pass
that existed to reclaim them had been dead since it was written. Fixing the
discharge cost **zero points** only because the escalation pass was repaired
first. Had the order been reversed, it would have cost real score.

**So: produce `HEAP_ALIASING` honestly before changing any heap representation.**
Otherwise the first heap-faithful engine has nothing to reclaim, and every
intermediate step looks like a regression.

## 5.2 One flag is not enough — three kinds of heap approximation

`HEAP_ALIASING` conflates three different failures, and an engine escalating on
one does not fix the others:

| flag | means | who declares it today |
|---|---|---|
| `HEAP_ALIASING` | receiver identity ignored; instances merged | nobody — `interval` should |
| `HEAP_NO_CONTENTS` *(new)* | reads return unconstrained values; only lengths known | nobody — `chc` should |
| `HEAP_NO_SHAPE` *(new)* | no reasoning about acyclicity or disjointness | nobody — everyone, for (b) |

`open_for(models_faithfully)` returns obligations closed under an approximation
the caller does *not* make, and `CLAUDE.md` is explicit that the caller must fix
**everything** that went wrong, not merely something. An engine that models
aliasing but still reads contents unconstrained must not be handed an obligation
lost to missing contents — that is pure cost.

## 5.3 `Expr` cannot express a heap fact, so heap proofs are uncertifiable

`core::term::Expr` is `Var | Int | Double | Bool | Bin | Not | Apply`. There is
no `Select(array, index)` and no `Field(obj, name)`.

Consequences, both live:

* `Artifact::Invariant.formula` is an `Expr`, so **no invariant can mention the
  heap.** `ai.rs`'s `interval_state_as_formula` already excludes non-integer
  cells for exactly this reason.
* `invariant_check::check_inductive` therefore cannot check a heap invariant,
  and returns `Inconclusive` for anything it cannot state. **With
  `AJAVE_CERTIFY_TRUE=1`, every heap-based proof is refused.**

So heap work and certification collide: build the heap theory without extending
`Expr`, and turning certification on throws away precisely the new proofs.

`Expr` needs two forms, and they must be keyed on the identity from H0:

```rust
/// Element of an array at an index. The array is named by its allocation
/// site, not by a local, because the fact outlives any particular variable.
Select { site: AllocSite, index: Box<Expr> },
/// A field of an object named by its allocation site.
Field { site: AllocSite, field: FieldKey },
```

## 5.4 Scope: a heap fact is not `VarId`-relative

`Invariant` documents its own hazard: "`VarId` is relative to `at.method`'s
body, so a consumer looking at a different body must not read this". A heap
fact is **global** — `o.f` means the same thing in every method — and cannot be
expressed as a `VarId` at a `ProgramPoint`.

This is the `scope` field that `docs/contracts.md` Part I identified as missing
and has never been added. Heap work is what forces it:

```rust
enum Scope { Execution, Method(MethodKey), Point(ProgramPoint), Heap }
```

Without it, a heap invariant published at one program point will be read by a
consumer in another method, and `CLAUDE.md` already records that class of
defect costing 32 points once.

## 5.5 `ProofKind` must record the aliasing assumption

A proof that rests on "these two references do not alias" is only as good as
that assumption. Either the assumption is discharged (and the proof is
unconditional), or it is assumed (and the proof is conditional and must say so).

`ProofKind::Invariant(id)` cannot express the second. Rather than a new variant,
the honest route is that an engine assuming non-aliasing declares
`HEAP_ALIASING` and does not claim `EXACT` — which is 5.1, and is why 5.1 is
first.

---

# Part 6 — Implementation plan

Each phase is independently executable and independently validatable. Phases
H0–H2 are contract work and must land before any engine changes, for the reason
in 5.1. H3–H5 are then parallel.

## H0 — Allocation sites in the IR

**Change.** `Rvalue::New(String)` → `Rvalue::New { class: String, site: AllocSite }`,
and the same for `NewArray`. `AllocSite` is a `(MethodKey, BlockId, usize)` or
an interned `u32` assigned by the lifter, stable across runs.

A site is **not** an object: a `new` inside a loop produces many objects at one
site. That is the standard allocation-site abstraction, it is sound as an
over-approximation (two objects from one site are conflated), and it is strictly
more precise than today's class-level merge.

**Validation.** `cargo test`; the IR well-formedness validator gains "every
`AllocSite` is in range"; smoke must be **byte-identical** — no engine reads the
field yet, so any change means something was already depending on the shape of
`New`. Cost: minutes.

**Why first.** Nothing else is expressible without it, and it is the only phase
with no soundness risk.

## H1 — Declare heap approximations honestly

**Change.** `interval` declares `HEAP_ALIASING` on every discharge that read a
field cell; `chc` declares `HEAP_NO_CONTENTS`. Add the two new flags from 5.2.
Add a `HEAP_FAITHFUL`-style escalation pass registration for the BMC, mirroring
`smt-bmc-fpa`.

**Validation.** Both properties, full corpus. **Expect the score to be flat and
the `open_for` population to grow** — this phase closes nothing new, it only
tells the truth about what was already closed. A score *change* here means an
engine was reading an obligation it should not have been, which is a finding.

The escalation pass must be checked for the two bugs that killed the FPA one:
it must return `Blocked` rather than `Exhausted` when nothing is heap-approximated
yet, and it must declare `Interest::STATUS`. Add both to `scripts/check-contracts.py`
as E6 if that check can be made precise.

## H2 — `Expr` heap terms, `Scope`, and certifier support

**Change.** `Expr::Select` and `Expr::Field` as in 5.3; `Scope` as in 5.4;
`invariant_check` renders and checks them via SMT array theory, which `smt_bmc`
already uses so the encoder exists.

**Validation.** Unit tests only, no corpus: an array invariant that is
sufficient and preserved confirms; one that is not refuted; an invariant over a
site the body never allocates is `Inconclusive`. Follow `invariant_check`'s
existing fixture discipline — **a control that confirms, first**, or every
negative result is vacuous.

## H3 — Site-indexed fields and array contents in the interval AI

The highest-value and highest-risk phase. **This is the engine that discharges.**

**Change.** `fields: BTreeMap<FieldKey, Interval>` →
`BTreeMap<(AllocSite, FieldKey), Interval>`, with a `Top`-valued fallback cell
per `FieldKey` for reads whose receiver site is unknown. Array elements get an
interval per `(AllocSite, index-or-Top)`. `FieldPrec::may_update_strongly`
becomes "the receiver's site is known and singular" rather than "the class has
one instance".

**Validation.** `benchmarks/ajave/` gains minimal programs *before* the change,
per `CLAUDE.md`: two objects of one class with different field values, where the
flat abstraction must join and the site-indexed one must not; an array written
at one index and read at another. Then both properties, full corpus, and a
metamorphic + ablation sweep on the checked profile.

**The risk, stated.** A read that returns a too-narrow interval is a wrong TRUE.
The flat abstraction is safe because it merges; a site-indexed one is only safe
if an unknown receiver falls back to the merged cell. That fallback is the whole
soundness argument and it needs a test named after it.

## H4 — Threaded heap state in CHC (#95)

**Change.** Thread an SMT array as an explicit argument of each Horn relation,
so a read is a `select` on the threaded state rather than a fresh constant.

**The trap, from the issue.** The previous attempt used JayHorn-style space
invariants — an uninterpreted predicate in a clause *body*, which the solver
interprets and may choose **empty**, making `assume phi(..)` unsatisfiable and
the read path vacuously safe. That produced wrong TRUEs on
`MinePump/spec1-5_product45` and `java-ranger-regression/TCAS_prop1`. Both are
smoke canaries; keep them there.

**Validation.** Those two canaries, plus `chc.rs`'s `encoder_conformance` suite —
and note `docs/` records CHC as having **two encoders**, so a fix to one leaves
the other exposed. Both properties, full corpus. Target: recovering the
867 → 860 loss #95 measured.

## H5 — Heap-aware predicates in CEGAR

**Change.** Allow `GetField`/`PutField`/`GetStatic` once H0 gives identity, with
predicates over `(site, field)` cells.

**Validation.** `body_uses_havoced_ops` is a **soundness** guard, not a capability
one: predicate abstraction over an unconstrained heap value collapses to Top, and
a Top state makes the safety check trivially succeed. Relaxing it needs the
domain to handle Top correctly first, and `predicate.rs` additionally cannot
represent infeasibility at all (task #42, `is_bottom` hardwired `false`).

**Honest prior: do this last, or not at all.** The engine census measured `cegar`
running on **0 of 121** tasks and concluded that unlocking it *competes* with
`interval` rather than adding, because both target the same obligations. H5 is
the phase most likely to be worth skipping.

## H6 — Shape analysis for linked structures (parked)

`BinaryTreeSearch`-shaped tasks need acyclicity and disjointness, which array
theory cannot express. Prerequisite: H0–H2. Approach: bi-abduction over a small
separation-logic fragment, or shape graphs.

Parked explicitly, with `HEAP_NO_SHAPE` declared by everyone in the meantime so
that when an engine can do this, the obligations are waiting for it.

---

# Expected outcome, and what would falsify it

| phase | expected score | what a surprise means |
|---|---|---|
| H0 | **identical** | an engine was depending on `New`'s shape |
| H1 | **flat**, `open_for` population grows | an engine was reading obligations it should not have |
| H2 | identical (off the scoring path) | — |
| H3 | **+20 to +50**, concentrated in `objects` and `algorithms` | a *fall* means the unknown-receiver fallback is wrong, which is a wrong-TRUE risk, not a precision one |
| H4 | **+7 to +15**, recovering #95 | a wrong TRUE on either canary means the space-invariant trap was reintroduced |
| H5 | 0 to +10, competing with `interval` | — |

#60's ceiling for `algorithms` + `objects` is ~+97. A realistic expectation for
H3 + H4 is **half of it**, because part of that ceiling is the linked-structure
tasks that H6 addresses and these phases do not.

The number to quote afterwards is both properties, idle-gated, with
`AJAVE_CERTIFY_TRUE` stated either way — and H2 is what makes it possible to
have certification *on* while heap proofs still count.
