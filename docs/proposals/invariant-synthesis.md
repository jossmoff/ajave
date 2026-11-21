# Invariant synthesis: a vocabulary, a map, and one mechanism

Design, 2026-11-21. Successor to workstream A of `docs/plans/codebase-health.md`,
which built the checker (A2) and deferred the decision this document makes
(A3: "whether to publish maps").

**The claim.** The portfolio's over-approximating engines already know the facts
that would close most of the corpus, and cannot say them. Fixing that needs
three things — a wider claim vocabulary, invariant *maps* instead of points,
and a synthesiser — and the third turns out to be the same mechanism as the
checker, which is what makes the whole thing affordable.

---

## Part I — What the corpus says

Measured 2026-11-21 on `f09f7ab`, over the 415 task-property pairs still
unproven after large-block encoding (`tools/blocker_census.py`).

| why not | tasks | % | open obligations |
|---|---|---|---|
| **structural** | 123 | 29.7% | 2062 |
| float-escalation | 84 | 20.3% | 250 |
| refuted | 63 | 15.2% | 3 |
| no-candidate | 47 | 11.4% | 248 |
| theory | 37 | 8.9% | 62 |
| timeout | 29 | 7.0% | 0 |
| model | 29 | 7.0% | 473 |

`structural`'s own description is the thesis of this document: *"an invariant,
or a different cap — NOT more time."*

**The dominant single blocker is a loop.** Of the 415, **80 tasks** report
`all_paths_complete (truncated at handle_goto, budget left)`. `handle_goto` is
the back-edge site: the loop was unrolled to `MAX_LOOP_UNROLL` and cut, with
fork and block-visit budget still in hand. More unrolling is not the answer to
a loop that needs an arbitrary number of iterations; an invariant is.

**And the open obligations are overwhelmingly of two kinds:**

| open obligation kind | count | share |
|---|---|---|
| **NullDeref** | 1654 | 53.4% |
| **ArrayBounds** | 1057 | 34.1% |
| Assertion | 158 | 5.1% |
| NegArraySize | 128 | 4.1% |
| ClassCast | 54 | 1.7% |
| ExplicitThrow | 37 | 1.2% |
| DivByZero | 10 | 0.3% |

NullDeref and ArrayBounds are **87.5%** of the 3098 open obligations. Both are
invariant-shaped: *this reference is non-null here*, *this index is within this
array's length here*. Neither needs a new theory.

---

## Part II — Five gaps, each evidenced

### G1. The claim language cannot express either dominant obligation

`core::term::Expr` is the vocabulary every artifact speaks. It has `Var`,
`Int`, `Double`, `Bool`, `Bin`, `Not`, `Select { site, index }`,
`Field { field, obj }`, `Depth { field, obj }`, `Apply`.

It has **no null constant and no array length.** The IR has both —
`Const::Null` and `Rvalue::ArrayLength(Operand)` — so the gap is in the claim
language only. An invariant therefore cannot state `r != null` or
`i < a.length`, which is to say it cannot be *sufficient* for 87.5% of the open
set. `invariant_check`'s sufficiency obligation (`I ⟹ safety(o)`) is
unsatisfiable-by-vocabulary for those obligations, not merely unproven.

### G2. The engines know those facts privately

`interval.rs` tracks `nullness: BTreeMap<VarId, Nullness>` with an explicit
`NonNull`, and `array_lens: BTreeMap<VarId, Interval>` alongside
`array_len_var` and `array_len_prod`. The information exists, per variable, at
every program point the analysis visits.

`interval_state_as_formula` publishes **integer bounds only**, and says so:
"Only variables the analysis actually narrowed, and only integer ones". So the
nullness lattice and the length map are computed, used internally, and never
published. The architecture's premise is that engines cooperate through
artifacts; the most valuable facts it computes are unpublishable.

### G3. Invariants are published at check points, not at loop headers

`ai.rs` publishes an `Invariant` only inside the discharge path, keyed by the
obligation it is about: `if let Some((at, state)) = at_check.get(&oid)`. The
program point is the *check*.

An invariant that stops the BMC unrolling has to hold at the **loop header**.
No producer emits one there, which is why the 80 `handle_goto` tasks cannot be
helped by the existing channel however good the facts are.

### G4. Points, not maps — so nothing is ever `Inductive`

`invariant_check`'s module doc states the problem exactly:

> The third, **initiation**, is deliberately absent… "Holds initially" is a
> property of an invariant *map* — one assertion per program point — not of a
> single invariant at a single point… Until an engine publishes a map rather
> than a point, this pass can refuse bad proofs but cannot confirm good ones as
> *inductive* in the full sense.

Consequences, all live: nothing promotes `InvStatus::Candidate` to `Inductive`;
`Blackboard::inductive_invariants()` is empty; `certify_true_enabled()` is off
by default because turning it on "rejects every `ProofKind::Invariant`
discharge"; and #107 records that `AJAVE_CERTIFY_TRUE` is a no-op for every
engine except `interval-ai`.

Note that A2's written spec and A2's implementation disagree about this. The
plan lists initiation as one of three checkable obligations; the code found it
is not checkable at a point and deferred it. The implementation is right.

### G5. The channel's vocabulary is one sentence

`Blackboard::interval_hints_for_method` recovers hints by matching a single
syntactic shape:

```rust
let Expr::Bin(Op::And, lo_e, hi_e) = &inv.formula else { continue };
let (Expr::Bin(Op::Le, l, lv), Expr::Bin(Op::Le, hv, h)) = … else { continue };
let (Expr::Int(lo), Expr::Var(v1), Expr::Var(v2), Expr::Int(hi)) = … else { continue };
```

Anything that is not literally `(lo <= v) && (v <= hi)` on one variable is
silently skipped. A pentagon ordering `x < y`, a linear equality `x + y == c`,
a disjunction, an implication — all dropped without a word. Producer and
consumer agree by accident on one shape, which is the "producer and consumer
disagreeing about an artifact" fault class in `CLAUDE.md` in its most
deceptive form: they agree just enough to look like they work.

---

## Part III — The design

### D1. Widen the vocabulary (two `Expr` variants)

```rust
/// The null reference.
///
/// # What a consumer may conclude
/// `Bin(Ne, r, Null)` is the claim that `r` is non-null **at the program point
/// the carrying artifact names**, and nothing about `r` anywhere else. A
/// reference is not a number: a consumer must not read `Null` as `Int(0)` and
/// must not do arithmetic on it.
Null,

/// The length of the array `obj` refers to.
///
/// Burstall-style like `Field`: one length array indexed by the reference, so
/// `len(o)` and `len(p)` are the same cell exactly when `o = p` and aliasing
/// stays the solver's job. This is the shape both CHC encoders already
/// maintain as a ghost length.
///
/// # Strength, versus `Select`
/// `Length { obj }` is about **one reference**, as `Field` is. `Select { site }`
/// is about **every array from an allocation site**. A consumer must not read
/// one as the other.
///
/// # Partiality
/// A reference from a parameter or an unmodelled call has no known length. An
/// absent length is *unconstrained*, never zero.
Length { obj: Box<Expr> },
```

Both need an encoding in `invariant_check` (it already encodes `Select`,
`Field` and `Depth`, so the pattern exists) and in whichever engine consumes
them. `Null` is representable in LIA as a reserved constant; `Length` as an
uninterpreted array read, exactly as `Field` is.

This is the change that makes 87.5% of the open set *expressible*. It does not
make it provable; D2–D4 are about that.

### D2. Publish maps, not points — the A3 decision

```rust
/// What holds at each program point of one method, on every execution.
///
/// # Why a map and not a set of points
/// Inductiveness is a property of the map. "Holds initially" is a claim about
/// the entry; "is preserved" is a claim about every CFG edge, relating the
/// assertion at the source to the assertion at the target. Neither can be
/// stated about one assertion in isolation, which is why `check_inductive`
/// could only ever confirm "sufficient and locally preserved" — a strictly
/// weaker property that its own doc warns the caller about.
///
/// # What a consumer may conclude
/// For each `(point, formula)` entry: `formula` holds on every execution that
/// reaches `point`. An absent point carries **no** claim (`true`), not a
/// contradiction. `status: Inductive` additionally means a certifier has
/// checked initiation over the entry and preservation over every edge.
pub struct InvariantMap {
    pub id: u32,
    pub method: MethodKey,
    pub entries: BTreeMap<ProgramPoint, Expr>,
    pub status: InvStatus,
    pub scope: Scope,
}
```

`Invariant` stays. A single-point claim is still the right artifact for a
local fact, and deleting it would break `interval-ai` and the hint path for no
gain. `InvariantMap` is the unit that can be *certified*, and
`ProofKind::Invariant(id)` resolves against either.

The certifier gains its third obligation:

1. **Initiation** — `init ⟹ entries[entry]`
2. **Preservation** — for every CFG edge `p → q`: `entries[p] ∧ T(p→q) ⟹ entries[q]'`
3. **Sufficiency** — `entries[at(o)] ⟹ safety(o)`

### D3. The synthesiser is the checker, run to fixpoint

This is the part that makes the design affordable, and it is the reason to do
Houdini rather than anything cleverer first.

**Houdini** (Flanagan & Leino, *Houdini, an Annotation Assistant for ESC/Java*,
FME 2001). Start from a candidate map that assigns *every* candidate predicate
to *every* program point. Repeatedly: find an entry that fails initiation or
preservation, and delete it. Stop when nothing fails.

Three properties, all of which this design depends on:

* **Sound by construction.** The surviving map satisfies initiation and
  preservation by the loop's own termination condition. There is no separate
  "trust the synthesiser" step — a bad candidate is removed, never believed.
* **Terminates**, in at most `|points| × |pool|` deletions, because the
  candidate set only ever shrinks.
* **Order-independent.** It computes the greatest inductive map within the
  candidate lattice, so the result does not depend on which failure is found
  first. (This is Houdini's central theorem; the lattice is the powerset of
  candidate assignments under inclusion, and initiation/preservation are
  monotone in it.)

And the mechanism *is* `check_inductive`'s obligations 1 and 2, applied to a
map and iterated. So:

> **Implementing Houdini closes G4 and G3 as a side effect.** The elimination
> loop needs exactly the initiation-and-preservation checker that A3 was
> waiting for, and its output is a map that is `Inductive` by construction —
> which is what finally lets `AJAVE_CERTIFY_TRUE` be turned on.

Where Houdini is weak is also known and worth stating: it can only find
invariants expressible as a **conjunction of candidates**. It will not invent
`i*i <= n`. That is the price of soundness-by-construction and the reason the
candidate pool is where the engineering judgement goes — and why D4 draws the
pool from what the other engines already computed rather than from syntax
templates alone.

### D4. Candidate sources — one per engine, and this is why it scales

The pool is per method. Each source contributes predicates it already has, so
no engine does new analysis to participate.

| source | contributes | expressible today? |
|---|---|---|
| `interval-ai` nullness lattice | `r != Null` for each `NonNull` ref | needs **D1** |
| `interval-ai` `array_lens` / `array_len_var` | `Length{r} == v`, `0 <= i < Length{r}` | needs **D1** |
| `interval-ai` intervals | `lo <= v <= hi` | yes |
| `interval-ai` pentagons (#119) | `x < y` orderings | yes, but dropped by **G5** |
| `smt_bmc` branch guards | the conditions on the path to a loop header | yes |
| `smt_bmc` **merged-region states** | `v == ite(c, a, b)` equalities at a join | yes — **new since large-block encoding** |
| `cegar` refinement predicates | whatever the refinement loop derived | type exists, **no producer** — see below |
| `chc` / Spacer | predicates from a partial derivation | yes |
| obligation safety conditions | `safety(o)` itself, as a candidate | needs **D1** for Null/Bounds |

The last row is the cheapest and may be the highest-yield: for a NullDeref
obligation inside a loop, "the thing we want to prove" is itself the obvious
candidate invariant, and Houdini's job is just to discover whether it is
preserved.

The `cegar` row needs care. `Artifact::Precision { predicates, tracked }` is
declared and **nothing in the tree publishes it** — it is one of the four
zero-producer artifact kinds `CLAUDE.md` names as "a comment with a type". So
cegar contributing candidates means *making it a producer*, which is a separate
piece of work with its own value (it also fixes that contract defect) and
should not be assumed free. It is listed last in D5's order for that reason.

The merged-region row is the genuinely novel one. Large-block encoding computes
an *exact* `ite`-structured state at every region join and currently discards
it after continuing exploration. Those are relational equalities over several
variables — precisely what a non-relational domain cannot produce — and they
are free.

### D5. Consumption — what each engine does with an `Inductive` map

| engine | consumes as | the win |
|---|---|---|
| `smt_bmc` | assume the map at a loop header instead of unrolling | the **80** `handle_goto` tasks |
| `k-induction` | strengthening for the step case | #80, which is `status:explored` for want of exactly this |
| `cegar` | initial `Precision.predicates` | skips refinement rounds |
| `chc` | Spacer hint / initial candidate solution | the measured gap: query decided in 0.05s, inference missing |
| `imc` | auxiliary invariants | published technique (Beyer et al., *Augmenting Interpolation-Based Model Checking with Auxiliary Invariants*, 2024) |
| `interval-ai` | seed the initial state at a point | narrowing it cannot derive alone |
| `invariant_check` | the certified object | A3/A4 |

Every row is an existing engine gaining capability from an artifact it already
declares interest in, which is the test of whether this scales rather than
bolting on a ninth engine.

---

## Part IV — Contract changes required

Not optional, and listed so they are not discovered late.

1. **`core::term::Expr`** — add `Null` and `Length`, each with a "what a
   consumer may conclude" doc, per the artifact rule in `CLAUDE.md`. Every
   `match` on `Expr` must be updated; the compiler enforces this, and
   `invariant_check`'s encoder must return `None` for them until it encodes
   them, so an unencodable claim refuses a discharge rather than passing.
2. **`core::artifact`** — add `InvariantMap` and an `Interest::INVARIANT_MAP`
   bit (or reuse `INVARIANT`; reuse is wrong, because a consumer that wants
   maps does not want to be woken for every point claim).
3. **`Blackboard`** — `inductive_maps_for_method()` beside the existing
   `inductive_invariants()` (which exists and yields nothing, because nothing
   promotes), and a replacement for
   `interval_hints_for_method` that does not pattern-match one shape. The
   right interface returns the conjunction of claims at a point and lets the
   consumer interpret it, rather than silently dropping what it cannot parse.
   **A claim the consumer cannot use must be visible as such**, which is G5's
   actual lesson.
4. **`docs/contracts.md`** — Part I's four mechanical checks apply: every
   declared interest has a producer, every artifact kind has a producer *and* a
   consumer, artifact monotonicity, scope coherence. `InvariantMap` must pass
   all four on the day it lands, or it becomes the fifth unused artifact kind.
5. **`docs/README.md`** — the engine table gains the new producer.
6. **`docs/plans/codebase-health.md`** — record that A3 is decided (maps), and
   that A2's spec was wrong about initiation being checkable at a point.
7. **`docs/plans/cooperation-options.md`** — the flag and its measurement.

---

## Part V — Phased plan

Each phase is independently measurable and independently revertible. The order
is chosen so that the first phase that can fail cheaply does so first.

### P1 — Vocabulary, and nothing else (half a day)

`Expr::Null`, `Expr::Length`, their encodings in `invariant_check`, and
`interval-ai` publishing nullness and length facts as single-point
`Invariant`s alongside the bounds it already publishes.

**Validation.** `cargo test`; unit tests that `check_inductive` confirms a
hand-built `r != Null` sufficiency for a NullDeref obligation and *refuses* a
false one; `smoke --check` byte-identical, because nothing consumes the new
claims yet.

**Exit criterion.** Count the published nullness/length claims over the smoke
set. If `interval-ai` publishes few, G2 is wrong and the whole plan is
mis-targeted — stop here and re-read.

### P2 — Maps and the third obligation (one day)

`InvariantMap`, initiation and preservation over a map in `invariant_check`, an
`InvariantMapCertifier` promoting `Candidate → Inductive`, and `interval-ai`
publishing its fixpoint **as a map** (it computes one; this is a serialisation,
not new analysis).

**Validation.** A2's own fixture table, extended to maps — including the row
A2 could not express: "an invariant that holds everywhere but not at entry →
`Refuted` (initiation fails)". Then `AJAVE_CERTIFY_TRUE=1` on smoke, which
must now equal `=0`. **Any difference is the list of currently-unsound
proofs**, which is the stated exit criterion of workstream A and has never
been computable.

### P3 — Houdini (two days)

The elimination loop over a candidate pool, as its own module — not an engine,
a free function over `(Body, pool, solver)`, so it is unit-testable without a
blackboard, exactly as `check_inductive` is. Pool from D4 rows that are already
expressible plus P1's new ones. Candidates at **loop headers**, which G3 says
nobody emits.

**Validation.** Unit fixtures first: `x := 0; while (x < n) x++;` with a pool
containing `0 <= x`, `x <= n`, `x <= n-1`, `false` must yield exactly
`{0 <= x, x <= n}` and must do so regardless of pool order (that is the
order-independence theorem, and it is a test, not a comment). Then the 80
`handle_goto` tasks as the named population, measured before and after.

### P4 — Consumption, one engine at a time (one day each)

In the order of D5's expected value: `smt_bmc` loop headers first (80 tasks),
then `k-induction` (#80), then `cegar`, then `chc`.

**Validation.** Each engine separately, both properties, against the
`sv-comp.baseline` recorded at `f09f7ab`. One engine per measurement —
`docs/plans/the-outer-gate.md`'s protocol, and the reason the heap workstream
could attribute its result and the scheduler workstream could not.

---

## Part VI — What would falsify this

Stated now, because a plan with no failure condition is a wish.

* **P1's exit criterion fails.** If `interval-ai` has few nullness or length
  facts to publish, then G2 is wrong: the engines do *not* know what the corpus
  needs, and the problem is inference rather than vocabulary. Cost of finding
  out: half a day.
* **Houdini's pool never contains a preserved candidate** on the
  `handle_goto` population. Then the needed invariants are not conjunctions of
  cheap predicates, and the honest next step is a learned proposer behind the
  same channel (Loopy, Lemur — and the safety story is unchanged, because the
  checker is unchanged). Cost: P3, two days, with the pool as the only thing
  thrown away.
* **Maps are certifiable but nothing becomes `Inductive`** because preservation
  fails on edges the LIA encoder cannot express. That is the shared-encoder
  limit `invariant_check` already concedes, and it bounds this work the way it
  bounds A2.
* **`AJAVE_CERTIFY_TRUE=1` smoke stays below `=0` smoke after P2.** Then real
  discharges rest on invariants that cannot be certified, and each one is an
  issue — which is workstream A's point, not a reason to stop.

## Part VII — Why this and not the alternatives

Three other candidates were measured or considered today and are ranked below
this one, with reasons, so the choice is reviewable.

* **Java Ranger L4/L5 (multi-exit regions).** Measured dead: 24 guard clauses,
  every branch refused a merge, cost bit-identical with the encoding on or off
  (gh #129).
* **Java Ranger L3 (method-region summaries).** Measured thin: a mergeable
  callee called from K sites costs 4 solver calls at every K in {1,2,4,8}. The
  only callee worth summarising contains a loop, and summarising a loop body
  *is* this document.
* **A relational float domain (affine arithmetic, Fluctuat).** 67 points
  measured and genuinely novel for Java, but ~44 of those points are
  TRUE-direction and it is a whole new domain. It is the right *second* bet and
  it does not subsume this one; nullness and bounds are 87.5% of the open set
  and no float domain touches them.

## Theory

* Flanagan & Leino, *Houdini, an Annotation Assistant for ESC/Java*, FME 2001 —
  the elimination algorithm, its termination and order-independence.
* Cousot & Cousot, POPL 1977 — the fixpoint framework `interval-ai` already
  computes a map in.
* Garg, Löding, Madhusudan & Neider, *ICE: A Robust Framework for Learning
  Invariants*, CAV 2014 — the counterexample-guided generalisation of
  candidate-based synthesis, if P3's pool proves too weak.
* Beyer, Chien & Lee, *Augmenting Interpolation-Based Model Checking with
  Auxiliary Invariants*, 2024 — the `imc` consumption row.
* Flanagan, Leino et al., ESC/Java — the origin of the
  candidate-annotation-plus-checker split this design reuses wholesale.
