# Making the LIA transition relation faithful, and spending the faithfulness

Status: proposed 2026-11-22, branch `feat/lia-faithfulness`.
Predecessor: `docs/proposals/invariant-synthesis.md` (P1–P4). Gates #130, #77.

## 1. The one sentence

`invariant_check` and `houdini` reason about Java programs through
`interpolation::encode_body_lia`, and that encoding is **not** a sound
over-approximation of the JVM: in four places it is *wrong* rather than
*loose*. Every conclusion drawn from it is therefore conditional, which is why
the synthesis engine currently publishes and concludes nothing. This plan makes
the relation honest and then spends the honesty on the two things that were
blocked on it — array-length reasoning and overflow-guarded preservation.

## 2. Why "loose" is fine and "wrong" is fatal

An `Over` engine may over-approximate freely. If the encoded relation `T`
*contains* every JVM step, then "no `T`-execution reaches the error" implies
"no JVM execution reaches the error", and that is the whole soundness argument.
`encode_body_lia` already leans on this heavily and correctly:

* `models_binop` declines `Div`, `Rem` and every bitwise and shift operator,
  because SMT-LIB's `div`/`mod` are Euclidean where Java's truncate toward
  zero. `Encoder::rvalue` then allocates an unconstrained binder. That is
  *loose*: the binder admits the JVM's answer and many others.
* A heap read through a reference the encoder cannot resolve to an allocation
  site becomes an unconstrained binder. Loose.
* An unmodelled call's result becomes an unconstrained binder. Loose.
* An exceptional edge carries the clause `true`. Maximally loose.

Looseness costs precision and nothing else. The danger is the opposite
mistake — a term that *excludes* a real JVM behaviour, making `T` smaller than
the JVM's step relation. Then "unreachable in `T`" no longer implies
"unreachable on a JVM", and every proof resting on it is void.

There are exactly four such places. Three are float leaks and one is overflow.

### 2.1 Overflow (known: #77, #130)

`(+ v0 1)` in LIA is not `iadd`. `x + 1 > x` is valid in unbounded integers and
false on a JVM at `Integer.MAX_VALUE`. `smt_text::lia_overflow_cond` exists and
says so, and `encode_body_lia` routes the disjunct into `error_formulas` — so
`imc` and `cegar`, which prove *unreachability of error*, are covered: proving
`error` unreachable proves both that nothing overflowed and that the property
holds, and on an overflow-free path LIA and `iadd` agree.

`edge_clauses` — the per-edge relation that `check_map_inductive` and `houdini`
use — get nothing. So a preservation check accepts `0 <= sum` across
`sum = sum + 2`. That is exactly the wrong TRUE on
`algorithms/BellmanFord-FunUnsat01`.

### 2.2 Three float leaks

LIA has no float sort, and the encoder's response is to let float-typed values
be read as integers in three places:

| Site | What it does | Why it is wrong |
|---|---|---|
| `encode_operand` | `Const::Double(3.5)` → `encode_zero()` = `0` | A specific wrong value, not an unknown. `#77`'s own lesson: "CHC used to encode all of these as the literal `0` — not a conservative unknown but a specific wrong value, and a proof resting on it is worth nothing." |
| `LiaTheory::models_cast` | `lia_width(to) >= lia_width(from)`, and `lia_width(Float) == 32`, so `f2i` and `i2f` are "modelled" — as the identity | `(int) 3.7` is `3`. And a `Float` variable holds a *bit pattern* in this encoding, so the identity copies a bit pattern into an integer variable. |
| `Encoder::rvalue`, `Rvalue::Cmp` | unconditional `encode_cmp`, which is `(ite (< l r) -1 …)` | Comparing IEEE-754 bit patterns as signed integers is not comparing doubles: every negative double has its sign bit set. This is `jvm-floats/NaNComparisonIsAlwaysFalse`'s mechanism, and Monniaux (TOPLAS 2008) is the general warning. |

`invariant_check` screens claims that *mention* a float variable, which is why
this has not produced a wrong answer through that path. The screen is not
enough: via `f2i` or `dcmpg` a float value reaches an **integer**-typed
variable, and a claim about that variable passes the screen while resting on a
bit pattern compared as an integer. ajave's one confirmed wrong TRUE (#48,
`jvm-floats/FloatIsNotDouble`) was a float-arithmetic proof.

## 3. The theorem this plan is organised around

Let `M` map each block to a formula. Write `ovf_b` for the disjunction of
`lia_overflow_cond` over block `b`'s arithmetic — a predicate on the *pre*-state
— and `T_{b→c}` for the edge clause.

**Checks.**

* **(I) Initiation.** `¬M(entry)` is UNSAT.
* **(P) Guarded preservation.** For every edge `b → c`,
  `M(b) ∧ (T_{b→c} ∨ ovf_b) ∧ ¬M(c)′` is UNSAT.

**Theorem.** If (I) and (P) hold, every JVM-reachable state `(b, s)` satisfies
`M(b)`.

*Proof.* Induction on the JVM run.

*Base.* The entry state's parameters are unconstrained and in range, and (I)
makes `M(entry)` valid, so it holds.

*Step.* Let `(b,s) → (c,s′)` on the JVM with `s ⊨ M(b)`.

*Case 1: block `b` did not overflow.* Then `T_{b→c}` describes this step —
with §2.2's leaks closed, every remaining approximation in the encoder is loose
rather than wrong, so `T` contains the JVM step — and `(s,s′) ⊨ T_{b→c}`, hence
the disjunction. (P) gives `s′ ⊨ M(c)`.

*Case 2: block `b` overflowed.* Then `s ⊨ ovf_b`, because `ovf_b` is a
predicate on the pre-state alone. The pair `(s, s′)` therefore satisfies the
disjunction via its second disjunct — **which constrains the post-state not at
all** — so (P) gives `s′ ⊨ M(c)` again.

An exceptional step is Case 1 with the clause `true`, which constrains nothing
either. ∎

Three things to notice, because they are what makes the design hang together.

**Overflow is an exceptional edge in disguise.** That is the whole content of
the formulation. This relation says `xp = x + 1` where a JVM says
`xp = wrap(x + 1)`, so the clause describes the JVM's step only when nothing
overflowed; when something did, we know nothing about the successor beyond that
it is *some* state. The encoding already has a way to say that — an
unconstrained post-state, which is how `block.exceptional` is modelled — so
`ovf_b` goes in as a second disjunct of the transition and needs no new
machinery.

**Two other shapes are wrong, and one of them is wrong subtly.**

* `M(b) ∧ T ∧ ¬ovf_b ∧ ¬M(c)′` — *assuming* no overflow. Unsound: it proves
  the invariant of overflow-free runs and says nothing about the run that wraps.
* `M(b) ∧ T ∧ (¬M(c)′ ∨ ovf_b)` — requiring the invariant to *exclude*
  overflow. Sound, and this was the shape this plan originally specified. It is
  needlessly destructive: it deletes every candidate at the target of any edge
  whose arithmetic the source cannot bound, **including candidates that are
  valid** and therefore cannot be broken by a wrap. A tautology about a
  variable the block never touches died under it
  (`a_candidate_on_an_unincremented_variable_still_survives`). The disjunct
  form keeps those, because a valid assertion survives an unconstrained
  post-state.

**Soundness needs the three float leaks closed, and nothing else.** Every other
approximation in the encoder is loose, so the induction's "`T` contains the JVM
step" holds for it. That is the precise reason this plan is four parts and not
forty: the premise of the theorem is a finite, enumerable claim about the
encoder, and §2 enumerates it.

This is the bounded-integer discipline of Why3 (Filliâtre & Paskevich, ESOP
2013) and SPARK/GNATprove: reason in unbounded integers, and discharge a range
condition per operation. CBMC's `--signed-overflow-check` is the same idea as a
separate assertion; Bryant et al. (TACAS 2007) is the general int/bitvector
abstraction-refinement framing.

## 4. The part nobody noticed: (P) is vacuous without range axioms

LIA variables are unbounded, and the encoder never says otherwise. So on the
plan's own fixture — `x := 0; while (x < n) x++;` with candidate `0 <= x` —
guarded preservation on the back edge asks whether `x + 1 > 2147483647` is
possible given `0 <= x ∧ x < n`. In LIA, `n` may be `2^40`. It is possible, so
the candidate dies, and **the empty map is the only fixpoint for any method
containing arithmetic.**

So Part C is worthless without Part B:

> For each `Int`-typed variable, assert `-2^31 <= v <= 2^31-1`; for each `Long`,
> the 64-bit bounds. **Pre-state only.**

### Pre-state only, and this is the trap

The post-state must not be constrained, and getting this wrong conceals the
whole of Part C. The post-state is where LIA and the JVM disagree: the relation
says `xp = x + 1` where a JVM says `xp = wrap(x + 1)`, so `xp` is the JVM's
value only when nothing overflowed. Asserting `range(xp)` beside `xp = x + 1`
therefore does not state a fact — it **removes the overflowing transition from
the model**, which is the unsound "assume no overflow" arriving through the
axioms instead of through the query.

It is self-concealing, which is why it gets its own test
(`range_axioms_are_asserted_of_the_pre_state_only`). With `range(xp)` present,
`ovf` is unsatisfiable on *every* edge, so the guard silently does nothing and
`0 <= x` is "preserved" by `x := x + 1` again — and every test of the guard
passes, for the wrong reason. This was written, built and measured before being
caught by reasoning about why the counting-loop fixture still passed.

A *reference*'s post-state is unaffected: references do not wrap, so the length
non-negativity axioms are asserted of both states.

**Soundness.** Every value a JVM local of type `int` can hold is in that range
(JVMS §2.3.1), so the axiom removes no JVM state. It restricts the LIA state
space to a superset of — in fact exactly, on these coordinates — the reachable
one. An over-approximating proof over a superset is sound.

It is also a *precision gain* for initiation: `M(entry)` now only has to hold of
in-range states, which is weaker than holding of all integers.

Three deliberate omissions, each conservative:

* **Binders are not constrained.** `Encoder::binders` records a sort, not a
  width (`LiaTheory::sort_of` returns `Int` for both), so the information is not
  recoverable without changing CHC's encoder too. Unconstrained is loose, hence
  sound. And the axiom reaches a binder anyway exactly where it is justified:
  `v := binder` on an edge yields `v′ = binder ∧ range(v′)`, which bounds the
  binder because it was stored into a typed variable.
* **References are not constrained.** `Ty::Ref`/`Str` are abstract identifiers
  with `0` for null, not JVM integers. Bounding them would be a claim about a
  representation the encoding invented.
* **Array cells are not constrained.** `(select arr i)` would need a quantifier.
  Over-deletes candidates whose overflow-freedom depends on an element's range.

## 5. The capability gap: there are no ghost lengths at all

`encode_body_lia` has **no `Rvalue::ArrayLength` arm**. It falls through
`Encoder::rvalue`'s `_ => self.fresh(false)`, so:

1. two reads of `a.length` are *unrelated* integers;
2. `a.length` is unconstrained, so the JVMS guarantee `length >= 0` is absent;
3. `new int[n]` does not relate the array's length to `n`;
4. `invariant_check::render` must therefore decline `Expr::Length` — and does,
   with a comment saying exactly this.

Consequence for the predecessor plan: the interval domain publishes 1,486
length conjuncts (`ai.rs::interval_state_as_formula`), **all** of which are
dropped from Houdini's pool at `houdini.rs:124` and from the certifier. `ArrayBounds`
is 1,057 of 3,098 open obligations and `NullDeref` another 1,654; P1 built the
vocabulary for 87.5% of the open set and the encoder cannot read half of it.

### The model

One SMT array `len : (Array Int Int)`, indexed by the **reference**:
`(select len r)` is `r.length`. This is McCarthy's theory of arrays (1962)
applied the way Burstall (1972) applies it to fields, which is how Boogie, VCC,
Why3 and Dafny all encode both fields and array lengths, and it is already how
this encoder handles fields (`field_array_name`) — aliasing is the solver's
problem, and `o.f` and `p.f` are the same cell exactly when `o = p`.

Indexing by reference rather than by `AllocSite` is forced by the claim
language: `Expr::Length { obj }` is a fact about a reference. `ai.rs` says why —
"`Length{r}` is a fact about the reference and survives reassignment", unlike
`array_len_var`, which is a fact about a local and dies with it. It is also the
*truth*: two references to one array have one length, which a site-indexed model
cannot state and a reference-indexed model gets for free.

**Length is immutable.** JVMS §6.5 `newarray` takes the length as an operand and
`arraylength` returns it unchanged; nothing writes it. So the only state-threading
constraint is the identity `lenp = len`, and the only facts are at allocation:

* `(= (select len r) n)` — JVMS: the length *is* the operand.
* `(>= (select len r) 0)` — on the normal continuation. If `n < 0` the JVM
  throws `NegativeArraySizeException` and there is no array, so the normal
  successor is unreachable; the throwing behaviour stays over-approximated by
  the block's exceptional edge (clause `true`) and by the `NegArraySize`
  obligation's error formula.

Plus one ground axiom per reference-typed variable, pre and post:
`(>= (select len v) 0)`. This is the JVMS invariant for *every* live array,
instantiated finitely instead of quantified — an array-typed parameter has no
allocation site in this body, so without it nothing says a parameter's length is
non-negative. Ground instantiation rather than `∀r.` is deliberate: a quantifier
in every query risks turning `unsat` into `unknown`, which refuses the proof.

### `Expr::Depth` has the same defect and no producer

`render` emits `(select depth_C_f obj)` and **nothing declares `depth_C_f`** —
`depth_array_name` occurs twice in the tree, both in `invariant_check`. z3 reports
an unknown constant, drops that assertion, and answers on what is left (the
mechanism `interpolation.rs` documents at line ~870). The direction happens to be
conservative, but it is the exact fault the comments on `Select` and `Field` exist
to prevent. `Expr::Depth` has zero producers, so this plan makes `render` decline
it with the reason `Expr::Length` used to carry, rather than build a second ghost
model speculatively.

## 6. Design: one struct, one assembly site

The four parts add three things a preservation query must not forget: ghost
declarations, range axioms, and the overflow disjunct. The current code assembles
that query by hand in two places (`check_map_inductive`, `houdini::synthesise`),
and a third is coming (discharge). A consumer that forgets the overflow disjunct
gets the **unsound** behaviour silently.

So the data structure is changed to make forgetting impossible. `edge_clauses`
stops being a `(from, to, clause)` tuple and becomes

```rust
pub struct EdgeClause {
    pub from: BlockId,
    pub to: Option<BlockId>,
    pub clause: String,          // identical to the matching disjunct of `transition`
    pub ghost: Vec<String>,      // length threading + allocation-site equalities
    pub overflow: Option<String>,
}
```

with the query built by **one** method, `LiaEncoding::preservation_query`, which
is the only code in the tree that writes a preservation script. `houdini` and
`check_map_inductive` call it; neither can assemble it wrongly.

### What happens to `transition`

`transition` is consumed by `imc` and `cegar`. The rule inherited from the
exceptional-edge work is that per-edge information must not widen it
("Deliberately NOT added to `transition`"), and that is why `ghost` is a
separate field on `EdgeClause` rather than conjoined into `clause`, and why the
range axioms live in `LiaEncoding::edge_preamble()` rather than in
`declarations`. `edge_clauses_are_the_disjuncts_of_transition` pins the
relationship so it cannot erode.

Two parts change `transition` deliberately, and both can only *lose* proofs:

* **Part D**, the float quarantine, replaces a wrong term with an
  unconstrained binder. `imc` and `cegar` have the same hole, and this is a
  soundness fix for them too.
* **Part A**, the ghost length, replaces a fresh binder per `arraylength` read
  with `(select ghost_len a)`. This *strengthens* `transition`, and the
  strengthening is sound: for a fixed receiver the select is as unconstrained
  as the binder it replaces, so the only states removed are ones where a single
  array has two different lengths, and those are not JVM states. The
  declaration of `ghost_len` must go in `declarations` rather than
  `ghost_preamble`, because the term now appears in `transition` and an
  undeclared symbol makes z3 drop the assertion containing it — which for
  `imc` and `cegar` would silently discard the transition relation.

So the honest claim is not byte-identity but *direction*: `transition` becomes
looser where a float was being computed on, tighter-but-sound where a length is
read twice, and identical everywhere else. Both directions are measured on both
properties rather than argued.

### Alternatives rejected

* **Parallel fields on `LiaEncoding`** (`block_overflow: BTreeMap<…>`): smaller
  diff, but the failure mode of forgetting one is silent unsoundness. Rejected
  on exactly the grounds `CLAUDE.md` gives for `Bounded { k }`.
* **Site-indexed lengths.** Cannot state the claim language's `Length{r}`, and
  gets aliasing wrong in the one direction that matters.
* **Rendering `Length` pre-state-only**, exploiting immutability to skip `lenp`.
  Correct but asymmetric: the receiver is mutable even though the length is not,
  so `i < a.length` needs `ip < (select len ap)`. Threading `lenp = len` through
  the edge states the immutability as a constraint a reader can see, instead of
  as a special case a reader must infer, and it extends if `Arrays.copyOf` is
  ever modelled.
* **Switching the encoder to bitvectors.** Removes the overflow problem by
  construction, and is what CHC already does. Rejected here: it would discard the
  interpolation path (`imc` needs LIA interpolants), and the int/bv trade-off is
  a measured choice the tree has already made in both directions.
* **Quantified length axiom `∀r. len[r] >= 0`.** One assertion instead of `n`,
  but risks `unknown`, and `unknown` refuses the proof.

## 7. Work breakdown, with exit criteria

| Part | What | Exit criterion |
|---|---|---|
| **P0** | `EdgeClause` struct; `LiaEncoding::{edge_preamble, preservation_query}`; both consumers moved onto it | `edge_clauses_are_the_disjuncts_of_transition`; full suite green |
| **P1** | Float quarantine: decline float `Const`, float↔int `Cast`, float `Cmp` | A test per leak that fails on the old encoder. Measured: VA and NRE both, expecting flat-or-slightly-down |
| **P2** | Ghost lengths; `render(Expr::Length)` enabled; `render(Expr::Depth)` declines | `Expr::length` candidates survive elimination on a fixture where they should and die where they should not |
| **P3** | Range axioms in `edge_preamble` | `0 <= x` survives on the counting-loop fixture *with* P4 enabled — i.e. P3 and P4 are only meaningful together |
| **P4** | Guarded preservation via `preservation_query` | `x := x + 1` no longer preserves `0 <= x` *alone*, and does once `x < n` is in the map; a valid assertion survives an unbounded increment |
| **P5** | Minimal benchmarks for each finding, before its fix; smoke canaries | `validate_own_benchmarks.py --only` agrees with a real JVM |
| **P6** | Measure: smoke, determinism, metamorphic, ablation, then an idle A/B on both properties | 0 WRONG; no correct→unproven; decide merge |

**The honest risk, now partly measured.** P3+P4 cost precision in a shape
Houdini is already weak at. `0 <= x` in `x := 0; while (x < n) x++;` is a true
invariant whose overflow-freedom depends on the *relation* `x < n`, so it
survives only if `x < n` is itself a candidate at the loop body — which it is
in the fixture, and need not be on a corpus method. A conjunction of unary
bounds cannot express "the increment is bounded"; an implication can
(`x < n ⇒ x + 1 <= n`), which is why implication candidates after Lahiri &
Qadeer's clausal predicate abstraction are the next widening rather than a
bigger pool.

The disjunct formulation in §3 recovers the cases where this would have been
gratuitous — a valid assertion survives an unbounded increment — but it cannot
recover a bound that genuinely needs a relation. If the measured outcome is
"the map is empty on every corpus method", that is a real negative result about
conjunctive synthesis in a bounded-integer model, and it is recorded as one.

That risk is exactly why P4 is last and measured on its own, and why no
discharge path is built in this plan. Faithfulness first; spending it is the
next decision, and it should be made against a number.
