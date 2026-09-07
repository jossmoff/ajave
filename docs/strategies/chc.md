# chc

**Direction:** Over
**Tier:** 5
**Status:** working; array bounds provable via ghost lengths, heap contents unmodelled — see "Measured reality"
**Source:** `ajave-engines/src/chc.rs`

## What Constrained Horn Clauses are, and what they are good at

A Constrained Horn Clause is an implication

```
  P₁(x̄₁) ∧ … ∧ Pₙ(x̄ₙ) ∧ φ(x̄)  →  H(x̄)
```

where the `Pᵢ` and `H` are *uninterpreted predicates* and `φ` is a constraint
in some background theory (here linear integer arithmetic). A program is
encoded so that a solution — an interpretation of every predicate making all
clauses valid — **is** the inductive invariant that proves the program safe.
Asking a Horn solver for a model is therefore asking it to *invent the
invariant*, which is the step a human normally has to supply.

That is the whole appeal, and it says exactly where CHC belongs in a portfolio:

**CHC is the right tool for**

- **Unbounded loops.** BMC unrolls to a depth and can only report
  `Bounded { k }`; a Horn model covers every iteration.
- **Recursion, including non-linear recursion.** A method becomes a predicate
  relating arguments to result, so `ackermann` needs a *summary*, not an
  unrolling. `jayhorn-recursive` is this shape.
- **Inter-procedural proofs without inlining.** The summary is computed once
  and used at every call site, so cost does not multiply with call depth.
- **Unbounded heap data structures**, given a heap encoding (below). Proving
  "every node in this list satisfies P" needs a *quantified* invariant, which
  space invariants give implicitly.

**CHC is the wrong tool for**

- **Finding counterexamples.** It is `Over`: a model proves safety, but the
  absence of one only means *no invariant was found in the solver's language*.
  Falsification belongs to BMC and concolic.
- **Bit-level reasoning.** Solvers are far stronger over `Int` than over
  bitvectors, and Java's wrapping arithmetic is a bitvector fact (see
  "Integer semantics").
- **Floating point.** No mainstream Horn solver reasons well about FP.
- **String-heavy code.** Same.

## The encoding, following JayHorn

The reference design for Java is JayHorn (Kahsai, Kersten, Rümmer, Schäf).
Its shape, and the parts our encoder gets wrong, are worth stating precisely.

### Predicates

- One `pre_f` and `post_f` per method `f`, of arity `n` and `n + k`: the
  pre- and postcondition.
- One `pc_i` per program location. **Its arity is the method's arguments plus
  the variables live at that point**, computed by a static liveness analysis.
- One `φ_type` per class, of arity `k + 1` for `k` fields plus the object
  reference. These are *shared across methods*.

Method entry links the precondition to the first location, and each statement
becomes a transition:

```
  pre_f(x₁..xₙ)                     →  pc₁(x₁..xₙ, …)
  pcᵢ(x₁..xₙ, …) ∧ ψ                →  pcⱼ(x₁..xₙ, …)
```

Method arguments are carried through every clause, because postconditions may
refer to them. An `assert(φ)` at `pc = i` becomes two clauses:

```
  pcᵢ(x̄, ȳ) ∧ ¬φ  →  false
  pcᵢ(x̄, ȳ)       →  pcᵢ₊₁(x̄, …)
```

**Arity is not a detail.** A Horn solver must synthesise an interpretation for
every predicate, and the difficulty grows sharply with the number of arguments.
Measured here on 2026-09-06: a five-line recursive program whose summary is
`f(n) ≥ 0` timed out with 14-ary block predicates, while the same program
written over its two live variables is `sat` in 0.01s.

### The heap: space invariants, and why we do not use them

**We tried this and removed it. It is unsound as stated, and the reason is
worth writing down because the shape recurs.**

The paper's design is described first; what we do instead is in *Ghost
lengths* below.

Rather than modelling the heap as an array and hoping interpolation copes —
which it does not — JayHorn abstracts it with **space invariants**. For each
class `C` with fields `f₁..fₙ` there is a predicate `φ_C(this, f₁..fₙ,
allocSite)` describing *every* object of that class. Field access is rewritten
into two bulk operations:

- `pull(o)` — read all fields of `o` into locals: `havoc` them, then
  `assume φ_C(o, locals…)`.
- `push(o, …)` — write all fields: `assert φ_C(o, values…)`.

The Horn solver then *infers* `φ_C`, which is implicitly a quantified
invariant over unboundedly many heap cells — the thing Craig interpolation is
bad at producing directly. `pull`/`push` also cut the number of heap
interactions: the paper's example drops from six to three.

References are encoded as **tuples** `(id, type, f₀…fₙ)` carrying immutable
distinguishing features — dynamic type, final fields, and an `allocSite`
integer identifying the `new` statement that produced the object. Without
those, the solver cannot tell two objects of the same class apart and the
space invariant collapses to something useless.

### Ghost lengths: what replaced the space invariants here

A space invariant is an **uninterpreted predicate that appears in a clause
body**. A Horn solver does not merely have to satisfy such a predicate — it
*chooses its interpretation*, and nothing forces that interpretation to be
large. Choosing `φ ≡ false` makes every `assume φ(…)` unsatisfiable, so the
read path becomes infeasible, everything downstream of it becomes unreachable,
and the program is declared safe. **A vacuous proof, not a proof.**

Our encoder guarded this with a closure condition — every reachable method
lifted, no unresolved call, no havoced reference — on the theory that if
nothing can enter the heap by an unmodelled route then the write clauses
constrain `φ` adequately. That is the wrong condition and cannot be made
right: closure of the *program* says nothing about whether the *invariant* is
adequately constrained. Measured on 2026-09-07, the guard held on 28 of 169
tasks, proved none of them, and produced wrong TRUEs on
`MinePump/spec1-5_product45` and `java-ranger-regression/TCAS_prop1`.

An uninterpreted **function** `arrlen : Ref → Int` has exactly the same defect
and is worth naming, because it looks safer and is not: the solver picks its
interpretation too, and `arrlen ≡ λ_. 0` falsifies every `v = arrlen(a)`
assumption just as thoroughly.

What works is **ghost state**. Array length is the one heap quantity that
carries most of the weight — `ArrayIndexOutOfBounds` is the bulk of the
no-runtime-exception property — and it is *immutable*: JLS 10.7 fixes
`array.length` as the creation dimension. So it does not need a heap at all.
Each reference-typed variable `i` gets a shadow integer at slot `n_vars + i`:

- `v = new T[n]` writes the shadow: `len(v)′ = n`, with `n ≥ 0` from JLS
  15.10.1.
- `v = w` copies it.
- **Any other assignment to `v` invalidates it** to an unconstrained
  non-negative `int`. Getting this wrong is a soundness bug, not a precision
  one: a stale length is a wrong bounds proof.
- `v.length` *reads* the shadow as a term. It assumes nothing, which is the
  whole point.

A ghost variable is ordinary universally-quantified state, threaded across
edges like any other variable, so no interpretation the solver chooses can
make a read infeasible. It needs no closure condition, and an array we never
saw created simply has an unconstrained length — the correct
over-approximation. The shadow is live exactly when its reference is, so it
survives into loop bodies, which is where bounds are actually proved.

What this does *not* give us is field and array **contents**. Those are
unconstrained reads again. That is a real precision loss against the paper,
and it is the honest position until contents are modelled by something whose
minimal interpretation cannot be weaponised — explicit heap threading with the
theory of arrays being the standard answer.

### Exceptions

JayHorn does not special-case exceptional control flow in the clauses. It
**removes it before encoding**: a method returns a *pair* of (return value,
thrown exception), and each caller checks whether the exception is non-null
before using the value. Exceptional edges become ordinary conditional branches.

This matters here because our engine instead *declines* whenever a reachable
method has a handler, which is by far its biggest limitation (below).

### Other normalisations

- Virtual dispatch becomes an explicit switch over the dynamic type.
- All methods become static, with `this` as the first argument.
- All fields become public — the program ends up looking like type-safe C.
- Small methods are inlined first; the competition configuration used
  `-inline-size 10`.

## Integer semantics: the trap

Encoding `int` as mathematical `Int` is *not* Java. Two options, both flawed:

- **Unbounded `Int` with overflow routed to `error`.** Sound — an overflowing
  program is reported unsafe rather than proved safe — but it cannot prove any
  property that *depends* on wrapping. `jayhorn-recursive/SatAddition01`
  asserts `addition(m,n) == m + n` for inputs up to `INT_MAX`, and that holds
  **only because** Java wrapping is well-defined. Unprovable under this
  encoding, permanently.
- **Bitvectors.** Exact, but Horn solvers are dramatically weaker over them.

There is no free choice here; it is a real trade-off, recorded as #17.

Whichever is chosen, the encoding must also state that every integral variable
lies in its JLS range. Without it the solver believes an `int` can hold 2⁴⁰,
every overflow guard becomes reachable, and nothing is provable — measured
here, and it turned a timeout into `sat` on a bounded recursive program.

## Solvers

- **Spacer** (inside Z3) implements a variant of PDR/IC3.
- **Eldarica** uses CEGAR with predicate abstraction.

They fail on different things, and JayHorn's SV-COMP 2019 configuration used
**Eldarica**, not Spacer. We currently use Z3/Spacer only. Trying Eldarica on
the clauses we already generate is cheap and untested.

## Measured reality of *this* engine

The 2026-09-06 survey over 580 (task, property) records found `chc` running on
**68 of 580 (12%)** and discharging **0** obligations, with exception handlers
(157) and floats (14) the dominant declines. Both of those are fixed —
exceptional edges are encoded in both encoders, floats are havoced rather than
declined — and the picture on 2026-09-07 is different in kind.

Over the 169 no-runtime-exception tasks that need a proof, CHC's **solver ran
zero times**: 94 reached the engine and encoded nothing, because the obligation
filter admitted only `ObligationKind::Assertion` while the whole
no-runtime-exception surface is `NullDeref`/`ArrayBounds`/`ClassCast`. It was
not failing to prove; it was never asked.

With that filter lifted and the three defects below fixed, the honest summary
is:

| defect | symptom it produced | how it read before |
|---|---|---|
| fresh values as global constants | `unknown` on every affected query | "Spacer is weak" |
| entry fact as a bare conjunction | `unknown`, via a rewritten negative predicate | "Spacer is weak" |
| query clause omitting `bindings` | `unsat` on safe programs | "the heap encoding is imprecise" |
| space invariants read as empty | **wrong TRUE** | invisible behind the `unknown`s |

The third is the one that kept issue #18 open. `unsat` on a program that is
actually safe reads as "our over-approximation admits a spurious
counterexample", and the natural inference is that the *heap* is too coarse.
The real cause was that the obligation's condition — `idx >= 0 & idx < len`,
three names deep — had **none of its defining equations in the clause that
decides it**, so `error` was reachable in every such program regardless of how
the heap was modelled.

The lesson generalises past this engine: when an encoding reports a spurious
counterexample, check that the clause deciding the property actually defines
the terms it mentions, before concluding the abstraction is too coarse.

## What it assumes, and where it is unsound if the assumption breaks

`Over`, so it may discharge and may not violate. Its soundness rests on:

- Overflow reaching `error` rather than wrapping silently. Comments once
  claimed this while `INT_MIN`/`INT_MAX` were declared and never read (#77);
  the constants are now referenced by the range constraints.
- **Every unmodelled construct becoming an unconstrained value rather than a
  declined program.** Heap reads, floats, unresolved calls and the operators
  LIA lacks are all havoced. That is the safe direction for an engine that may
  only discharge: a proof over more states holds of fewer.

  This replaced a policy of *declining* such programs outright, which was
  sound but refused almost the whole corpus — one `GetStatic` anywhere in any
  reachable method used to refuse the lot.

- **Nothing the solver interprets appearing in a clause body as an
  assumption.** This is the rule the space invariants broke, and it is the one
  to check first when adding anything to this encoder. A predicate or function
  the solver interprets can be given its *minimal* interpretation, which makes
  the assumption unsatisfiable and the path vacuously safe. Facts must be
  carried as universally quantified state (ghost variables), or asserted as
  clause *heads*, never assumed from something the solver gets to choose.

- **Every clause being a well-formed Horn rule.** Three separate violations of
  this have been found here, and each masqueraded as solver weakness while
  hiding a soundness bug behind an `unknown`: fresh values emitted as global
  constants, a method entry fact emitted as a bare conjunction, and — not a
  well-formedness bug but the same shape of seam — the query clause omitting
  the `bindings` that define the values its condition is built from.

  `(get-info :reason-unknown)` names all of these directly. Run it before
  concluding that Spacer is weak.

## Known incompleteness

- Field and array **contents** are unconstrained reads (see *Ghost lengths*).
  Array **length** is exact.
- No bitwise operators — LIA has none, and `Encoder` allocates an
  unconstrained binder rather than inventing a value (#77).
- Euclidean vs truncating division.
- Floats are havoced, not modelled.
- The single-method bitvector encoder, selected when nothing resolvable is
  called, has neither ghost lengths nor exceptional-edge support parity, so
  `new int[n]` with a symbolic `n` is still unprovable there.

## How it is certified

It is not. `Certifier` has one implementation and it replays *violations*; a
CHC discharge is trusted on the strength of the direction discipline the
blackboard enforces at publish time. See `architecture.md`.
