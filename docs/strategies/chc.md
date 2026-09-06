# chc

**Direction:** Over
**Tier:** 5
**Status:** working, but proves nothing on the corpus — see "Measured reality"
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

### The heap: space invariants

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

From the 2026-09-06 survey over 580 (task, property) records:

| | |
|---|---|
| records where `chc` ran at all | **68 of 580 (12%)** |
| of those, obligations discharged | **0** |
| declined: reachable method has an exception handler | 157 |
| declined: reachable method uses float/double | 14 |

So there are two independent failures, and fixing either alone changes
nothing:

1. **It almost never runs.** The exception-handler guard is the dominant
   cause. That guard is correct *given the current encoding* — it was added
   after `argv-tasks/HttpTransport_false` scored a wrong TRUE, because the
   encoding follows normal control flow only, so an obligation inside a
   `catch` is unreachable and gets vacuously discharged. The fix is not to
   remove the guard but to **encode exceptions**, as JayHorn does.
2. **When it runs it proves nothing.** Predicate arity is the measured cause;
   see above. Liveness-restricted arity plus JLS range constraints moved z3
   from `unsat` (a spurious counterexample) to `unknown` (an honest "no
   invariant found") on `jayhorn-recursive`, which is progress in kind but
   still not a proof.

It also declines on heap operations entirely, where the literature's answer —
space invariants — is the single largest missing capability.

## What it assumes, and where it is unsound if the assumption breaks

`Over`, so it may discharge and may not violate. Its soundness rests on:

- Overflow reaching `error` rather than wrapping silently. Comments once
  claimed this while `INT_MIN`/`INT_MAX` were declared and never read (#77);
  the constants are now referenced by the range constraints.
- Declining every program shape the encoding does not model — heap, floats,
  unresolved calls, exception handlers. Each decline is a precision loss and
  the reason the engine is currently harmless.

## Known incompleteness

Everything it declines, plus: no quantified heap reasoning, no bitwise
operators (LIA has none, and `Encoder` allocates an unconstrained binder
instead of inventing a value — #77), and Euclidean vs truncating division.

## How it is certified

It is not. `Certifier` has one implementation and it replays *violations*; a
CHC discharge is trusted on the strength of the direction discipline the
blackboard enforces at publish time. See `architecture.md`.
