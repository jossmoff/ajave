# Research memo: what is unexplored, and one capability already in the binary

**Status:** research notes for a decision. Nothing implemented.
**Date:** 2026-11-22
**Written after** four direction guesses in one afternoon, three of which measured
zero.

## 0. Why this memo exists

On 2026-11-22 four candidate directions were estimated and then measured:

| direction | estimate | measured |
|---|---|---|
| loop-unroll cap raised 6× | unknown | **0 of 69 structural pairs** |
| refuted witnesses reopened | +60 to +100 | **0 of 79 pairs**, violations fully suppressed |
| Horn-ICE learner over scalar atoms | +138 → +74 → +10..25 | not measured; bucket shrank three times |
| float-escalation | +50 to +70 | not yet measured |

Two of those nulls were verified to be real interventions rather than inert
ones — the suppression knob flips `1 -> Violated` to `1 -> Open`, and the cap
sweep's runtime doubles from 223s to 461s. So the nulls are information, and
what they say is consistent:

> **Every bucket in the blocker census is named after what *blocks* the verdict.
> Remove the blocker and the obligation underneath is still unprovable.**

`InsertionSort-FunSat01 [valid-assert]` is the clean case. One obligation, one
refuted witness. Suppress the witness and the obligation becomes `Open` and
nothing proves it, because the assertion is

```java
assert (data.length < 2 || data[0] < data[1]);   // after iterativeMergesort(data)
```

which needs **sortedness** — `∀i. a[i] ≤ a[i+1]` — a quantified fact about array
*contents*. Of 2675 open obligations in the TRUE-expected population, 1468 are
`NullDeref` and 900 `ArrayBounds`; the `valid-assert` half of the structural
bucket is 51 `Assertion` obligations of this functional kind. Nothing in the
portfolio can state a quantified array fact at all.

That is the real gap, and it was not what the morning's proposal addressed.

## 1. Found first, because it needs no theory: `imc` is dark on a stale premise

`interpolation.rs:78` emits, on every run:

```
imc: z3 is present but cannot interpolate (support was removed upstream);
install SMTInterpol and set AJAVE_SMTINTERPOL_JAR to enable it.
```

The workspace links cvc5 **statically, in-process** (`cvc5 = { version = "0.4",
features = ["static"] }`), `nra.rs` already uses that API
(`use cvc5::{Kind, Solver, Term as CvcTerm, TermManager}`), and the crate
exposes:

```rust
pub fn get_interpolant(&self, conj: Term) -> Option<Term<'tm>>
pub fn get_interpolant_next(&self, ...) -> ...
pub fn get_interpolant_with_grammar(&self, ...) -> ...
pub fn get_abduct(&self, conj: Term) -> Option<Term<'tm>>
pub fn get_abduct_next(&self, ...) -> ...
pub fn get_abduct_with_grammar(&self, ...) -> ...
```

So an entire engine has been inert for the reason that *one* solver lost a
feature, while the binary has linked a solver with that feature the whole time.
This is the same fault class as the silent ablation and the stale `gh #48`
pointer: a true statement about the environment, recorded once, and never
re-checked when the environment changed.

**Honest caveat, because it is not a drop-in.** Interpolation-based model
checking wants an *inductive sequence* of interpolants; `get_interpolant` gives
a binary interpolant and `get_interpolant_next` enumerates alternatives for the
same conjecture, not a sequence. SMTInterpol provides sequences directly. A
sequence can be built by iterated binary interpolation, which is standard but is
work, and the sequence property has to be checked rather than assumed. Estimated
value is unknown because `imc` has never run on this corpus — which is itself
the point: there is no measurement to appeal to, so the first step is to get one
cheaply rather than to argue.

## 2. Theory A — abduction: solve for the missing fact instead of guessing it

### The idea

Every technique tried so far *enumerates* candidate facts and filters them:
Houdini over a pool, ICE over atoms, interval widening over a domain. Abduction
inverts it. Given premises `Γ` and a goal `φ`, abductive inference finds a
simple `ψ` with

```
Γ ∧ ψ ⊨ φ        and      Γ ∧ ψ  consistent
```

So instead of asking "is this candidate inductive?", ask the solver **"what fact
is missing?"** Dillig, Dillig and Aiken built this into verification for error
diagnosis (PLDI 2012 — given a failed verification, is the program buggy or is
the report a false alarm? identifying the missing facts *is* abduction), into a
dedicated tool (`Explain`, CAV 2013 — "inference of missing preconditions, error
diagnosis"), and into loop-invariant inference (OOPSLA 2013, with Li — a
backtracking search combining Hoare-style reasoning with abduction, where a
failed verification condition makes abduction propose a new candidate
invariant). Reynolds, Barbosa, Larraz and Tinelli made it scale via enumerative
SyGuS (IJCAR 2020), and that is what cvc5 ships as `get-abduct`.

### A.1 — abduction as a *measurement instrument* (this is the novel part)

Before building any domain, run abduction over the open obligations and
**cluster the answers**. For each of the 2675 open obligations, the premises are
the path condition and the facts already published; the goal is the safety
condition. Ask cvc5 for the weakest abduct. Then count what comes back:

- abducts that are scalar relations (`i < n`, `n ≤ len(a)`) → an octagon-shaped
  domain or a clausal learner is the right build;
- abducts quantified over an index (`∀k ∈ [0,n). a[k] ≠ null`) → an array
  content domain is the right build;
- abducts about string contents → a string-lemma channel;
- obligations with **no** abduct → genuinely out of reach, and worth knowing.

That distribution is the thing nobody has measured, and it is exactly what four
failed guesses today were substitutes for. Abduction is used for diagnosis, for
invariants, and for library specifications (Zhou, Dickerson, Delaware,
Jagannathan, OOPSLA 2021); using it as a **census instrument to choose which
abstract domain to implement** does not appear in the literature.

It is also cheap in the way that matters: no new dependency, no soundness
surface (nothing is published), and it fails visibly — if cvc5 returns nothing
useful on a sample of 50 obligations, the instrument is discarded in an
afternoon.

### A.2 — abduction as an engine

The sound composition is three steps, and only the first is new:

1. **Ask.** `get_abduct` for the missing hypothesis at the obligation.
2. **Verify.** The abduct is a *candidate*, exactly like a Houdini candidate, so
   it must pass initiation and the overflow-guarded preservation query that
   `#132` merged. An abduct that is not inductive is discarded.
3. **Publish and consume.** Through the existing `Invariant` channel, which
   `f26ed94` proved pays (+10, by letting a truncated search complete).

Step 2 is the part the literature does not supply for bytecode: every abduction
result above is stated over mathematical integers, and on a JVM an abduct like
`0 ≤ sum` is false the moment the addition wraps. Without the guard, abduction
would manufacture the #130 wrong TRUE faster than Houdini could.

ajave also already has the architectural slot: `CLAUDE.md` says "an engine that
cannot proceed should `ask` rather than give up", and `Query`/`Lemma` exist for
engine-to-engine questions. Abduction makes the solver answerable to the same
channel.

## 3. Theory B — array content, which is what the measurements actually demand

Two complementary lines, both mature, neither applied to JVM bytecode here:

**FunArray** (Cousot, Cousot, Logozzo, POPL 2011) — a *segmentation functor*
that splits an array into consecutive non-overlapping segments, with the split
chosen by the analysis itself, parameterised by bound expressions, segment
abstraction and a reduction operator. Once instantiated it is fully automatic.
Implemented in Clousot/CCCheck and run over major .NET libraries, inferring
thousands of invariants at **circa 1% overhead**. That scalability record on the
closest adjacent platform to the JVM is the strongest argument available, and it
fits our existing machinery: a functor over an abstract domain is exactly what
`ajave_core::fixpoint::AbstractDomain` and the CPA substrate are for, and the
ghost-length array merged in #132 already gives segments their bounds.

**Quantified invariants via syntax-guided synthesis** (Fedyukovich, Prabhu,
Madhukar, Gupta, CAV 2019; the FreqHorn line) — use the program's syntax to see
which elements a loop touches, generalise facts about single elements into facts
about ranges, then filter with SMT. This is the direct route to sortedness, and
it composes with A.1: the abducts tell you which ranges to hypothesise about.

A caveat from the literature itself: FreqHorn is reported to struggle with
complex iteration patterns and recursive calls, which is a fair description of
`RedBlackTree` and `HPack`. So this buys the loop-shaped array code, not the
whole bucket.

## 4. Theory C — test-and-refine, with a real JVM at the frontier

**SYNERGY** (Gulavani, Henzinger, Kannan, Nori, Rajamani, FSE 2006) and its
successor **DASH** (Beckman, Nori, Rajamani, Simmons, Tetali, Thakur, ISSTA
2008, tool YOGI) unify testing and abstraction refinement: tests choose the
*frontier* of an abstract counterexample, and the algorithm then either extends
the frontier by directed testing or **refines the abstraction at the frontier**.
DASH uses test generation to decide not just where to refine but *how*, needs no
whole-program may-alias analysis, and scaled better than SLAM on 69 Windows
drivers.

This matters because it explains today's most expensive null result. We removed
a false violation and gained nothing — because nothing *refined*. DASH's claim
is precisely that the failed test is the refinement signal, not merely noise to
be deleted.

And ajave holds a signal no SV-COMP tool has: **193 witnesses refuted by a real
JVM** in this population alone. A refuted witness is a concrete proof that a
path the model believes in does not exist on the real machine — a frontier,
located by the strongest oracle available, for free. PLDI 2012's question "is
the program buggy or is this a false alarm?" is normally answered by a human or
a solver; here the JVM answers it, and then abduction can be asked for the fact
that excludes the path.

Using concrete refutation from the target machine to drive abstraction
refinement in a portfolio verifier is, as far as I can establish, unexplored.

## 5. What is actually novel, separated from what is merely new to us

| | novel? | basis |
|---|---|---|
| cvc5 interpolants reviving `imc` | no — plumbing | the capability is in the binary already |
| FunArray on JVM bytecode | weakly — a port | strong precedent on .NET at 1% overhead |
| Quantified SyGuS for sortedness | weakly | published; composes with abduction |
| **Abduction as a domain-choosing census** | **yes** | abduction is used for diagnosis and invariants, never to decide which domain to build |
| **Abduction with a wrapping-sound teacher** | **yes** | all published abduction assumes mathematical integers |
| **Refutation-by-real-machine as the refinement frontier** | **yes** | DASH's frontier, located by a JVM rather than a test generator |

## 6. What I would do first, and why it is not a build

**A.1, the abduction census.** It is the only item here that reduces uncertainty
instead of spending it. It needs no new dependency, publishes nothing so has no
soundness surface, and its output is the input every other decision on this page
needs: *which facts does the corpus actually require?* Four guesses at that
question failed today; the fifth should be measured.

Concretely: take 50 open obligations spread across the structural,
no-candidate and theory buckets, emit the premises and the goal, call
`get_abduct`, and tabulate the shape of what returns. One afternoon. If the
abducts are quantified over array indices, build Theory B and skip the scalar
learner entirely. If they are scalar relations, the morning's proposal was right
after all and its target was simply mis-sized. If nothing returns, both are
dead and that is the most valuable outcome of all.

Then, in order of expected value and independent of that result: get `imc`
running on cvc5 interpolants, because an engine that has never run on the corpus
is an unmeasured quantity rather than a known zero.

## References

- Isil Dillig, Thomas Dillig, Alex Aiken. *Automated Error Diagnosis Using
  Abductive Inference.* PLDI 2012.
- Isil Dillig, Thomas Dillig. *Explain: A Tool for Performing Abductive
  Inference.* CAV 2013.
- Isil Dillig, Thomas Dillig, Boyang Li. *Inductive Invariant Generation via
  Abductive Inference.* OOPSLA 2013.
- Andrew Reynolds, Haniel Barbosa, Daniel Larraz, Cesare Tinelli. *Scalable
  Algorithms for Abduction via Enumerative Syntax-Guided Synthesis.* IJCAR 2020,
  LNCS 12166. Shipped in cvc5 as `get-abduct` / `get-abduct-next`.
- Patrick Cousot, Radhia Cousot, Francesco Logozzo. *A Parametric Segmentation
  Functor for Fully Automatic and Scalable Array Content Analysis.* POPL 2011,
  105–118.
- Grigory Fedyukovich, Sumanth Prabhu, Kumar Madhukar, Aarti Gupta. *Quantified
  Invariants via Syntax-Guided Synthesis.* CAV 2019. Earlier: *Solving
  Constrained Horn Clauses Using Syntax and Data*, FMCAD 2018.
- Bhargav Gulavani, Thomas Henzinger, Yamini Kannan, Aditya Nori, Sriram
  Rajamani. *SYNERGY: A New Algorithm for Property Checking.* FSE 2006.
- Nels Beckman, Aditya Nori, Sriram Rajamani, Robert Simmons, Sai Tetali, Aditya
  Thakur. *Proofs from Tests.* ISSTA 2008 / IEEE TSE. Tool: YOGI.
- Zhe Zhou, Robert Dickerson, Benjamin Delaware, Suresh Jagannathan.
  *Data-Driven Abductive Inference of Library Specifications.* OOPSLA 2021.
- `docs/measurement-validity.md` — why §0's nulls were checked for inertness
  before being believed.
