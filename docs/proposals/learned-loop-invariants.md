# Proposal: learned loop invariants over the JVM's own vocabulary

**Status:** proposed — awaiting a decision, nothing implemented
**Date:** 2026-11-22
**Measured against:** `0cb403b` (post-#132), `benchmarks/sets/sv-comp.baseline` at `f09f7ab`

## 1. The measurement that picks this, not the argument

669 points remain on the corpus. Joining each unproven task-property pair to
*its own* property's expected verdict — not, as a first pass wrongly did, to
whatever the `valid-assert` stanza said:

| | pairs | points |
|---|---|---|
| `no-runtime-exception`, expect TRUE | 134 | 268 |
| `valid-assert`, expect TRUE | 120 | 240 |
| `valid-assert`, expect FALSE | 137 | 137 |
| `no-runtime-exception`, expect FALSE | 23 | 23 |

**508 of 669 points are TRUE proofs.** The remaining ground is a proving
problem.

A blocker census over all 254 TRUE-expected pairs (`tools/blocker_census.py`,
4 workers, so read the `timeout` row with suspicion):

| bucket | tasks | pts | open obligations | responds to |
|---|---|---|---|---|
| **structural** | **69** | **138** | 1671 | an invariant, or a different cap — *not* more time |
| float-escalation | 52 | 104 | 237 | letting the FPA pass reach it (#56) |
| no-candidate | 38 | 76 | 241 | unknown — nothing published at all |
| refuted | 29 | 58 | 3 | feeding refutations back into the loop |
| theory | 25 | 50 | 58 | a different encoding |
| model | 19 | 38 | 465 | modelling the callee |
| timeout | 15 | 30 | 0 | anytime engines, partly |

Two facts from that table decide the direction. **`model` is 19 tasks of 254**,
so lifting more of `java.base` is not where the proving gap is — which was the
competing hypothesis and is now dead. And the structural bucket's blocker is

```
all_paths_complete (truncated at handle_goto, budget left)
```

— the BMC stops at a loop back edge *with budget still in hand*. No scheduler
converts that. By construction the only ways out are unrolling the loop (the
trip count is `Verifier.nondetInt()`, so there is no bound) or having an
invariant.

What the open obligations are is the final piece:

```
NullDeref  1468  (55%)      ArrayBounds  900  (34%)      — 89% of 2675
```

## 2. The mechanism is already proven to pay, on these very task families

`f26ed94` closed #105 and measured **+10**: five tasks moved from UNKNOWN to
TRUE, and the trace shows exactly how.

```
main 21ec85c:   Main.merge#18 -> Open
f26ed94:        Main.merge#18 -> Discharged { by: smt-bmc-fpa, proof: Exhaustive }
```

`interval-ai` publishes an invariant certificate; `interval_hints_for_method`
reads it into per-variable bounds; the BMC consumes them (`loaded 119 AI
interval hints`) and *completes* a search it previously truncated. So
"invariant → the BMC finishes → TRUE" is a demonstrated path in this codebase,
with a number against it.

Now look at which tasks remain in the structural bucket:

```
BellmanFord-*, InsertionSort-FunSat01/02, InsertionSort-MemSat01,
MergeSortIterative-FunSat01/02, RedBlackTree-*, Tsp-MemSat01,
Base64, HPack, BufferedBlockCipher, StrictLineReader
```

These are **sibling tasks of the five that converted**, and their open
obligations are the two kinds P1 built vocabulary for (`Expr::Null`,
`Expr::Length`). The channel works; what is missing is something to put in it
when the program has a loop. `docs/interval-ai-hint-path.md` says why nothing
is: the hint exploration runs with `Sep` (no widening), so a loop whose trip
count is not statically known never converges, `complete` is false, and
**nothing is published at all** — measured at 83 hints for a bounded loop and
**0** for `for (i = 0; i < n; i++)`.

## 3. Why the invariant engine we have does not get there

`AJAVE_HOUDINI=1` against `=0`, one build, 69 loop-heavy unproven pairs:

| | correct | unproven | WRONG | score |
|---|---|---|---|---|
| off | 5 | 64 | 0 | 10 |
| on | 5 | 64 | 0 | 10 |

Identical — the same tasks with the same verdicts, not a gain lost in noise.
The plumbing demonstrably runs, so the honest reading is that the **hypothesis
class** fails. Houdini finds conjunctions of pool members and nothing else
(Flanagan & Leino, FME 2001), and the invariant an array-bounds proof in a
counting loop needs is relational:

```java
for (int i = 0; i < n; i++) { a[i] = i; }   // needs  i < n  AND  n <= len(a)
```

No conjunction of unary bounds on `i`, `n` and `len(a)` separately says
`i < len(a)`. That is #131, with
`benchmarks/ajave/engine-ai/ALowerBoundSurvivesOnlyIfTheIncrementIsBounded` as
its minimal case.

An earlier independent measurement agrees from the other direction: the heap
work found the Horn query *decided in 0.05s* and concluded the gap is invariant
inference, not a heap model.

## 4. The adjacent fields, and precisely what each supplies

| field | result | what it supplies here |
|---|---|---|
| Program verification (Boogie/SPEC#) | Houdini — greatest conjunctive inductive map over a pool | what we have; the floor, not the ceiling |
| Invariant learning | **ICE** — a learner fed positive, negative *and implication* counterexamples, with decision-tree learners that converge to any concept expressible over the atoms | escape from conjunctions, with a convergence guarantee |
| Invariant learning | **Horn-ICE** (OOPSLA 2018) — ICE is *insufficient* when several unknown predicates at several program points interact; the samples are Horn clauses | our `InvariantMap` is per-block, i.e. already the Horn case |
| Incomplete verifiers | **Invariant synthesis for incomplete engines** (TACAS 2018) — CEGIS where a sound-but-incomplete verifier feeds back *non-provability information* | ajave already has this channel and calls it `Completeness::discharge_blocker` |
| Dynamic analysis | **Daikon** — infer likely invariants from observed executions | where positive samples come from, cheaply and in the right shape |
| Predicate abstraction | Lahiri & Qadeer, clausal predicate abstraction (CADE 2009) | the monomial case *is* Houdini; the clausal case gives implications — the cheapest possible first step |
| Property-directed learning | Sorcar — Houdini computes the *tightest* invariant, which is wasted work; target what the assertions need | how to keep the atom set tiny |

The literature's own framing matters: Houdini is not a rival of ICE but "a
prime example of an ICE learner for conjuncts". We are at the weakest point of
a family whose stronger members are well understood.

## 5. Design

### 5.1 Atoms come from the obligations, not from a pool

Houdini draws candidates from `Blackboard::candidate_conjuncts` — everything
any engine ever claimed. That is both too large and the wrong shape. Instead,
derive atoms **property-directedly** from the open obligations, whose safety
conditions are already exactly the two dominant kinds:

- `NullDeref` on reference `r` → atom `r ≠ null`
- `ArrayBounds` on `(i, a)` → atoms `0 ≤ i`, `i < len(a)`

plus, for each loop, the relations that make those provable: for an induction
variable `i` and any integer in scope `m`, the octagon-shaped atoms
`i ≤ m`, `i < m`, `m ≤ len(a)`. That is roughly 5–15 atoms per loop against
Houdini's whole-blackboard pool, and it targets 89% of the open set by
construction rather than by tuning.

**This must be derived from obligation *shape*, never from inspecting these 69
tasks.** `CLAUDE.md`'s overfitting rule applies with full force; the test is
whether the atom rule can be stated without naming a benchmark, and it can.

### 5.2 Samples are real JVM states, not solver models

An ICE learner needs concrete samples; Houdini never did. ajave can supply
them from machinery it already has — `concrete`, `concolic`, and the
`JvmReplay` certifier — by recording block-entry valuations of the atoms during
execution. This is Daikon's data source.

Why it matters beyond convenience: a sample from a real execution is a
*reachable* state, so a candidate it falsifies is definitively not invariant.
There are no false negatives to re-check, and the solver is never consulted
about a candidate that cheap evidence already kills.

Daikon's weakness is that it offers no guarantee. That is precisely what §5.3
supplies, and the combination is the point: Daikon's samples with ICE's
convergence and a sound teacher turn "likely invariants" into proved ones.

### 5.3 The teacher — and check the invariant in the *consumer's* theory

Initiation and preservation are the teacher, and `LiaEncoding` already provides
both, with the overflow guard merged in #132:

```
initiation     ¬M(entry)                              UNSAT
preservation   M(b) ∧ (T_{b→c} ∨ ovf_b) ∧ ¬M(c)′      UNSAT  for every edge b→c
```

A failed preservation query returns a model, which is a Horn-ICE sample: a
concrete `(pre, post)` pair the learner must separate. So the teacher produces
exactly the sample kind the OOPSLA'18 learner consumes — no new machinery.

**The architectural decision this proposal most wants scrutiny on.** #130 was a
wrong TRUE because the producer proved in LIA and the consumer reasoned in
bitvectors: `0 ≤ sum` is preserved by `sum = sum + 2` in unbounded arithmetic
and false on a JVM once it wraps, and the BMC used the hint to *prune*, so it
skipped the throwing path and still claimed `all_paths_complete`. The guarded
preservation theorem makes the LIA query sound, but it does so by weakening —
it admits overflow as an unconstrained transition.

For invariants destined for the **hint channel** there is a better rule:
**validate in the theory of the consumer.** The BMC is a bitvector engine and
owns a bitvector encoder; the preservation query for one candidate on one edge
is tiny. Checking it in QF_BV removes the theory mismatch rather than papering
over it, and generalises to a blackboard rule worth adopting:

> An artifact that crosses a theory boundary is validated in the theory of the
> consumer, or it carries an `Approximations` tag the consumer is obliged to
> check.

The second half already exists (`open_for(models_faithfully)`), which means the
architecture can *enforce* this instead of a comment asserting it. Concretely:
a learned invariant is published `INT_WRAPPING` unless its preservation was
discharged in bitvectors, and the hint reader consumes only untagged ones.

### 5.4 Two stages, with the first designed to be falsifiable

**Stage 1 — clausal candidates (small).** Extend `houdini.rs` from monomial to
clausal: candidates `p ⇒ q` over the §5.1 atom set, which is Lahiri & Qadeer's
clausal predicate abstraction and exactly what #131 asks for. Sound by
construction and order-independent for the same reason Houdini is. Expected to
reach `i < n ∧ n ≤ len(a) ⇒ i < len(a)`.

**Stage 2 — Horn-ICE decision trees (large).** Only if stage 1 pays. Samples
from §5.2, teacher from §5.3, learner the OOPSLA'18 polynomial-time
decision-tree algorithm over Horn samples, biased to small trees.

The staging is the point. Stage 1 is a bounded change to one existing file with
its own measurement, and it is the cheapest possible test of the central
hypothesis — "the class, not the plumbing". If stage 1 converts **0 of the 69
structural tasks**, the hypothesis is wrong and stage 2 is not justified. That
exit criterion is written down before any code, which is the discipline
`docs/measurement-validity.md` §5 argues for.

### 5.5 The consumer channel needs widening, and that is real work

`interval_hints_for_method` returns `HashMap<(BlockId, VarId), (i64, i64)>` —
**interval-shaped**. It cannot express `i < len(a)`, which is a relation
between two terms and the whole point of §5.1. So part of the cost is a
relational hint channel: either extend the map to carry `Expr` facts, or have
the BMC consume `Artifact::Invariant` formulas directly as assumptions at a
block.

The latter is cleaner and closes a standing defect: `InvariantMap` currently
has a producer and **no consumer** (`docs/contracts.md` §2). It is also where
the soundness surface lives, since the BMC asserts a hint as a fact — so this
is the part to review hardest, and the part §5.3's rule exists to protect.

A second consumer is available and deliberately *not* proposed yet: the LBE
region builder refuses `back_edge` regions (112 branches, 27% of refusals among
still-truncating tasks) because a region containing a loop has no summary. A
loop invariant is that summary. The census notes no published veritesting level
addresses this, so it is the most novel application — and exactly why it should
wait until stage 1 has shown the invariants are real.

### 5.6 Artifacts, producers, consumers

Per `CLAUDE.md`, nothing lands without both ends:

| artifact | producer | consumer |
|---|---|---|
| `StateSample` (new) | `concolic`, `concrete`, `JvmReplay` | the learner |
| `Invariant` / `InvariantMap` | the learner | the BMC's assumption channel (§5.5) |
| non-provability | `Completeness::discharge_blocker` (exists) | the learner's atom selection |

## 6. Why this is novel

Not "we implemented ICE". Four things here are, as far as I can establish, not
in the literature:

1. **A wrapping-sound teacher.** Every published ICE, Horn-ICE and
   data-driven-invariant result states its semantics over mathematical
   integers. On a JVM the oracle must survive `int` wrapping, and a learner
   with an unguarded LIA teacher does not merely lose precision — it confidently
   produces the #130 wrong TRUE, at −32. The guarded-preservation theorem
   (`docs/proposals/lia-faithfulness.md` §3) is what makes a learner safe on
   bytecode, and it was built for an unrelated reason before this was the plan.
2. **Samples from a real JVM, not from the solver.** Daikon's source with ICE's
   guarantee. Dynamic detection gives no soundness; ICE assumes a teacher that
   can always answer. Here the JVM supplies reachable states and the SMT
   teacher supplies the guarantee, and the replay certifier already exists to
   make the JVM a first-class oracle.
3. **Non-provability information from a heterogeneous portfolio.** TACAS'18
   formalises one sound-but-incomplete engine telling the learner what it could
   not prove. ajave has eleven engines, each already recording *which condition
   refused* — a strictly richer signal than that framework contemplates, and
   nobody appears to have learned from a portfolio's refusals.
4. **Invariants consumed to restrict an under-approximating search, not to
   prove.** The usual direction is invariant ⇒ proof. Here the invariant lets a
   bounded search *terminate*, which is what the +10 measured. That inverts the
   soundness obligation — an invariant used for pruning must hold in the
   consumer's theory — and yields the blackboard rule in §5.3.

The JVM-specific vocabulary is a fifth, smaller point: nullness over references
and immutable lengths via a ghost array (McCarthy/Burstall-style) rather than
numeric predicates over scalars.

## 7. What would falsify it

- **Stage 1 converts 0 of the 69 structural tasks.** Then the hypothesis "class,
  not plumbing" is wrong and stage 2 is abandoned. One measurement.
- **Samples are unavailable where it matters.** If `concolic` cannot get past the
  same loops the BMC truncates at, §5.2's sample source is empty on exactly the
  population of interest. Check before building stage 2: count block-entry
  samples obtained on the 69.
- **A learned invariant produces a wrong TRUE.** The canary already exists
  (`ALiaProvedBoundMustNotPruneABitvectorSearch`); stage 1 adds one for a
  learned implication. Any WRONG stops the work at once.

## 8. Risks

The dominant one is **a repeat of #130** — an unsound hint pruning a real path.
Mitigated by §5.3 (validate in the consumer's theory), the existing canary, and
`Blackboard::contested()`. It is worth stating plainly that this is the single
most dangerous mechanism in the tool: a hint is asserted as fact by an engine
whose conclusions are trusted, and the cost of being wrong is −32 a task.

Cost is the second: one solver query per candidate per edge per round. #131
already records the prerequisite — one persistent solver process with
`push`/`pop` and a worklist, rather than a process per query.

Third, **overfitting**. The atom templates must be justified from obligation
shape (§5.1), and the honest check is the held-out one: state the rule, then
look at what it does to tasks nobody inspected.

## 9. The cheaper things, stated honestly

This proposal is the best *capability*, not the best points-per-day:

- **float-escalation: 52 tasks, 104 points, and the theory already exists.** The
  blocker is `float_arith_approximated` — the FPA pass is in the portfolio and
  does not reach these obligations. That is a gating and scheduling question
  (#56), not a new theory, and it is very likely cheaper per point than
  anything here.
- **no-candidate: 38 tasks, 76 points, cause unknown.** Nothing published at
  all — not even a blocker. The precedent is #108, where the same bucket hid a
  defect worth +4 correct FALSE for about 80 lines. Characterising it costs an
  afternoon and might be the best trade on the board.

If the goal is the score this quarter, do those two first. If the goal is a
capability the tool does not have and that the remaining 138-point bucket
cannot be reached without, this is it.

## References

- Cormac Flanagan, K. Rustan M. Leino. *Houdini, an Annotation Assistant for
  ESC/Java.* FME 2001.
- Pranav Garg, Christof Löding, P. Madhusudan, Daniel Neider. *ICE: A Robust
  Framework for Learning Invariants.* CAV 2014.
- Pranav Garg, Daniel Neider, P. Madhusudan, Dan Roth. *Learning Invariants
  using Decision Trees and Implication Counterexamples.* POPL 2016.
- Deepak D'Souza, P. Ezudheen, Pranav Garg, P. Madhusudan, Daniel Neider.
  *Horn-ICE Learning for Synthesizing Invariants and Contracts.* OOPSLA 2018
  (PACMPL vol. 2); arXiv 1712.09418.
- Daniel Neider, Pranav Garg, P. Madhusudan, Shambwaditya Saha, Daejun Park.
  *Invariant Synthesis for Incomplete Verification Engines.* TACAS 2018; arXiv
  1712.05581. Journal version, *A Learning-Based Approach to Synthesizing
  Invariants for Incomplete Verification Engines*, JAR 64, 2020.
- Michael D. Ernst, Jake Cockrell, William G. Griswold, David Notkin.
  *Dynamically Discovering Likely Program Invariants to Support Program
  Evolution.* IEEE TSE 27(2), 2001. Tool paper: Ernst, Perkins, Guo, McCamant,
  Pacheco, Tschantz, Xiao, *The Daikon System for Dynamic Detection of Likely
  Invariants*, Science of Computer Programming 69, 2007.
- Shuvendu K. Lahiri, Shaz Qadeer. *Complexity and Algorithms for Monomial and
  Clausal Predicate Abstraction.* CADE 2009.
- Saswat Padhi, Rahul Sharma, Todd Millstein. *Data-Driven Precondition
  Inference with Learned Features.* PLDI 2016; `LoopInvGen`, SyGuS-COMP INV
  track.
- `docs/proposals/lia-faithfulness.md` §3 — the guarded preservation theorem.
- `docs/interval-ai-hint-path.md` — the channel, and why it publishes nothing
  on a loop.
- `docs/measurement-validity.md` — why the exit criterion in §7 is written
  first.
