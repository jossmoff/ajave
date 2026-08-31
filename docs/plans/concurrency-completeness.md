# Concurrency completeness: five mechanisms, not thirty features

Written 2026-08-31. The unsupported list reads as about thirty separate
features. It is not: almost every entry is a symptom of one of **five missing
mechanisms**. Building the mechanisms closes the features in batches; building
the features one at a time would produce thirty special cases and a `do_call`
nobody can reason about.

Everything below preserves the standing invariants: benchmark first (a minimal
program that reproduces, added *before* the fix), zero wrong answers at every
step, DPOR and exhaustive agreeing on every decided verdict, and smoke plus
`--set ajave` clean before each commit.

---

## The five mechanisms

### M1 — Choice points: the explorer branches on more than thread order

**Today** the explorer's only nondeterminism is *which thread runs next*. Every
other choice has to be refused.

**Symptoms it explains**
- Every timed operation: timed `await` (latch, barrier, `Condition`), timed
  `poll`, timed `tryLock`, `awaitTermination`. All refused for one reason — a
  timeout may or may not expire, and we cannot decide which.
- Issue **#63** (`ScheduleAndInputBoth`): violations needing both a specific
  interleaving *and* specific input values are unreachable, because the explorer
  cannot branch on an input.
- `Semaphore.tryAcquire`, `Thread.isInterrupted` polling, and anything else
  whose result is a scheduling artefact rather than a computed value.

**The mechanism.** A general `choose(n)` in the interpreter that the explorer
treats as a branch point, exactly as it treats an enabled-thread set. A timed
operation becomes `if choose(2) { /* as untimed */ } else { /* timed out */ }`.
Both outcomes are permitted by a real JVM, so branching is sound *and* complete
where refusing was merely safe.

**Why first.** It is the smallest of the five, it is additive rather than a
refactor, it closes an open issue and one of our two remaining unproven
benchmarks, and it is the same machinery M5 needs later (a read branching over
the writes it may observe is a choice point). Building it now means M5 is an
extension rather than a second mechanism.

**Cost.** State space. Each timed call multiplies the search, so timed
operations should be modelled but not gratuitous, and `max_states` becomes load
bearing.

---

### M2 — Exception handling in the concurrent interpreter

**Today** there is none. `Terminator::Throw` sets the thread to `Terminated` and
stops; the IR's `! exc: * -> bb` edges are never followed. `try`/`finally`
around a lock works only because nothing on the normal path throws.

**Symptoms it explains**
- `interrupt()` of a parked thread — must throw `InterruptedException` and
  resume. Refused today because a model cannot raise.
- `Future.cancel`, `add()` on a full queue (`IllegalStateException`),
  `IllegalMonitorStateException` on unbalanced `unlock`, `BrokenBarrierException`.
- Any library member whose contract is "throws on this input" — which is most of
  the interesting ones.
- Exception-carrying control flow *inside* threads generally: a worker that
  throws currently terminates silently rather than running its handlers.

**The mechanism.** Follow the exception edges the lifter already emits: on a
raise, walk the frame stack for a handler whose range covers the current
program point and whose caught type matches, bind the exception object, and jump.
Then let a model return `Raise(class)` instead of a value.

**Why second.** M1 does not need it, but M3 does — dynamically created threads
that throw must behave — and it is independently valuable. It is also the
mechanism that makes the *existing* `try`/`finally` lock benchmarks faithful
rather than accidentally correct.

---

### M3 — Threads created dynamically, not discovered statically

**Today** `threads.rs` pattern-matches `Thread.<init>` and `start()` inside a
single method body, traces the Runnable to an allocation, and pre-allocates one
`ThreadState` per *construction site*. The interpreter then binds the body at
`start()` from the object's real class — which is the tell: **identity is
already dynamic, only the allocation is static.**

**Symptoms it explains** — all six thread-shape gaps at once:
- `class W extends Thread` — the implicit `super()` in `W.<init>` has receiver
  `this`, which is not an allocation *in that method*. This is idiomatic Java and
  is currently refused.
- Threads created in a **loop** — one construction site, N runtime threads, so
  the second `start()` finds no state.
- Threads from a **factory method**, from a **field**, from a **collection**, or
  passed as a **parameter**.
- Thread pools with fewer workers than tasks: the work queue needs threads that
  outlive one task.

**The mechanism.** Delete the pre-allocation. Create a `ThreadState` and frame at
`start()`/`submit()` from the receiver's concrete class, append to
`g.threads`, and bound the count at runtime against `max_threads`. `frames`
becomes keyed by thread id rather than indexed by position.

**Why third, not first.** It is the highest-value change and the riskiest: thread
identity is load-bearing for DPOR's enabled sets, for the per-branch state
restore, for vector clocks, and for `replay_schedule`. Doing it after M1 and M2
means the benchmark suite that must catch a regression is at its strongest, and
the two mechanisms it might otherwise have to work around already exist.

`threads.rs` does not disappear entirely: a static *upper bound* on thread count
is still wanted for the `max_threads` precondition, but it becomes an estimate
rather than an allocation, and being wrong costs nothing.

---

### M4 — Library models as data

**Today** `do_call` is a ~2000-line function of hand-written match arms. Every
new class is more of it, and every arm is an independent soundness commitment
with no shared vocabulary.

**Symptoms it explains**
- `ConcurrentHashMap`, `CopyOnWriteArrayList`, `ConcurrentLinkedQueue` — the
  concurrent collections other than `BlockingQueue`.
- `ThreadLocal`, `Exchanger`, `StampedLock`, `Phaser`, `CompletableFuture`,
  `ForkJoinPool`.
- The `Executors` factories we do not cover.

**The mechanism.** A small effect vocabulary — *release*, *acquire*, *park until
predicate*, *cell read/write*, *container insert/remove*, *raise* — and each
class expressed as a table over it. Most of the remaining classes are then a few
rows rather than a few hundred lines.

This is the same direction as issue **#67**: a declarative model with a
refinement order and mechanically checked consumer monotonicity. M4 supplies the
vocabulary that #67 orders. Doing them together is what turns "we wrote a lot of
models" into "library models are a checked artefact".

**Why fourth.** It is a refactor, and refactors want a stable base. After M1–M3
the shape of what a model needs to express is known; before them it would be
guessed.

---

### M5 — Weak memory

**Today** the explorer considers only sequentially consistent executions, and the
DRF-SC gate makes that honest: a TRUE is only issued for programs verified
race-free. Racy programs are *declined*, not analysed.

**Symptoms it explains**
- Broken double-checked locking, publication through a non-volatile field: bugs
  that require reordering to manifest. We decline them; we do not find them.
- 64-bit tearing of non-volatile `long`/`double`.
- Final-field freeze semantics.

**The mechanism.** A read becomes a choice point over the writes it may observe
(M1 supplies the branching), constrained by happens-before (already built, as a
relation, precisely so it survives this change).

**Why last, and why it may not land.** Two hard problems beyond the search:

1. **Which model.** Implementing JLS ch.17 faithfully — the committed-execution
   and causality rules — is a research project on its own, and the model is known
   to be subtly wrong in ways that prohibit legal compiler optimisations. The
   tractable target is a sound over-approximation, which trades false alarms for
   coverage and therefore needs certification more than ever.
2. **Certification stops working.** A JMM-permitted but rare behaviour cannot be
   reproduced by running on a JVM, so the replay net that refutes 131 wrong
   FALSEs across the corpus is silent exactly here. Every violation M5 finds is
   uncertified by construction.

**Recommendation: scope M5 out of "implement everything" and treat it as a
separate decision.** M1–M4 close every gap that is engineering. M5 is the one
that is research, and it is also the one that weakens the property the tool is
best at — not shipping wrong answers.

---

## Sequencing

| Phase | Mechanism | Status |
|---|---|---|
| 1 | Choice points | **done** (#68 closed) |
| 2 | Exceptions | **done** (#69 closed) |
| 3 | Dynamic threads | **done** (#70 closed) |
| 4 | Models as data | **coverage done**, refactor open (#71) |
| 5 | Weak memory | **stale reads done**; the rest remains research |

### What actually landed, against what was planned

Phases 1–3 landed as designed. Two caveats worth keeping honest:

**Phase 4 delivered the coverage, not the refactor.** `ConcurrentHashMap`,
`ThreadLocal` and `CompletableFuture` are modelled, but `do_call` is still a long
match rather than a table over an effect vocabulary. The refactor is the part
that makes the *next* ten classes cheap and that #67 needs to order, so #71 stays
open for it. `Phaser` and `ForkJoinPool` are still refused.

**Phase 5 was scoped out and then partly done anyway.** The recommendation was to
treat weak memory as a separate decision, because it is research and because it
weakens certification. What landed is the narrow, one-directional slice: a racing
read may observe the value the location held before the racing write. That is a
subset of what the JMM permits, so a FALSE found this way is real while no TRUE
may rest on it — and it is enough to find unsafe publication, which is *correct
under sequential consistency* and so unreachable by interleaving search.

The full model — reordering a thread's own writes, multiple stale values,
committed executions — is not attempted, and the certification asymmetry stands:
a JMM-permitted rare behaviour cannot be reproduced on a JVM, so the replay net
is silent exactly there.

Bounds (`max_threads: 4`) are raised as part of phase 3, since a dynamic thread
count is what makes the bound meaningful rather than structural.

## Invariants

1. A minimal benchmark reproducing the gap is added **before** the fix.
2. Zero wrong answers, checked on `--set ajave` and `--set smoke`, every commit.
3. `dpor_equivalence.py` reports zero disagreements.
4. Any new approximation is classified by *direction of failure* before it lands:
   precision loss is acceptable, verdict flip is not. Refuse instead.
5. New bounds and constants get a sensitivity sweep, per CLAUDE.md.
