# Concurrency: parked 2026-09-01

Paused deliberately, not abandoned. It works, it is sound, and the remaining
work is capability rather than score — concurrency has no SV-COMP category, so
none of it moves the valid-assert or no-runtime-exception totals.

Everything here is measured, not estimated. Re-measure before trusting it.

## Where it got to

- **92 benchmarks, 88 correct, 0 wrong, verdicts stable across repeats.**
- **17 of 24** real-world constructs answered (71%), probed rather than assumed.
- Four properties: `valid-assert`, `no-runtime-exception`, `no-deadlock`,
  `no-data-race`.
- Cost to the sequential corpus: **nothing**. VA 815 / NRE 1035 before and
  after, because the concurrency engine handles concurrent programs itself and
  the scored corpus contains none.

The modelled surface, the deliberate refusals and the reasoning behind each are
in `docs/strategies/concurrency.md`. The mechanisms and the defects they
exposed are in `changes.md` under 2026-08-31 and 2026-09-01.

## Soundness posture

Two guarantees worth not losing:

**DRF-SC is enforced, not assumed.** The explorer only considers sequentially
consistent executions, and JLS 17.4.5 gives that guarantee to data-race-free
programs only. Race freedom is therefore checked as the *precondition of the
proof*: a program with a race is never discharged. So a TRUE from this engine is
sound under the Java Memory Model, not merely under SC.

**An engine that does not model threads may not discharge in a program that
starts them.** Enforced at the blackboard's publish gate, beside the direction
discipline. `Thread.start()` is not a call a sequential engine follows, so to
one of them the thread never runs and any obligation whose reachability depends
on another thread's writes looks unreachable — which is how smt-bmc "proved" the
canonical unsafe-publication bug.

## What is left, in the order to do it

| # | Work | Effort | Note |
|---|---|---|---|
| 1 | **#71 — models as data** | medium | **Do this first.** The four small classes below are six more hand-written models with six independent soundness arguments otherwise; as table rows they are nearly free, and #67's refinement order can then govern them |
| 2 | `LockSupport.park`/`unpark` | medium | The primitive `ReentrantLock`, the synchronizers and the queues are *all* built from. Modelling it lets several hand-written models be expressed in terms of it rather than in parallel to it |
| 3 | `ConcurrentLinkedQueue`, `CopyOnWriteArrayList`, `AtomicIntegerArray` | small each | Nearly free after 1 |
| 4 | `Phaser` | medium | Reusable barrier with dynamic parties |
| 5 | `CompletableFuture` composition | medium | `thenApply`, `supplyAsync` etc. each take a lambda a model must invoke, and `supplyAsync` spawns onto the common pool |
| 6 | `ForkJoinPool` / `RecursiveTask` | large | Genuinely large, least used. Keep refused until everything else is done |
| 7 | Weak memory beyond one stale value | research | See below |

Also open: **#63**, the schedule × input product. The branching mechanism exists;
what is missing is *candidate values* for wider nondeterministic types, which
must come from the solving engines. That is portfolio ordering — the concurrency
engine currently runs before the BMC and only once — not a missing mechanism.

## Traps for whoever picks this up

Four things cost real time here and would cost it again.

**Write the benchmark before the fix, and check it fails.** Five wrong answers
were found this way, four of which were live. One benchmark written to catch a
bug *passed against the buggy engine* because neither thread body read `this`;
it had to be rewritten until it discriminated. A regression test that passes
against the bug it was written for is worse than none.

**Litmus tests agree with their own assumptions.** A 22-benchmark suite at a
100% pass rate concealed five defects. Every benchmark had two threads and one
instance per class, so thread multiplicity, cycles longer than two, and aliasing
were untestable *by construction*. The defects appeared within minutes of
writing six realistic programs.

**The suite can be idiomatically stale.** All 92 benchmarks used anonymous inner
classes, so the fact that `new Thread(() -> ...)` was completely unanalysable
went unnoticed until it was probed for. The suite tested Java as written in 2005.

**Determinism first, then diagnosis.** A verdict that varied between identical
runs (a `HashSet` chose the search order) hid a second defect underneath it: the
race search returned at the first assertion violation. Fixing the determinism
locked in the *unlucky* outcome and made the real bug visible.

## On weak memory specifically

What landed is one narrow slice: a racing read may observe the value the location
held before the racing write. It is a *subset* of what the JMM permits, so it is
usable in one direction only — a FALSE found that way is real, and no TRUE may
rest on it.

Going further is research, and it also breaks the strongest thing this tool has:
a JMM-permitted but rare behaviour cannot be reproduced by running on a JVM, so
the replay net that refutes wrong FALSEs across the corpus is silent exactly
there. Do not start it without deciding what replaces certification.
