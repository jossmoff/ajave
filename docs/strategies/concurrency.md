# concurrency (engine: `ConcurrencyEngine`)

**Direction:** Under (falsification); Over only where the search is exhaustive
**Tier:** 2 (falsify)
**Status:** working — 44/46 of the concurrency suite, 0 wrong
**Source:** `ajave-engines/src/threads.rs` (thread discovery),
`concurrent_state.rs` (state model), `concurrent_exec.rs` (interpreter and
library models), `concurrency.rs` (engine, precondition checks, DPOR)

Most of the plan below is built. See **Modelled surface** for what the engine
handles today and, more importantly, what it deliberately refuses.

## Why

No Java verifier in SV-COMP 2026 handles concurrency. The Java track has exactly
two base categories:

```
Java.no-runtime-exception.Main
Java.valid-assert.Main
```

`C.Concurrency` exists — for C only. There is a `no-deadlock.prp` in
`sv-benchmarks/properties/` that no category uses, and our
`ReachSafety-Java.set` contains zero concurrency benchmarks across all 21
directories.

**So this scores zero points today.** That is the honest framing, and it should
stay in this document. The motivation is that concurrency is a real gap in Java
verification, and ajave's blackboard is unusually well suited to it: an engine
that proposes candidates and another that certifies them is exactly the shape we
already run for witnesses.

Scope is deliberately a limited subset, sequenced so each phase produces answers
we can defend rather than a large unsound engine.

## Motivating defect (verified 2026-08-28)

This program:

```java
public class Main {
  static class Boom implements Runnable {
    public void run() {
      String s = null;
      s.length();
    }
  }
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Boom());
    t.start();
    t.join();
  }
}
```

gives:

```
ajave:    TRUE
real JVM: Exception in thread "Thread-0" java.lang.NullPointerException
              at Main$Boom.run(Main.java:5)
```

`java/lang/Thread` is in `PURE_OWNERS`, so `t.start()` classifies as
`CallModel::Pure`, and the lifter rewrites it to a `Havoc` — or drops it, since
it returns void. **The thread body is never analysed at all.**

This is the same call-disappears-from-the-IR shape as issue #49. It does not
currently cost points because nothing in the scored set starts a thread, but it
is a live blind spot and the natural first thing to fix.

(Whether SV-COMP counts an exception uncaught in a *non-main* thread as
violating `G ! uncaught(RuntimeException)` is a separate question this document
does not settle. Being blind to the body is a gap either way.)

### A third certification problem: worker-thread exceptions exit 0

Measured, not assumed:

```
$ java -ea -cp . Main
Exception in thread "Thread-0" java.lang.NullPointerException: ...
        at Main$Boom.run(Main.java:19)
JVM exit code: 0
```

An exception escaping a non-main thread is printed by the default handler and
terminates only that thread. **The process still exits successfully.**

`JvmReplay` confirms a violation with
`!out.status.success() && stderr.contains(expected)` — it requires a non-zero
exit. So even with full schedule control, a concurrency witness whose exception
occurs in a worker thread would never be confirmed. The certifier would have to
also parse `Exception in thread "..."` from stderr and decide whether a
worker-thread escape counts for the property.

This bit the tooling immediately: `validate_concurrency_benchmarks.py` keyed on
exit status and reported `ThreadBodyThrows` — a program that provably throws —
as `OKx40`. Fixed to parse stderr regardless of exit code and to record which
thread raised, since main vs. worker is exactly what decides whether it is a
property violation.

Worth noting the benchmarks earned their keep before the engine exists, which
is the argument for writing them first.

## What blocks the work

Five things. None is optional; nothing above them is buildable.

### 1. `Thread` is a pure owner

As above. The fix is a contract rather than a `PURE_OWNERS` entry, so the call
survives into the IR.

### 2. Monitors are no-ops

`lift.rs`, opcodes 0xc2/0xc3: *"monitorenter / monitorexit — single-threaded:
no-ops beyond the nullcheck."* Correct for the current corpus. There is no IR
construct for a lock.

### 3. Single-entry is pervasive

`prog.entry` is `Main.main`, and `reachable_from_entry()` drives obligation
seeding, the CLI verdict guard, and the AI's method list. A thread's `run()` is
a second root; nothing in the pipeline expects more than one.

### 4. The witness cannot express a schedule

`verdict::Witness` was `nondet_sequence: Vec<i64>` plus typed entries. A
concurrency counterexample is a thread interleaving, which that cannot
represent — and a stock JVM will not deterministically replay one.

This matters more here than anywhere else. Every FALSE ajave emits today is
confirmed by `JvmReplay` actually running the program; that is what makes the
zero-wrong record mean something. A concurrency FALSE would be the first
verdict we assert on an engine's own word.

**Status: addressed.** `Witness` now carries
`schedule: Vec<ScheduleSlice>`, and `JvmReplay` returns `Inconclusive` rather
than `Refuted` for any witness that needs schedule control — refuting would be
wrong (the violation may be real) and confirming would be worse (we would not
have checked it).

#### On the witness file format

We emit SV-COMP violation witness format **2.0** (YAML: `violation_sequence`,
segments, assumption and target waypoints). Format 2.0 **does not define
concurrency violation witnesses at all** — the format paper states they "have
not yet been defined for concurrency safety".

Format **1.0** (GraphML) did: Beyer & Friedberger (2020, "Violation Witnesses
and Result Validation for Multi-Threaded Programs") annotated each automaton
transition with a `threadId` and marked creation with `createThread`.

`ScheduleSlice` is a run-length encoding of exactly that per-transition
sequence, so conversion either way is mechanical and we stay alignable with
whatever 2.0 eventually specifies.

Two consequences worth being explicit about:

- **We would be ahead of the standard.** Worth something for a paper, but it
  means there is no agreed format to target yet.
- **No external validator can check a concurrency witness we produce.** That is
  a second, independent reason certification has to be our own harness, and it
  removes the usual safety net where a third-party validator would catch us
  being wrong.

### 5. No alias, points-to or escape analysis exists

None in `ajave-engines`. The flat field abstraction added 2026-08-28
deliberately *merges* all instances of a field and ignores object identity —
the opposite of alias analysis. Any plan that says "consume alias facts" has an
unstated prerequisite that is its own project.

## Implementation plan

Ordered so the phases that unblock everything else come first. This inverts the
usual ordering, which puts exploration first and certification last.

### Phase 0 — Close the blind spot (small, do first)

Give `java/lang/Thread` a contract instead of `PURE_OWNERS` membership, so
`start()` is no longer erased. Classify `start`/`run`/`join` as
`Unexpressible`, which blocks a no-runtime-exception TRUE rather than claiming
one while never looking inside `run()`.

Turns the wrong TRUE above into UNKNOWN. Not an answer, but an honest one, and
it is the same conservative move the contract layer already makes everywhere
else.

**Exit criterion:** the motivating program returns UNKNOWN; smoke unchanged.

### Phase 1 — Certification and witness format

**Before any exploration.** Extend `Witness` with a schedule — a sequence of
`(ThreadId, steps_before_switch)` — and build a harness that replays it
deterministically.

Two options, in preference order:

1. **Deterministic scheduler in our own interpreter.** `concrete.rs` already
   executes bodies. Cheapest, and we control it — but only as trustworthy as
   that interpreter, which this session showed mismodels transcendental math
   (it agreed with NRA against the JVM).
2. **JVM instrumentation** — a Java agent enforcing the schedule at
   synchronisation points. Far more faithful, considerably more work.

Start with (1), and state plainly in this document that a concurrency FALSE is
certified by our interpreter rather than by a real JVM. That is a weaker
guarantee than every other FALSE we emit and must not be glossed.

**Exit criterion:** a hand-written racy program produces a FALSE whose schedule
replays deterministically and reproduces the failure.

### Phase 2 — IR and lifter  ✅ partially done

Done: `Stmt::MonitorEnter`/`MonitorExit` are lifted rather than discarded
(opcodes 0xc2/0xc3), and every engine declares them no-ops explicitly. Only
four exhaustive matches existed, so the blast radius was small; only two scored
benchmarks use `synchronized` and both were verified unchanged.

Still to do: multi-root reachability, volatile distinction.

### Phase 2 (original scope) — IR and lifter

- `Stmt::MonitorEnter(Operand)` / `Stmt::MonitorExit(Operand)` replacing the
  no-op at 0xc2/0xc3.
- Thread lifecycle call models (`start`, `join`) that keep the body reachable.
- Multi-root reachability: `reachable_from_entry` gains the `run()` of every
  started thread.
- Volatile accesses distinguished — the classfile parser already reads the
  access flags.

**Exit criterion:** `--ir` on a two-thread program shows both bodies, the
monitor operations, and the lifecycle calls.

### Phase 3 — Our own benchmarks, before the engine

`ajave-benchmarks/` with JVM-verified ground truth found six wrong answers the
SV-COMP corpus never surfaced. Build the concurrency litmus tests *first*:

- lock/unlock mutual exclusion
- unsynchronised counter (racy) and synchronised counter (safe)
- `volatile` visibility
- `wait`/`notify`
- `join` ordering
- lock-order-inversion deadlock
- double-checked locking

**Ground truth cannot come from running the program once** — a race need not
manifest, and a passing run proves nothing. Expected verdicts must be
established by construction and documented per benchmark, and
`validate_own_benchmarks.py` needs a distinct path for concurrent tasks rather
than its current deterministic-run check.

**Exit criterion:** ~15 benchmarks with justified expected verdicts.

### Phase 4 — Bounded interleaving explorer (sequential consistency)  🔨 in progress

Built so far:

- **`threads::discover`** resolves `new Thread(new Worker())` and
  `new MyThread()` precisely, and returns `Unresolved(reason)` for anything
  else. The direction of approximation is the important part and it is the
  opposite of the usual instinct: an Under engine that *over*-approximates the
  thread set can report a bug in a thread that never runs, so this
  under-approximates and fails closed. A unit test asserts an unresolvable
  `start()` is not reported as `Sequential`.
- **`concurrent_state`** — `ThreadState` (reentrant monitor stack, status),
  `GlobalState` (heap, monitor ownership, schedule), `Bounds`. `Blocked` and
  `Waiting` are distinct statuses because collapsing them would let the
  explorer resume a `wait()` nobody notified. Deadlock is "no thread runnable,
  not all terminated", which covers both lock-order inversion and a missed
  notify.
- **`concurrency::check_preconditions`** — three refusals, each preventing a
  specific wrong FALSE (unresolved threads, ambiguous monitor identity,
  unmodelled `java.util.concurrent` primitives). Refusals log at INFO, since
  "found no bug" and "did not look" are different claims.

Remaining: the exploration loop, which needs a concrete step function shared
with `concrete.rs`.

### Phase 4 (original scope) — Bounded interleaving explorer

A `Cpa` over `(thread states, heap, monitors)` with a bounded number of context
switches. No reduction — this is the ground truth everything later is measured
against.

Direction is **Under**: it may publish `Violated`, never `Discharged`. Bounded
exploration proves nothing.

**Exit criterion:** Phase 3's racy benchmarks return FALSE with replayable
schedules; the safe ones return UNKNOWN, not TRUE.

### Phase 5 — Candidates via the blackboard

Publish `RaceCandidate` / `DeadlockCandidate` rather than verdicts, and let
another engine establish feasibility. This reuses the propose/certify split we
already run for witnesses, and is the genuinely novel part.

Requires extending `Artifact`, which is delicate: a 2026-08-28 bug in exactly
that area — an unconfirmed violation vetoing a completed proof — silently voided
an entire category. Add candidates as a **new** artifact kind rather than
overloading `Status`.

**Exit criterion:** a deadlock benchmark produces a candidate with its wait-for
cycle.

### Phase 6 — Partial-order reduction  ✅ done

DPOR (Flanagan & Godefroid, POPL 2005) implemented in `concurrency.rs`.

The interpreter reports an `Access` per step — field read/write, monitor, or
lifecycle event — and `Access::conflicts` decides dependency: same location
with at least one write, same monitor, or a lifecycle event for that thread.
Two reads commute, which is where most of the reduction comes from.

`add_backtrack` scans **backwards** for the latest dependent transition by
another thread and adds a backtrack point there. Only the latest matters;
earlier reorderings are subsumed by it.

`Strategy::Exhaustive` is retained as the baseline DPOR is validated against —
a reduction without a baseline is not a result.

**Deliberately weaker than the paper:** the persistent-set refinement (which
threads can *reach* p) is not implemented, so a backtrack point adds every
enabled thread rather than the minimal set. That over-explores and never
under-explores: it costs time, not soundness. Source-DPOR, sleep sets and
wakeup trees are the natural next steps and are measurable against this.

The reduction is what made a higher preemption bound affordable (3 -> 10),
which is what let `SynchronizedCounter` be covered at all.

### DPOR is not sound for deadlock detection

Worth stating plainly, because it is easy to assume one explorer serves every
property.

DPOR's reduction is justified by reasoning over **enabled** transitions: two
independent enabled transitions commute, so exploring one order represents
both. A deadlock is a state in which *nothing* is enabled, reached by threads
blocking on one another — and the interleaving that produces it can be exactly
the one the reduction discards, because the blocking transitions never entered
an enabled set to be compared.

Measured, not assumed: DPOR explored 236 states of `LockOrderInversion` and
reported **no deadlock**, which is a wrong TRUE for `no-deadlock.prp`. The same
program under `Strategy::Exhaustive` reports FALSE correctly.

So the no-deadlock property uses the unreduced explorer. This is the concrete
reason the exhaustive baseline is kept rather than deleted once DPOR worked —
it is not only a validation aid, it is load-bearing for one property.

Making DPOR deadlock-aware (including blocked transitions in the backtrack
computation) is the real fix and is the natural next piece of work.

### The no-deadlock property

SV-COMP already defines it — `CHECK( init(Main.main()), LTL(G !deadlock) )` in
`sv-benchmarks/properties/no-deadlock.prp` — and the Java track simply has no
category using it. We support that file verbatim rather than inventing our own.

It is answered **outside the obligation system**. Every other property is a
condition at a program point, which is what an `Obligation` is; a deadlock is a
property of the *execution*. Forcing it into the obligation model would mean
seeding a synthetic obligation against the entry method that no engine but this
one could discharge, which buys nothing and obscures the claim. `--property
no-deadlock` therefore calls the explorer directly:

| Exploration result | Verdict |
|---|---|
| `Deadlock` | FALSE |
| `ExhaustiveNoViolation` (no bound hit) | TRUE |
| `Incomplete` or a refusal | UNKNOWN |

Monitor identity also needed refining for this: `l.a` and `l.b` are both
`java.lang.Object`, so allocation-site-per-class identity called them ambiguous
and refused. A monitor loaded from a field now uses the **field** as identity,
which is sound when that field is written exactly once program-wide — precisely
the `final Object a = new Object()` idiom these benchmarks use.

### Bugs this phase surfaced

Worth recording, because each was a wrong FALSE waiting to happen:

- **`synchronized` methods were invisible.** `synchronized void inc()` is the
  `ACC_SYNCHRONIZED` access flag, not `monitorenter`/`monitorexit` bytecode —
  the JVM takes the monitor as part of invocation. A lifter watching only for
  the opcodes saw an unlocked method and the explorer reported a data race
  that cannot happen. The lifter now makes the implicit lock explicit
  (acquire on entry, release before every return). Static synchronized methods
  lock the class object, which we do not model, so they are left alone rather
  than locked against the wrong thing.
- **The bound counted switches, not preemptions.** Qadeer & Rehof's result is
  about preemptions — interrupting a thread that *could* have continued. A
  switch away from a blocked or terminated thread is forced, and counting it
  burned the whole budget on ordinary start/join sequences.
- **Sequential engines poison threaded programs.** `concrete` reports
  `JoinOrdersWrite`'s assertion as violated, because `t.start()` is a no-op to
  it and the joined write never happens. Replay refutes the witness, but the
  refuted candidate still vetoed the concurrency engine's proof. Fixed by
  discharging over `open_or_unconfirmed()` — the same fix as the blackboard
  ordering bug of 2026-08-28.
- **`this` for a worker must be the object main allocated.** Fabricating a
  fresh identity made the thread write to a different object than main read,
  which looked exactly like a missing happens-before edge.
- **Parameters bind by JVM slot, not argument index.** The lifter assigns
  VarIds in its own order. Binding `VarId(i)` to the i'th argument silently
  wired parameters to unrelated locals; the tell was violations appearing on
  1-slice schedules, i.e. with no interleaving at all.

### Phase 7+ — deferred

JMM (volatile, `synchronizes-with`, final-field semantics), DPOR proper,
alias/escape analysis, `java.util.concurrent` models. Each is a project; none is
needed to answer the first benchmarks.

## Modelled surface

What follows is the state as of 2026-08-31. The refusals matter as much as the
features: every one of them is a place where an approximation would have been
easy and wrong, and the engine answers UNKNOWN instead.

### Threads

| Feature | Status |
|---|---|
| `Thread.start` / `join` | modelled; `join` is a happens-before edge |
| Thread identity | one per construction, body resolved at `start()` from the Runnable object's class |
| `Thread.sleep` / `yield` / `onSpinWait` | modelled as no-ops — they order nothing |
| `Thread.isAlive` / `currentThread` | modelled |
| `Thread.interrupt` / `isInterrupted` | flag only; **refused** when the target is parked |
| `Runnable` via subclassing or delegation | both |
| `new Thread(null)` | **refused** |

### Locks and conditions

| Feature | Status |
|---|---|
| `synchronized` blocks and methods, reentrancy | modelled |
| `Object.wait` / `notify` / `notifyAll` | modelled, including full monitor release and restore (JLS 17.2.1) |
| `ReentrantLock` lock/unlock/tryLock/isLocked | modelled |
| `Condition` await/signal/signalAll | modelled |
| Timed `await`, `lockInterruptibly`, fairness | **refused** |
| `ReentrantReadWriteLock` | **refused** |

### java.util.concurrent

| Feature | Status |
|---|---|
| `CountDownLatch` await/countDown/getCount | modelled |
| `Semaphore` acquire/release/tryAcquire | modelled |
| `CyclicBarrier` await/getParties | modelled; barrier action **refused** |
| Scalar atomics, including CAS | modelled, one transition per operation |
| `ExecutorService` execute/submit/shutdown/awaitTermination | modelled |
| `Future` get/isDone | modelled; `cancel` **refused** |
| Pool with fewer workers than tasks | **refused** — see below |
| `Phaser`, `ForkJoinPool`, `CompletableFuture`, `AtomicReference` | **refused** |
| Timed `await`, `submit(Callable)` | **refused** |

### Why those refusals are refusals

Each one is a case where the cheap approximation produces a *wrong verdict*
rather than a lost proof:

- **A pool with fewer workers than tasks** runs some tasks one after another.
  Treating every task as concurrently runnable invents interleavings the JVM
  cannot produce — for two increments, the one where both read 0. That is a
  wrong FALSE at −32.
- **Interrupting a parked thread** must throw `InterruptedException` and resume.
  Setting a flag and leaving it parked reports a deadlock the program recovers
  from: another wrong FALSE.
- **Timed waits** can return false on expiry, which we cannot decide; assuming
  they never expire proves programs that hang.
- **A barrier action** must run on the tripping thread, which means pushing a
  frame from inside a library model.

### The invariant that holds the interpreter together

A modelled call must not touch its own program counter. `advance` steps past the
statement afterwards, unless the call parked the thread — which it detects from
the thread status, the single source of truth for parking.

Both directions of violating this caused real bugs. `Stmt::Assign` stores a
returned value only while the frame has not moved, so a model that advanced
first silently dropped its own result (`tryLock`'s boolean, `incrementAndGet`'s
count, `Future.get`'s value). A model that parked *and* advanced sent the thread
past the call it was blocked on — walking a blocked `lock()` into the critical
section unlocked.

### Object identity

Monitor identity is concrete: a monitor operand evaluates to the `ObjId` of the
`new` that actually ran, so two `new Account(...)` are two monitors by
construction. There is no allocation-site abstraction and no need for one. The
only guard is that reference 0 — null, and how an untracked object reads — is
refused as a monitor, since it is the one value that could collapse two distinct
monitors into one.

Class initialisers are **executed**, not pattern-matched. Guessing them was
worth two wrong answers: aliased statics minted separate objects (inventing an
AB/BA deadlock between a lock and itself), and a static initialised by a factory
call read as null, whose null-check pruned every path reaching it and turned a
real deadlock into a proof.

## Soundness boundary

Stated at each phase, never overstated. As of 2026-08-31:

> Sound for falsification under **sequential consistency**, over the modelled
> subset above, within the context-switch, state and depth bounds. A TRUE is
> claimed only when the search completed within every bound; hitting any bound
> yields UNKNOWN. Does not model the Java Memory Model.

Do not claim JMM soundness until the Phase 7 litmus tests actually pass.

**The SC assumption is the largest remaining gap, and it is one-directional.**
Under SC we cannot see bugs that need reordering: broken double-checked locking,
and publication through a non-volatile field, both *look* correct to this engine.
It will therefore report TRUE for some programs that fail on a real JVM. No such
benchmark is in the suite, because adding one we knowingly answer wrongly would
put a wrong answer in a suite whose value is that it has none — the gap is
recorded here instead.

## Notes on the source proposal

Derived from `concurrency-prop.md` (another agent's proposal), which is a
reasonable research roadmap but was written without reference to the codebase —
its examples are Java rather than Rust, and its Phase 6 ("consume alias,
points-to, thread-locality, escape") depends on analyses ajave does not have.

Kept from it: the blackboard propose/certify split, semantic events over
bytecode, conservative dependency first, and an explicit soundness boundary per
phase.

Changed: certification moved to the front, because a concurrency counterexample
cannot be certified by the mechanism that makes every other ajave FALSE
trustworthy — the proposal does not mention this at all. IR and lifter work
promoted to a real phase rather than assumed. Alias-dependent reduction pushed
behind its prerequisite.
