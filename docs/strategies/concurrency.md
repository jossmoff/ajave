# concurrency (engine: `ConcurrencyEngine`) — PLANNED

**Direction:** Under (falsification) initially; Over only for the bounded case
**Tier:** 2 (falsify)
**Status:** planned — not yet implemented
**Source:** n/a

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

### Phase 2 — IR and lifter

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

### Phase 4 — Bounded interleaving explorer (sequential consistency)

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

### Phase 6 — Partial-order reduction

Only now, with Phase 4 as the measured baseline. Report schedules explored
before and after; a reduction without a baseline is not a result.

Conservative dependency first: `mayAlias ∧ conflicting ∧ ¬HB`. With no alias
analysis, `mayAlias` degrades to "same field name" — coarse, but sound.

### Phase 7+ — deferred

JMM (volatile, `synchronizes-with`, final-field semantics), DPOR proper,
alias/escape analysis, `java.util.concurrent` models. Each is a project; none is
needed to answer the first benchmarks.

## Soundness boundary

Stated at each phase, never overstated. After Phase 4:

> Sound for falsification only, under sequential consistency, with a bounded
> number of context switches, over a modelled subset of `java.lang.Thread` and
> intrinsic monitors. Proves nothing about programs it does not falsify. Does
> not model the Java Memory Model.

Do not claim JMM soundness until the Phase 7 litmus tests actually pass.

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
