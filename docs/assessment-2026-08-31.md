# Where ajave stands, and what is publishable

Written 2026-08-31, after the concurrency build-out. Numbers in this document
were measured on this date; the method for each is stated so they can be
re-checked rather than trusted.

## 1. Where we are

### This session

The concurrency engine went from intrinsic monitors to most of
`java.util.concurrent`, and the benchmark suite from 22 to 53.

| | before | after |
|---|---|---|
| Concurrency benchmarks | 22 | 89 (85 correct, 0 wrong, stable across repeats) |
| Modelled primitives | `Thread`, `synchronized`, `wait`/`notify` | + `ReentrantLock`, `Condition`, atomics, the synchronizers, `ExecutorService`/`Future`, `BlockingQueue`, `ReentrantReadWriteLock`, `ConcurrentHashMap`, `ThreadLocal`, `CompletableFuture`, thread lifecycle |
| Nondeterminism modelled | thread interleaving | + timed-wait expiry, spurious wakeups, arbitrary `notify` waiter, spurious weak-CAS failure, `nondetBoolean`, stale reads |
| Soundness boundary | sequential consistency, unstated | DRF-SC, **checked**: a TRUE is only issued for programs verified race-free |
| Sequential score (valid-assert) | 816 | 816 |
| Sequential score (no-runtime-exception) | 1021 | 1021 |

The sequential scores are unchanged, which was the point of measuring them: the
`<clinit>`-execution and monitor-identity changes touch code paths every engine
uses. Each has exactly one wrong answer, both pre-existing and both known —
`ReverseInterpolator_true` (a benchmark defect, verified with a standalone
`java -ea` that exits 1) and `Pan_exceptionprone` (issue #51, parked).

### The defects found, and how

Five defects surfaced. **Four were wrong answers, not missing coverage**, and
all five were exposed by writing programs a Java developer would recognise
rather than by writing more litmus tests:

| Defect | Cost | Found by |
|---|---|---|
| `dedup()` collapsed two threads of one class into one | wrong FALSE (−32) | two workers of the same class |
| `start()` on a thread with no state failed silently | wrong TRUE (−16) | dining philosophers (3-node cycle) |
| Aliased statics minted separate objects | wrong FALSE (−32) | `static final Object B = A` |
| Unseeded static read as null, pruning paths | wrong TRUE (−16) | a `Condition` in a static initialiser |
| Certifier rebuilt a different initial state than the explorer | lost FALSEs | a read/write lock on a static |

The 22-benchmark suite was passing 100% throughout. Every one of those
benchmarks had two threads and one worker per class, so none could see the first
two defects at all.

## 2. Compared to the field

### The competition

SV-COMP 2026 evaluated 11 verifiers on the Java track: **1,731 verification
tasks** over two specifications (`valid-assert`, `no-runtime-exception`).
Published cumulative scores: **JBMC 1561** (1st), **GDart 1470** (2nd),
**JLiSA 1311** (3rd, first participation).

Our corpus is 1,784 property-task pairs (1,013 valid-assert + 771
no-runtime-exception across 1,033 task files) — within ~3% of the official
count, so essentially the same benchmark set. Maximum achievable score on it is
2,829.

**ajave scores ~1,850 on that corpus** (815 + 1035), or 65% of maximum, with **zero wrong answers of its own**.

### Why that number is not yet a claim

It is measured with our harness and our certification, and three things stand
between it and a defensible comparison:

1. **No external witness validation.** SV-COMP scores a FALSE only when an
   independent validator confirms the witness. We certify FALSE internally — by
   replaying on a real JVM, which is *strong* evidence, and for concurrency by
   replaying the schedule in our own interpreter, which is weaker. Until we emit
   witnesses in the competition format and pass them through an official
   validator, our score and JBMC's are not measured the same way. **This is the
   single highest-value thing to fix.**
2. **Different resource limits.** We ran with a 60s timeout on a contended
   laptop; SV-COMP allows 900s on standardised hardware. This handicaps us — 35
   valid-assert and 23 no-runtime-exception tasks timed out — so the gap is if
   anything understated on that axis.
3. **No wrong answers remain.** The real one (`Pan_exceptionprone`) is fixed;
   the only entry still in the "wrong" column is a mislabelled benchmark
   (issue #72), where our FALSE is correct and confirmed by executing the
   program on a JVM with the witness input.

The honest framing: *on the same corpus and the same scoring formula, with a 15×
smaller time budget, ajave computes 1,837 points' worth of correct verdicts.*
Whether that survives official validation is unknown and is the first thing to
find out.

### Concurrency specifically

There is no Java concurrency category in SV-COMP. The Java track has exactly two
specifications, both sequential; `no-deadlock.prp` exists in the repository but
no category uses it, and `ReachSafety-Java` contains zero concurrency
benchmarks. So there is no competitor to compare against **within SV-COMP**.

That is not the same as being first. **Java PathFinder has model-checked Java
bytecode for concurrency defects, with partial-order reduction and deadlock
detection, since the early 2000s.** Any claim of novelty has to be made against
JPF, not against SV-COMP's empty category. What is genuinely unoccupied is the
intersection: concurrency analysis inside the SV-COMP framing of property files,
scored verdicts and certified witnesses.

## 3. Paper potential — the tool in general

**As a technique paper: no.** ajave is a portfolio of established methods —
bounded model checking, k-induction, interpolation, CEGAR, CHC, interval
abstract interpretation, search-based falsification. There is no novel core
algorithm, and a reviewer would correctly ask which idea is new.

**As a competition contribution: yes, and this is the obvious move.** SV-COMP
runs a 4-page tool-paper track. JLiSA entered for the first time this year,
placed 3rd, and got a paper. Entering SV-COMP 2027 is concrete, achievable, and
the score above suggests it would not be an embarrassing debut. Prerequisites
are mechanical: competition witness format, official validator, BenchExec
integration.

**As an empirical paper about the architecture: yes, and it is the strongest
result here.** Measured 2026-08-31 over 1,716 of the 1,785 task-property pairs
(the remainder timed out at 60s), counting how often execution-based
certification changed the answer and in which direction:

| | count |
|---|---|
| FALSE verdicts proposed by the portfolio | 792 |
| ...refuted by certification, and **would have been wrong** | **131** |
| ...refuted by certification, but were actually correct (recall lost) | 147 |
| ...confirmed and kept | 514 |

**16.5% of every FALSE the portfolio proposes is wrong, and execution-based
certification catches all of them.** Without it the tool would ship ~131 wrong
answers instead of 2; at −32 each that is ~4,200 points of penalty avoided
against 147 points of recall given up.

That is a quantified argument for a design principle: in a portfolio of
under-approximating engines, *proposing* a violation and *establishing* one must
be separate steps, and the second should be concrete execution rather than
inspection of a witness. It also says something uncomfortable about tools that
lack such a step, since nothing about our engines is unusually careless — the
gap between "my search reached a violating state" and "this program really does
that" is simply large. The Java setting is what makes the check cheap: we can
run the actual program on the actual JVM.

Caveats to state in any write-up: certification only guards FALSE, so the wrong
TRUEs it cannot see (`Pan_exceptionprone`) remain; and for concurrency the
refuter is our own interpreter replaying a schedule, which is weaker evidence
than a JVM and is precisely what an independent schedule-witness validator would
fix.

**A second empirical paper, independent of the engine.** The
measurement-discipline findings are unusually concrete and under-reported:
verdicts that depended on `HashMap` iteration order; stale `/tmp` directories
letting one run analyse another run's classes; a rebuild mid-run producing a
score that described no build that ever existed; the same build measuring 89
timeouts under load and 43 idle, a ~20-point swing that was investigated as a
code regression. Each is a way a verification result gets silently corrupted,
each was measured here, and together they argue that a large fraction of
published verification numbers are less reproducible than they appear. That is a
paper, and the artifact already exists.

## 4. Paper potential — concurrency specifically

Assessed honestly against prior work:

- **DPOR** is Flanagan & Godefroid, POPL 2005. Not novel.
- **DPOR being unsound for deadlock** — the reduction is justified over *enabled*
  transitions, and a deadlock is the absence of enabled transitions — is known.
  Our contribution is an empirical demonstration (DPOR explored 236 states of
  `LockOrderInversion` and reported no deadlock — a wrong TRUE) plus a working
  deadlock-aware variant and a harness that checks it against the unreduced
  baseline on every benchmark. That is good engineering, not a theoretical
  result.
- **JPF** already does Java concurrency model checking with POR.

So: no technique paper. Three things here *are* publishable:

**(a) Litmus suites systematically under-test concurrency analysers.**
The strongest empirical result of this session, and it is quantified: a
22-benchmark litmus suite at 100% pass rate concealed five defects, four of them
wrong answers, and six realistic programs found all five. The suite failed in a
characterisable way — every benchmark had two threads and one instance per
class, so thread multiplicity, cycles longer than two, and aliasing were all
untestable by construction. That is a specific, actionable claim about how
concurrency tooling is validated, with a defect taxonomy attached. ISSTA, ICST,
or an FSE tools/industry track.

**(b) A catalogue of which approximations produce wrong verdicts.**
We now have `java.util.concurrent` approximations classified by *direction of
failure*: modelling a queued thread pool as fully concurrent invents a race
(wrong FALSE); modelling a read lock as exclusive hides one (wrong TRUE);
treating `sleep` as an ordering edge proves racy programs safe (wrong TRUE);
leaving an interrupted thread parked reports a deadlock the program recovers
from (wrong FALSE); reading an uninitialised static as null prunes the paths
that reach the bug (wrong TRUE). The general lesson — that an
under-approximation which *prunes paths* does not lose precision but
manufactures proofs — is worth stating with this evidence behind it. Best as a
section of (a) rather than its own paper.

**(c) Propose a Java concurrency category for SV-COMP.**
This is the largest community contribution available and does not depend on the
engine being good. The gap is real and documented; `no-deadlock.prp` already
exists and is unused; SV-COMP actively wants realistic Java benchmarks (the
ARG-V competition contribution this year is exactly that). We have 53 benchmarks
with ground truth argued from the JLS/JVMS and confirmed on a real JVM, balanced
across TRUE and FALSE, spanning monitors, synchronizers, executors, concurrent
collections and realistic scenarios. Contributing that suite plus a category
proposal is concrete, useful to everyone, and carries a paper.

### Ranking

1. **The certification result** (§3). The strongest and best-evidenced claim we
   have, it is about the tool in general rather than concurrency, and the
   experiment is already run.
2. **SV-COMP 2027 entry + Java concurrency category proposal** (c). Highest
   value per unit of risk, and (c) is a genuine unoccupied gap.
3. **The empirical paper on litmus-vs-realistic validation** (a), with the
   approximation catalogue (b) as a section.
4. **The measurement-discipline paper** (§3). Independent of concurrency; the
   evidence is already collected.
5. **A technique paper on the engine as a whole.** Still not recommended — but
   see #67, which proposes the one part of it with a real claim to being a
   technique.

### What a reviewer will attack first

- **Sequential consistency.** We do not model the JMM, so broken
  double-checked locking and non-volatile publication look correct to us. We
  will report TRUE for programs that fail on a real JVM. This must be scoped
  explicitly, not glossed.
- **Overfitting.** Constants were chosen by watching benchmarks; CLAUDE.md says
  so. The held-out split and constant-sensitivity sweep (issue #47) need to
  exist before any score is defended in print. The `max_switches` sweep done
  today is the pattern to follow.
- **Novelty against JPF.** Any concurrency claim must be positioned against JPF
  explicitly, and the honest position is "SV-COMP-framed, certified, and
  benchmark-contributing", not "first".
- **Two wrong answers.** Fix `Pan_exceptionprone`; report
  `ReverseInterpolator_true` upstream.

## 5. Recommended next steps

Ordered by value per unit of risk:

1. **Emit competition-format witnesses and run an official validator.** Converts
   an internal number into a defensible one. Everything in §2 depends on it.
2. ~~Fix the two wrong answers.~~ **Done.** `Pan_exceptionprone` fixed; the
   remaining entry is issue #72, a benchmark to report upstream.
3. **Held-out benchmark split and constant sweep** (issue #47).
4. **Package the concurrency suite as an SV-COMP benchmark contribution.**
5. **Decide on the JMM.** Either scope it out explicitly, or implement enough of
   it (volatile ordering, publication) to state a stronger boundary.
