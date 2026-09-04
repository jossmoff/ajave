# Notable Techniques and Contributions

Noteworthy implementation details, design decisions, and novel techniques that may be worth discussing in a paper.

## 2026-09-04 — engines that ask, and what asking is actually good for

The blackboard was being used as a mailbox. Four of five artifact kinds had zero
producers, `Blackboard::since` had zero consumers, and ten of eleven engines
took `_budget` and ignored it. Every artifact was an *answer*, so an engine that
got stuck had exactly one move: give up on the obligation, conservatively, and
discard everything it had established. When the BMC meets `Math.sin(x)` it knows
`x` is constrained and the path feasible, and throws all of it away — not
because the information is unavailable, but because there was nobody to ask.

`Artifact::Query` and `Artifact::Lemma` close that, on top of a shared term
language (`core::term::Expr`) whose absence explains three of the four dead
artifact kinds. The publish rule mirrors `Direction` one level down:
`Bounds`/`Holds` are claims about every execution and need `Over`;
`SatisfiedBy`/`RefutedBy` are about one and need `Under`.

### Three blockers, all the same mistake

Closing the loop end to end needed three fixes, and each was a component
declaring itself finished while work remained:

1. **The answerer retired in round 0.** `ranges` returned `Exhausted` when
   nobody had asked yet, and the orchestrator retires an engine that says it is
   finished. "Nothing to do yet" and "nothing to do ever" are different answers,
   and only the engine knows which it means.
2. **The asker would not re-enter.** Gated on `bb.open()` — but an
   unconstrained `Math.sin` lets the solver claim `sin(x) > 2`, so the pass had
   *closed* the very obligation the answer would settle. The same trap the FPA
   pass fell into, fixed the same way: gate on
   `open_for(UNMODELLED_CALL)`.
3. **The orchestrator ended the run.** `open == 0` meant Report, so a pending
   question could not survive to the next round.

Fixing (2) also repaired something from earlier the same day: `UNMODELLED_CALL`
had been declared on `Rvalue::Havoc` and never fired, because `Math.sin` lifts
to a `Call` and reaches a different path. That is why the first attempt at it
measured no change at all.

### The negative result, which is the valuable part

The loop works. It does not pay.

```
smoke           121 correct / 153  ->  120 correct / 152
float category   56 correct /  59  ->   56 correct /  59
```

`MathHelper_true`, dense in `Math` calls, went from 7.6s to a 60s timeout: many
queries, so a full second exploration, for nothing.

The reason is worth stating precisely, because it says where the channel *does*
pay. A range does not make a path through an unmodelled call **trusted**. The
obligation is still refused with `skipped_obligation` because the path is
tainted, and taint blocks the check independently of whether a branch was
pruned. Bounding a value you cannot model leaves it unmodelled.

**So the query channel pays when an answerer can supply a *value*, not when it
can only bound one.** Lifting `FdLibm` — where `Math.sin` becomes ordinary
double arithmetic — would qualify. A range table does not. The channel is right;
`ranges` was the wrong first answerer.

Asking is therefore behind `AJAVE_ASK=1`, default off, so the next answerer has
somewhere to plug in and the measurement can be repeated rather than re-argued.
That leaves `Query`/`Lemma` with no default producer, which contradicts the rule
added to `CLAUDE.md` the same day. The rule stands and gains a clause: an
artifact kind no engine produces by default is **unfinished**, and must be
recorded as such rather than left to look complete.

### Also landed

A sound pruning rule that survives independently of the above. A tainted branch
condition may not be *imposed* — a witness derived from it would be about a
different program — but it can be *asked about*. If it is unsatisfiable given
only sound facts, no execution takes it, whatever the unmodelled value turns out
to be. Asked and immediately retracted, so nothing downstream inherits a
constraint over an untrusted value.

## 2026-09-04 — the operand stack had no types, and that was hiding the float gap

`float-nonlinear-calculation` scored 40 of a possible 99 and looked like a
search problem: 87 tasks built from `Math.sin`/`cos`/`pow`/`sqrt`, which no SMT
theory can express. The obvious reading was that our Alternating-Variable-Method
searcher was not strong enough, and the obvious next step was to import more of
the Concolic Walk algorithm.

That reading was wrong. The searcher was finding the answers and then being
handed a broken program to evaluate them on.

### The defect

`Lifter::stack_slot(depth)` allocated **one `VarId` per operand-stack depth,
with a hardcoded `Ty::Int`**, and `spill()` — which materialises the abstract
stack whenever control leaves a block — built its temps the same way. So any
value that crossed a basic-block boundary on the operand stack was recorded in
`body.vars` as an int, whatever it actually was. A call ends a block, so
`Math.f(..) op Math.g(..)` hits this every single time.

Nothing then reports an error. Every consumer that asks the IR for an operand's
type simply gets the wrong answer:

- `concrete::is_float_operand` chooses between real `f64` arithmetic and the
  integer path, so `dmul` became an **i64 multiply of the two bit patterns**;
- `smt_bmc::fp_width_of_operand` decides whether to emit `fp.mul`, so the BMC
  encoded the same multiply as a bitvector multiply;
- `smt_encode::width_of` sizes the SMT variable, giving a 64-bit double a
  32-bit sort.

On `coral17` — `asin(x)*acos(x) < atan(x)` — the search proposed `x = 1000`,
because `asin(0.001)` bits times `acos(0.001)` bits, wrapped to `i64` and read
back as a double, is `-1.36e169`, which is comfortably less than `-999`. JVM
replay refused the witness, so the verdict was never wrong; the task was simply
lost to UNKNOWN, along with 38 others.

The fix keys stack slots by `(depth, ty)` and propagates entry stack *types*
along the worklist rather than just heights — which is what the bytecode
verifier's own `StackMapTable` records, and is therefore as well-defined as the
height propagation it replaces. A type mismatch at a merge point diverges the
block, exactly as a height mismatch already did.

`benchmarks/ajave/jvm-floats/SpilledDoubleKeepsItsType` is the minimal case:
six lines, ground truth `2.0 * 3.0 == 6.0` argued from JLS 15.17.1 and confirmed
on a real JVM, which ajave could not verify.

### What it was hiding

This is the interesting part. Fixing the types made
`AbstractSerializationStreamReader_false` go from 0.8s to a timeout, and the
trace says why:

```
check ObligationId(2) in Main.fromDouble(D)J  tainted=false path_tainted=true
INCOMPLETE (handle_branch_fork)   x infinity
```

The BMC's first pass encodes float arithmetic as *bitvector* arithmetic by
default (`AJAVE_FP_ARITH=0`), and the taint machinery is what knows the result
is meaningless — but taint only fires once `operand_is_float` can see that the
operands are floats. With the types wrong, it never fired: the engine imposed
guards computed from nonsense and got small, fast, confidently-wrong constraint
systems. With the types right, it correctly refuses to impose those guards, and
then forks on every branch it cannot decide.

**The mistyping and the FPA-off default were compensating errors.** The recorded
measurement that FPA-by-default costs -69 on no-runtime-exception was taken on
an IR in which most float operands were not recognised as floats, so it does not
transfer and has to be redone. More generally: a guard that says "this value is
meaningless, do not trust it" is only as good as the type information it
consults, and ours was silently absent for every value on the operand stack.

### Measured

`float-nonlinear-calculation`, valid-assert, 180s budget: **40 -> 57**
(38 -> 55 correct, 0 wrong), from the lifter change alone.

Full corpus, 180s: **valid-assert 825 -> 843** (689 -> 706 correct, still the
one known-defective `ReverseInterpolator` wrong answer), **no-runtime-exception
1112 -> 1112, 0 wrong**. Cost is one task, `AbstractSerializationStreamReader`,
which goes from 0.8s to a timeout and does not come back with FPA on — the body
is dense double arithmetic with division and `d2i` casts, so this is the engine
correctly declining to impose guards it cannot decide, not a new defect.

The three `jayhorn-recursive` failures the smoke gate reported are **not** from
this change — the pre-change binary reproduces them, so the baseline is stale.

## 2026-09-04 — encoding provenance: what an engine did not model

`Direction` says what a consumer may conclude from an artifact. It says nothing
about whether the producer's encoding was a model of *this* program, and those
turn out to be different questions.

The bitvector BMC pass encodes float arithmetic as bitvector arithmetic by
default. That is honest under-approximation — of a program that is not ours. It
published a violation derived from `bvmul` on two IEEE-754 bit patterns, which
*closed* the obligation, so the FPA pass — whose entire purpose is deciding
exactly those — skipped the task because `bb.open()` was empty. JVM replay then
refuted the witness, and nothing reopened it.

Artifacts now carry `Approximations` beside `Direction`: a `Copy` bitset of what
the producer did not model faithfully (`FLOAT_ARITH`, `REAL_ARITH`,
`INT_WRAPPING`, `HEAP_ALIASING`). `Blackboard::open_for(models_faithfully)`
returns the open obligations *plus* those whose status was derived under an
approximation the caller does not make.

Two properties make this cheap to adopt:

- It only ever **widens** what an engine looks at, so a wrong entry costs time,
  never correctness. Nothing can be discharged that could not be already.
- It is the general form of `open_or_unconfirmed`, which hard-codes one instance
  of the same idea (an Under engine's witness is a candidate until replay
  confirms it). Both say: *a status is only as good as the model it came from.*

Reopening is deliberately targeted rather than blanket. An engine is offered an
obligation back only when it models something the closer actually got wrong —
otherwise every precise pass re-explores every task, which is the regression
that got the FPA pass gated on `open()` in the first place (float NRE 166 ->
114).

`benchmarks/ajave/jvm-floats/SpilledDoubleKeepsItsType` — six lines asserting
`2.0 * 3.0 == 6.0` — goes unverifiable -> refuted-FALSE -> **TRUE** across the
two changes together.

### Measured

Full corpus, 180s: **valid-assert 843 -> 847**, **no-runtime-exception 1112 ->
1112**, no new wrong answers. Session total 825 -> 847 on valid-assert.

The mechanism is visible end to end on `PartitionEx`, which the change turns
from UNKNOWN into TRUE:

```
before:  smt-bmc violated=1 (9ms) -> "nothing open, skipping the escalation pass"
after:   smt-bmc violated=1 (8ms) -> smt-bmc-fpa discharged=1 (220ms)
```

The bitvector pass finds a float "violation" in 9ms and closes the obligation.
Previously the FPA pass skipped and replay refuted the witness, leaving nothing
behind. Now the FPA pass is offered the obligation back and proves it.

Cost: the float category runs 2.5x slower (78s -> 195s back-to-back on the same
machine), because the FPA pass now runs where it used to skip. That did **not**
translate into corpus timeouts — 41 against 39, with total wall time up 13% —
so the trade is positive at the current budget. It is worth re-checking if the
FPA pass ever gets cheaper to enter, because this is the shape of cost that
becomes a regression only once something else moves.

## 2026-09-01 — the concurrency completeness plan, phases 1-5

Thirty-odd unsupported features turned out to be five missing *mechanisms*.
Building the mechanisms closed the features in batches; building the features
one at a time would have produced thirty special cases. All five landed, plus
the two wrong answers they exposed on the way.

### The mechanisms

**Choice points.** The explorer's only nondeterminism was which thread runs
next, so everything else had to be refused. A decision *tape* fixes that — the
interpreter cannot ask the explorer anything mid-statement, so it signals that a
decision is needed and leaves the program counter alone, the explorer appends
one and re-runs the statement, and the second run reads it back. That is the
same "do not advance, re-execute" contract parking already used. Consumers now:
every timed operation, spurious wakeups, spurious weak-CAS failure, arbitrary
`notify`/`signal` waiter selection, exact `nondetBoolean`, and stale reads.

**Exception handling.** There was none: `Terminator::Throw` killed the thread and
the lifter's `! exc:` edges were never followed, so `try`/`finally` around a lock
worked only because nothing on the normal path throws.

**Threads created at `start()`.** Bodies were already resolved from the object's
real class; only the *allocation* was static, one identity per construction site.
Creating the thread where it starts made where the object came from irrelevant,
closing `extends Thread`, loops, factories, fields and collections at once.

**Library models.** `ConcurrentHashMap`, `ThreadLocal`, `CompletableFuture`.

**Weak memory**, in the one form that is both useful and honest: a racing read
may observe the value the location held before the racing write. A *subset* of
what the JMM permits, so it is usable in one direction only — a FALSE found this
way is real, and no TRUE may rest on it.

### The general lesson: nondeterminism is not one thing

Six independent sources, each mapping to a bug class invisible without it. The
ones that surprised me were the ones the *specification* grants and an
implementation reliably hides:

- `wait` may return spuriously (JLS 17.2.1) — which is *why* a wait must sit in a
  loop, so a program guarding with `if` is incorrect because of it
- `notify` wakes an arbitrary waiter — waking a fixed one makes the verdict
  depend on the interpreter's iteration order rather than on the program
- `weakCompareAndSet` may fail spuriously — that is what makes it cheap, and why
  its contract demands a retry loop

Two need a fairness bound, since the specification permits unboundedly many.
`max_spurious` is 1, measured: every benchmark is decided there and 2 exhausts
the state bound on a three-thread program.

### Two wrong answers, both from pretending a mechanism away

**Sequential engines were proving concurrent programs.** `Thread.start()` is not
a call a sequential engine follows, so to one of them the thread never runs, and
any obligation whose reachability depends on another thread's writes looks
unreachable. smt-bmc "proved" the assertion in the canonical unsafe-publication
bug on exactly that basis. The *violation* side of this blind spot was already
handled — a sequential engine's candidate is refuted at replay — but nothing
guarded the *proof* side, which is the more expensive direction. Now enforced at
the blackboard's publish gate, beside the direction discipline it already
applies, and free: the concurrency engine handles concurrent programs itself and
the scored corpus has none.

**Taint did not follow control flow.** A branch taken on a placeholder from a
stepped-over call decides *which code runs*, and everything computed afterwards
is conditioned on a guess even though no single variable in it is tainted. Two
benchmarks reported FALSE against a ground truth of TRUE before the classes they
exercise were modelled at all.

### And one that only a deterministic search could show

The explorer chose the next thread by iterating a `HashSet`, and Rust seeds
hashers per process. `SleepIsNotSynchronization` returned FALSE or UNKNOWN across
identical runs. Fixing it to `BTreeSet` then locked in the *unlucky* outcome,
which exposed the real bug underneath: the race search returned at the first
assertion violation, when under `no-data-race` an exception merely kills that
thread and the program continues. Determinism did not just make results
repeatable; it made a second defect visible.

## 2026-08-31 — DRF-SC: turning "we assume sequential consistency" into a checked condition

The concurrency explorer only ever considered sequentially consistent
executions, and said so in a document. That is the assumption a reviewer attacks
first, and the honest reading of it is worse than it sounds: **on a racy program
an exhaustive SC search proves nothing about a real JVM**, because JLS 17.4.5
gives the SC guarantee to data-race-free programs only. Every TRUE we issued for
a racy concurrent program described a machine the JVM is not obliged to be.

The fix is not to implement the Java Memory Model. It is to detect races and
make race freedom the *precondition of the proof*:

> A TRUE from this engine is sound under the JMM, because it is only issued for
> programs verified data-race-free.

### Happens-before is a relation, not the schedule

The design decision that matters, and the one chosen to avoid a dead end.

Under sequential consistency an execution *is* a total order, so "did A happen
before B" could be read off positions in the interleaving. That answer is
useless for the question that matters — whether two accesses are ordered *by
synchronisation* — and in schedule order **every pair is comparable, so a data
race is not even expressible**.

So happens-before is built from release/acquire edges emitted by the
synchronisation primitives themselves (`vclock.rs`), never from scheduling
order. Two payoffs, both deliberate:

* races become expressible, as incomparable clocks;
* the relation survives non-SC exploration. A weak-memory explorer branches a
  read over the writes it may observe, and none of these edges change. A
  relation derived from the schedule would have to be thrown away at that point.

### Read locks are where the modelling gets interesting

Two readers hold a read lock simultaneously and are genuinely concurrent, so
ordering them would hide a write performed inside a read section — which is a
real bug shape, and `ReadWriteLockConcurrentReaders` is built from it. Readers
therefore acquire only from the writer channel and publish to a separate channel
that only writers absorb. Writers absorb both.

This is the general shape of the problem: **too few edges reports races that do
not exist, too many hides races that do**, and both are wrong answers rather
than precision losses.

### Two bugs the benchmarks caught, both about *when* rather than *what*

`release` advanced the thread's own clock component **before** publishing, so
the acquirer inherited a clock that already covered the releaser's next action.
Everything then looked ordered, and the detector reported no races at all —
including on a two-line unsynchronised counter. Publishing must precede the tick.

Thread termination published nothing, because the edge sat where `advance`
notices an already-empty frame stack rather than at `Terminator::Return`, where
threads actually finish. A joiner learned nothing from the thread it joined, so
every joined write looked racy. Both were found by disagreement between the
detector and benchmarks whose race status was known by construction.

`submit` was not a fork either: an executor task shared no history with its
submitter, so values the submitter had already initialised looked racy to it.

### What it cost, and why that is the point

`NoJoinNoOrdering` and `NonVolatileNoGuarantee` were reported TRUE and are now
UNKNOWN. Both are racy, so the SC result does not transfer. `NonVolatileNoGuarantee`
is the sharp case: its bug *requires* weak memory to appear, so under SC the
program looks correct — which is exactly why that TRUE had to go. Both carry a
`DRF-SC BOUNDARY` note so the UNKNOWN reads as a boundary rather than a
regression.

### Still out of reach

Detecting reordering-dependent bugs, as opposed to declining to verify them.
That needs a weak-memory explorer where a read branches over visible writes. It
also breaks the certification story: a JMM-permitted but rare behaviour cannot be
reproduced by running on a JVM, so the replay net that backs every other FALSE
stops working exactly where it would be needed most.

## 2026-08-31 — concurrency: from litmus tests to real programs, and the five wrong answers that found

The concurrency engine went from 22 to 46 benchmarks and from intrinsic monitors
to most of `java.util.concurrent`. The interesting part is not the feature list;
it is that **every serious defect was found by writing a realistic program, not
by writing a litmus test**, and four of the five were wrong answers rather than
missing coverage.

### The pattern: litmus tests agree with their own assumptions

The suite had 22 benchmarks, all passing, all two threads and one worker class.
Adding six programs that a Java developer would recognise — a bank transfer,
dining philosophers, a semaphore pool, a latch scatter/gather — immediately
produced a wrong TRUE and a wrong FALSE:

- `discover` ended with `sort(); dedup()`, so **two threads running the same
  `run()` collapsed into one entry**. Every existing benchmark had one worker per
  class, so the bug was invisible. `TwoWorkersSameClass` was FALSE (−32) because
  only one of its two writes happened; `DiningPhilosophers` was TRUE (−16)
  because its three-node wait-for cycle needs all three philosophers.
- `start()` on a thread with no state fell through an `if let` with no `else`,
  which is what converted the under-count from a refusal into a wrong answer.
  **Silence on an unmodelled operation is the most expensive failure mode there
  is**: refusing costs a point, answering wrongly costs sixteen or thirty-two.

Neither is exotic. Both needed a third thread or a second instance, which no
litmus test had.

### Ordering that was load-bearing by accident

Thread identities are assigned in construction order; entries were sorted by
method name because `prog.bodies` is a `HashMap` and determinism demanded *some*
order. Pairing those two lists by index is only correct when the orders agree.
The fix is not a better sort — it is to stop pairing: `start()` now resolves the
body from the class of the Runnable object it was actually handed, so entry
order carries no meaning at all.

A benchmark written to catch this (`WorkersBoundInConstructionOrder`) passed
against the buggy engine, because neither thread body read `this`. It was
rewritten until it discriminated. **A regression test that passes against the
bug it was written for is worse than none**, and the only way to know is to run
it against the unfixed engine first.

### Guessing at `<clinit>` cost two verdicts in opposite directions

Class initialisers were approximated: a static whose initialiser was visibly a
`new` got a fresh object id, everything else read as null.

- The "from new" test was a set that only ever *grew*, so when javac reused a
  register — `static final Condition cond = lock.newCondition()` reuses the one
  that held the lock — the second `putstatic` still looked like a `new`.
  Identity was minted at the `putstatic` rather than at the `new`, so
  `static final Object B = A` produced a second object for the same one, and two
  threads taking A-then-B and B-then-A were reported to deadlock between a lock
  and itself. Reentrancy makes that impossible: wrong FALSE.
- Fixing identity exposed the opposite error. `cond` correctly stopped being
  seeded, read as null, and **its null-check pruned every path that reached
  `await`** — reporting TRUE for a program that deadlocks on a missed signal.

The second is the more instructive: an under-approximation that *prunes paths*
does not lose precision, it manufactures proofs. Both went away by running
`<clinit>` rather than pattern-matching it, which is also just what the JVM
does, and gets aliasing, factory methods and computed initial values right for
free.

### One rule, three bugs

Whether a modelled call may advance its own program counter looked like a detail
and was three defects:

- `Stmt::Assign` stores a returned value only while the frame has not moved.
  A model that advanced first silently discarded its own result — `tryLock`'s
  boolean, `incrementAndGet`'s count, `Future.get`'s value — and the next read
  failed as an unknown operand.
- A model that parked *and* advanced sent the thread past the call it was
  blocked on, walking a blocked `lock()` into the critical section without the
  lock. `wait()` had the same defect, so the handshake benchmarks had been
  passing for the wrong reason.

The invariant now: **no modelled call touches the program counter**, and thread
status is the single source of truth for parking. Every synchronizer added
afterwards — latch, semaphore, barrier, condition, executor — blocked correctly
without any new machinery, which is the sign the abstraction was right.

### Bounds that were not what they claimed

Two constants were doing jobs they were not documented to do.

`max_steps` was described as "steps per thread, so a spinning thread cannot
consume the whole budget", but was allocated once and decremented across every
interleaving — a cap on *total exploration*. Programs that terminate perfectly
well exhausted it simply by having many interleavings, so a provable TRUE
degraded into UNKNOWN as the program grew rather than as it misbehaved. It is
now per-segment, which is where divergence actually happens, with explicit
`max_states` and `max_depth` for search size.

`max_switches` was 10, below what a three-thread program needs to be *exhausted*.
Raised to 32 after measuring 10/16/32/64: verdicts identical from 16 upward and
suite runtime flat at 4s, so above the threshold it does not behave as a tuning
knob — DPOR and `max_states` bound the search. All bounds now take environment
overrides so that sweep is repeatable, which is what CLAUDE.md asks for on any
constant chosen by watching benchmarks.

### Allocator state outliving its path

The explorer restored frames and thread objects between sibling DFS branches but
not the allocators. Sibling branches are alternative universes that re-execute
the same statements, so a carried-over `next_tid` gave the same `submit` a
different thread identity in each — beyond the states that exist. Thread
constructions had escaped this only by happening at depth 0, before any
branching, which is the same "the tests were too simple" pattern as the dedup
bug. **Anything an interpreter accumulates has to be scoped to the path**, not
to the search.

### Where approximation was declined

Several features are refused rather than approximated, each because the cheap
version yields a wrong verdict rather than a lost proof: a thread pool with
fewer workers than tasks (queued tasks are not concurrent — inventing that race
is −32), interrupting a parked thread (must throw and resume, not stay parked),
timed waits (can return false on expiry), and a `CyclicBarrier` action (needs a
frame pushed from inside a model). `ExecutorSingleThreadSerialises` is kept in
the suite *expecting UNKNOWN*, so that making the pool unsoundly concurrent
shows up as a wrong answer.

### What did not change

Sequential consistency. The engine cannot see bugs that need reordering —
broken double-checked locking and non-volatile publication both look correct to
it — so it will report TRUE for some programs that fail on a real JVM. That gap
is documented in `docs/strategies/concurrency.md` rather than benchmarked,
because adding a benchmark we knowingly answer wrongly would put a wrong answer
into a suite whose entire value is that it has none.

## 2026-08-31 — float category 18 -> 40, and three self-inflicted regressions

`float-nonlinear-calculation` went from 18 to 40 on valid-assert while
no-runtime-exception held at 166. **None of the gain came from better solving.**
It came from being able to run and encode the program correctly:

1. The concrete evaluator handled only `abs/min/max/round/signum`. Every other
   `Math` call returned Unknown and ended the run Inconclusive, so a program
   calling `Math.sin` was not executable and every engine that depends on
   running it was blind. `coral17` is violated at x = -0.5, which was already in
   the search's seed list — we simply could not run the program.
2. The interpreter had no float arithmetic at all. `Add|Sub|Mul|Div|Rem` on
   `Value::I64` did `wrapping_mul` on raw bit patterns, so `NaN * NaN` produced
   a non-NaN value and every downstream comparison diverged from the JVM.
3. `float_search` wrote 64-bit patterns for 32-bit `nondetFloat` slots, so the
   engine searched with -3.88e9 while the JVM replayed 18.145. A confirmation
   under those conditions is meaningless, and since a confirmed violation is
   reported as FALSE unchecked, that is a soundness hazard.

This is worth generalising: SMT-LIB has **no transcendental functions** — there
is no `fp.sin` — so no encoding work can decide most of this category. Solving
over the reals gives answers correct over R but not IEEE-754. `Math.sin` is
specified only to within 1 ulp, so there is no unique symbolic answer: the JVM
is the ground truth. These benchmarks come from `concolic-walk` and `jpf-symbc`,
which exist to be solved by search.

### Three regressions I introduced and then had to find

- **FPA defaulted on from a valid-assert-only measurement.** +7 there, -69 on
  no-runtime-exception, shipped as an improvement. Resolved by escalation: a
  second BMC pass with FPA that only touches obligations the cheap pass left
  open, returns immediately when nothing is open, and is bounded to 5s per query
  so a bonus pass cannot spend the whole task budget. Recovered both.
- **`float_search` wired into the portfolio with no applicability guard**, so it
  ran on every property, burning up to 300k concrete executions against
  exception obligations its fitness cannot steer toward.
- **A per-call `HashSet` allocation** in the interpreter's hot path, now cached
  per method.

Each was caught by measurement, not review. The lesson is not "be more careful"
but "measure both properties before calling a default settled".

### A benchmark defect

`argv-tasks/ReverseInterpolator_true` expects TRUE. We answer FALSE with
`input = 16.342388153076172f`, and a standalone `java -ea` run exits 1 with
`AssertionError`. The guard `|input| <= 100.0f` admits it, and the assertion
asks a reverse interpolator to match `x^5 * 16` within 1.1. Deliberately not
worked around: suppressing a correct, JVM-verified answer to match an expected
verdict is overfitting. Costs -32 until resolved upstream.

Final: valid-assert 816 (672 correct — 848 excluding the disputed task),
no-runtime-exception 1021 (527 correct). 24 more tasks answered correctly than
at the start of the day.

## 2026-08-30 — verdicts were not reproducible, and it was being read as timeout noise

### What was wrong

Rust seeds `HashMap`/`HashSet` hashers randomly **per process**, so iterating one
gives a different order on every run. Three such iterations fed the solver:

- `Program::devirtualise` returned virtual-dispatch targets in hash order. BMC
  explores them in that order and stops when its budget runs out, so the order
  decides which targets are examined at all.
- `apply_ai_hints` asserted AI interval bounds in hash order. The formula stays
  logically identical but changes shape, so the solver returns a different
  (still valid) model — and only some witnesses reproduce on a real JVM.
- `merge.rs` built merged constraints from `HashSet` unions at join points.

Separately, `ajave-build-{pid}` and `ajave-shadow-{pid}` were created with
`create_dir_all` and never deleted. Pids are reused, so a run could inherit an
earlier run's directory; `collect_classes` returns everything in it, so the
verifier analysed another task's classes alongside its own.

### Why it hid for so long

It presented as score variance and was attributed to timeouts. The recorded
range "valid-assert ~804-818, varies with timeouts" is a ~14 point band, and
this session measured 798/800/802/814/820 and blamed CPU contention. Contention
was real and explained part of it (89 timeouts on a loaded machine, 43 on an
idle one). The residue was this.

The arithmetic matches. Two of 134 smoke tasks were nondeterministic — about
1.5%. Across 1033 valid-assert tasks that is roughly 15 tasks at 1-2 points
each, so **±15-30 points of run-to-run noise**, against an observed band of ~16.

It was also easy to dismiss: on a 134-task set two flaky tasks move the score by
1-3 points, which is exactly the magnitude that gets called noise. And it only
reproduces inside a parallel batch, so serial loops of a dozen runs kept showing
a stable answer.

### Fixes

All three iterations now run in sorted order (`FK` gains `Ord`), and z3 is given
fixed seeds so its model choice cannot drift either. `ScratchDir` replaces both
temp directories: unique by construction, created with `create_dir` so a
collision retries rather than silently reuses, and self-deleting on drop.

`tools/bench.py --repeat N` runs every task N times and fails if any returns
more than one verdict. It found the second cause immediately after the first was
fixed, which the manual checks had missed.

### Instrument bug found on the way

The orchestrator's per-engine `discharged=` counter observed *stored* statuses.
A discharge published after a violation is recorded in `proved_safe` but
discarded from `statuses` (first final status wins) — and that discarded
discharge still steers the verdict through `verdict_excluding`. So the counter
reported "no discharges" for the very publication that decided the answer. It
now counts published discharges.

### Effect on score: about zero, and that is the point

`VirtualDispatchPicksOverride` settles on TRUE (correct, a real gain);
`objects14` settles on UNKNOWN, so that point is now lost every run rather than
70% of them. Net ~0.

What changed is that a score delta now means something. Before this, no
comparison below roughly ±20 points on the full corpus was readable, which
retroactively weakens several conclusions drawn the same day — including
"820 versus a 814 baseline".

Verified: smoke 134x3, ajave 97x5, concurrency 16x5 — all verdicts stable, 0
wrong.

## 2026-08-30 — unified benchmark layout, one runner, and process-group cleanup

### Layout

Three overlapping corpora and four harnesses became one tree and one runner.

```
benchmarks/
  sv-comp/   official corpus (1033 tasks, gitignored)
  ajave/     our own suite (71 tasks, JVM-verified per-property ground truth)
  sets/      named subsets both runners read
  benchexec/ tool-info + benchmark definitions
```

Compatibility symlinks (`sv-benchmarks`, `ajave-benchmarks`) keep the twelve
existing tools resolving during migration.

### One runner

`tools/bench.py` replaces the overlapping logic in `smoke_test.py`,
`score_full.py`, `score_own.py` and the Rust corpus test, each of which had
re-implemented task discovery, property selection and verdict comparison — and
disagreed on all three. The property mismatch in #54 was possible only because
one of them *inferred* the property rather than reading it; the new runner takes
ground truth from the task's own yml and never decides what a task should
answer.

Outcomes are `correct` / `unproven` / `WRONG`. Only WRONG and
correct->unproven regressions fail `--check`; an UNKNOWN that was already
UNKNOWN is not a regression, which is what made the previous suite noisy enough
to ignore.

### Process-group cleanup — the bug that froze the machine

`subprocess.run(timeout=…)` and Rust's `Child::kill` both signal only the direct
child. ajave spawns a solver (z3/cvc5) and a real JVM for witness replay, so
**every timed-out task orphaned a solver and a JVM**, each holding hundreds of
megabytes and running indefinitely.

Across a corpus run with dozens of timeouts this compounded until the machine
ran out of memory and froze. It also silently corrupted measurement: load
average reached 61 on a 10-core box, and the smoke set that takes **29s** on an
idle machine took **152s** under that load. Several performance conclusions
drawn earlier the same day were artifacts of it.

Both runners now spawn each task into its own process group (`start_new_session`
in Python, `process_group(0)` in Rust) and kill the *group*, so no descendant
outlives the run. `tools/procguard.py` carries a test that demonstrates
`subprocess.run` leaking a grandchild where `run_guarded` leaks none.

Supporting measures:
- `tools/cleanup.sh` sweeps strays and temp dirs; matches only project-specific
  patterns, never a bare `java` or `z3`.
- `bench.py` sweeps on exit and refuses more workers than the machine has memory
  for (~1.5GB each: ajave + solver + JVM).
- Load and free memory are printed with every result, so two numbers are
  comparable or visibly not.

### BenchExec

Kept as the competition-fidelity backend and moved to `benchmarks/benchexec/`.
It enforces limits through Linux cgroups, so it cannot run on macOS — local
development uses `bench.py`. Both read the same sets, so they agree on what is
covered and differ only in resource enforcement.

Baselines recorded on an idle machine: smoke 134 runs, ajave 97, concurrency 16;
0 wrong across all three.

## 2026-08-30 — corpus regression gate rebuilt around declared ground truth (#54)

`crates/ajave-cli/tests/corpus.rs` was 114 hand-written tests that invoked the
binary with **no `--property` flag** and asserted a literal verdict. 24 failed on
a clean `main`, and because they always failed the suite no longer distinguished
a regression from standing noise — the one job it existed to do.

Two independent defects were tangled together:

1. **Implicit property.** With no flag the binary runs `--property assert`, but
   many expected verdicts describe runtime-exception behaviour.
   `tasks/stage04_divzero` is `int y = 100 / nondetInt(); assert y != 12345;`,
   declared FALSE. Under valid-assert TRUE is *correct* — `100/x == 12345` has
   no integer solution and `x == 0` throws before the assertion is reached.
   Under no-runtime-exception it is FALSE. Both answers are right; the test
   asserted the one belonging to the other property.

2. **Expectations pinned to output, not truth.** The old header stated each test
   asserts "the verdict ajave *currently* produces", so every genuine
   improvement registered as a failure. `jbmc-regression/array1` moved
   UNKNOWN -> TRUE — correct per SV-COMP — and counted as a regression.

### What the task files actually say

All 114 task ymls declare exactly one property, `assert.prp`, yet their expected
verdicts plainly span uncaught exceptions too: `ModuloZero1` has no reachable
assertion failure and is declared FALSE. This corpus uses "assert" to mean *the
program misbehaves*, which covers both SV-COMP properties.

Rather than re-adjudicate 114 ground truths — an invitation to fit expectations
to current output, exactly what produced the drift — each task now runs under
**both** properties and the results are combined:

* `expected: false` — at least one property must be violated.
* `expected: true` — neither may be violated, and both must be proved.

The second is deliberately conservative. With NRE UNKNOWN we do not know whether
an exception escapes, so the task scores "unproven" rather than passing: a
regression gate must never produce a false pass. Validated on an 18-task sample
before adopting: 14 correct, 4 unproven, 0 wrong.

### Failure conditions

* **Wrong verdict** — combined answer opposite the declared one. Always fails;
  this is the -16/-32 case at competition.
* **Regression** — a task previously `correct` no longer is, against the
  baseline in `tasks/corpus-expectations.txt`
  (`UPDATE_CORPUS=1 cargo test --release -p ajave --test corpus`).

An UNKNOWN that was already UNKNOWN does not fail. Precision we never had is not
a regression, and treating it as one is what made the old suite ignorable.

Baseline at time of writing: **114 tasks, 70 correct, 44 unproven, 0 wrong.**

Tasks are keyed by path relative to `tasks/`, not directory name —
`ArithmeticException1` exists both at the top level and under
`jbmc-regression/`, and the bare name silently collapsed them into one entry.

### Why data-driven

1188 lines became ~350, and the defect class is gone rather than patched: a test
can no longer disagree with its own task file about which property it checks,
because it no longer restates the expectation at all.

## Witness replay: accept the exception family, not one predicted name (2026-08-28)

`JvmReplay` confirmed a violation only when the JVM's stderr contained the
single exception class `exception_class()` predicts from the obligation kind.
That is stricter than the property being checked, and it refused witnesses that
crashed the JVM exactly as intended:

- `String.charAt(i)` out of range throws `StringIndexOutOfBoundsException`, but
  the contract-seeded bounds checks use the `ArrayBounds` kind — which demanded
  `ArrayIndexOutOfBoundsException`.
- `ExplicitThrow` is seeded for any `athrow` of a RuntimeException subclass, so
  programs raise `IllegalStateException` or `NoSuchElementException` while the
  check demanded the literal name `RuntimeException`.

For the no-runtime-exception property, what matters is that *some* uncaught
RuntimeException escaped `main` — that is the property. Replay now accepts the
family per obligation kind, and stays strict for assertions where
`AssertionError` is the only correct outcome.

This also decides how a new precondition should pick its obligation kind: the
kind determines what replay will accept, so `NonEmpty` is seeded as
`ExplicitThrow` rather than `ArrayBounds`, because an exhausted iterator raises
`NoSuchElementException` and a bounds kind would make replay demand an index
exception the JVM never throws.

## More expressible preconditions (2026-08-28)

Two conditions previously marked `Unexpressible` turned out to be statable, and
marking them so was costing answers in *both* directions — the guard blocked
TRUE while nothing could construct the FALSE, leaving the task unanswerable.

- **`NoOverflow { a, b, op, width }`** for `Math.addExact`/`subtractExact`/
  `multiplyExact`. Overflow is only observable at a wider type: at the original
  width the arithmetic silently wraps, which is precisely what these methods
  exist to detect. The lifter widens both operands to `long`, computes there,
  and requires the result to fit in 32 bits. (The 64-bit overloads have no wider
  type available and stay unseeded.)
- **`NonEmpty`** for `Iterator.next`, `Stack.pop/peek` and the Deque removal
  methods, now that element counts are tracked in `$$coll_size`. Emptiness is
  `$$coll_size == 0`, so an exhausted iterator becomes a checkable obligation
  rather than an unanalysable call.

Own benchmark suite: 65/81 -> 69/81 (85.2%), 0 wrong.

## Verdict resolution: an unconfirmed violation must not veto a proof (2026-08-28)

**Architectural change to the blackboard's status model.** Worth reading before
touching `publish`, `open`, or the verdict computation.

### The bug

The blackboard held exactly one `Status` per obligation, and `is_final()` made
the first one stick. Whichever engine published first therefore won outright.

That is wrong for a portfolio containing engines in both directions. An
under-approximating engine's `Violated` is a **candidate**: it carries a witness
which JVM replay may refute. An over-approximating engine's `Discharged` is a
**proof**. Letting an unrefuted candidate erase a proof — purely because it
arrived earlier in the engine order — is an ordering artifact, not a soundness
rule.

Concretely, this cost the entire `float-nonlinear-calculation` valid-assert
category. NRA solves over the reals so cvc5 can handle `sin`/`exp`; Java
computes in IEEE-754. A real-valued counterexample routinely fails to reproduce
once rounded to the nearest double, so NRA's violations were refuted at replay —
but by then they had already:

1. removed the obligation from `bb.open()`, so the BMC never considered it, even
   though it had explored the same body exhaustively and found **zero**
   violations with `all_paths_complete: true`; and
2. forced the final verdict to UNKNOWN, since a refuted violation fell straight
   through to UNKNOWN without asking what else was known.

Symptom: 0 correct-TRUE and 66 unknown on valid-assert, against 83 correct on
no-runtime-exception for the *same benchmarks*. That asymmetry is what exposed
it — the engines could prove no exception escapes but not the assertions.

### The change

Three pieces, each independently sound:

- **`Blackboard::proved_safe`** — a set recording every `Discharged`, kept even
  when a `Violated` occupies `statuses` for the same obligation. The two are not
  contradictory until the violation is confirmed.
- **`Blackboard::open_or_unconfirmed()`** — obligations that are open *or* hold
  only an unconfirmed violation. The BMC's per-obligation discharge loop uses
  this, so an exhaustive exploration is not silently skipped because an Under
  engine published first.
- **`Blackboard::verdict_excluding(refuted)`** — recomputes the verdict with
  replay-refuted violations withdrawn. Returns TRUE only when every *remaining*
  obligation is discharged and every excluded one was independently proved safe,
  so a refuted violation on an otherwise-unproven obligation still yields
  UNKNOWN.

The soundness argument is unchanged in the direction that matters: a violation
that survives replay is still final, `Direction::Under` still cannot discharge,
and `Direction::Over` still cannot violate. What is removed is the ability of an
*unconfirmed* claim to suppress evidence.

### Not the fixes that were tried first

Two earlier attempts are worth recording as dead ends:

- **Gating NRA on whether its witness survives concrete re-execution.** Sound in
  principle, useless in practice: our concrete interpreter mismodels the same
  transcendentals, so it agreed with NRA and the filter passed everything. A
  filter that shares the bug it is filtering cannot work.
- **Falling back to `verdict_excluding` alone.** Correct but insufficient — the
  obligation had no independent discharge to fall back *to*, because the BMC had
  already been excluded from considering it. The `open_or_unconfirmed` change is
  what made the fallback have something to find.

Own benchmark suite: 63/81 -> 65/81, 0 wrong.

## External-method contracts: one table, preconditions instead of vetoes (2026-08-28)

Five separate places encoded "what does this JDK method do" —
`could_throw_runtime_exception`, `pure_owner_member_may_throw`,
`str_call_can_throw`, `PURE_OWNERS`/`CallModel`, and the field-abstraction
clobber sets. Each was incomplete and they drifted independently, which is why
the same unsoundness resurfaced three times in different disguises (issues #48,
#49, and the `PURE_OWNERS` call-erasure below).

**One `Contract` table now, in `ajave-models`:**

```rust
pub struct Contract { requires: &'static [Precondition], effect: Effect }
pub enum Precondition {
    NonNull(u8), IndexInRange{index,seq}, RangeInBounds{start,end,seq},
    NonNegative(u8), NonZero(u8), NonEmpty, Unexpressible,
}
```

Everything derives from it: totality is `requires.is_empty()`, the lifter seeds
`Check` obligations from preconditions, the verdict guard stands down only where
those obligations carry the burden, and the field abstraction reads `effect`.

**The key idea is naming *why* a method throws rather than flagging *that* it
might.** `s.contains(t)` raises NPE exactly when `t` is null. Flagging it
may-throw forces UNKNOWN on every program that calls it; seeding `NonNull(1)`
lets the existing nullness analysis discharge it. Conditions we cannot state
(`IllegalFormatException`, overflow in `addExact`) map to `Unexpressible` and
still block — which is the honest answer, not a gap.

Measured on NRE: **835 → 967**, 0 wrong. securibench 1 → 49 correct-TRUE,
jbmc-regression 80 → 98. Those are the same answers the pre-refund build gave,
but now backed by discharged obligations rather than by the call having silently
vanished from the analysis.

### The invariant that made it safe

`Precondition::is_seeded()` states which kinds the lifter actually emits, and
the verdict guard trusts *that*, not "expressible". Getting this wrong is not
theoretical: an intermediate version let the guard skip `IndexInRange` while the
lifter still ignored it, and three wrong TRUEs appeared in `ajave-benchmarks`
within a minute. The predicate and the seeding loop are adjacent and
cross-referenced for that reason.

Seeding also had to be hoisted *above* the `CallModel` dispatch: `new
StringBuilder(-1)` throws, but StringBuilder takes the `StrCall` path and would
otherwise skip the check — the same "call disappears down one branch" shape as
the `PURE_OWNERS` bug.

### Supporting changes

- **Collection size**: `$$coll_size` as an ordinary synthetic field (`add`
  bumps it, `size()` reads it), so `list.get(i)` carries a real `0 <= i < size`
  obligation the interval domain can discharge. Deliberately expressed in terms
  the analysis already understands rather than as a new domain.
- **Effect-aware clobbering**: a callee without a body no longer discards every
  tracked field when its contract says `Effect::Pure`. Precision *and*
  performance — fewer invalidations means tighter states and faster convergence.
- **Devirtualised interface calls**: `ObjectFactory.createObject()` is declared
  on an interface with no body, but resolves to a benchmark implementation; it
  no longer counts as unanalysable.
- **NRA witness substantiation**: NRA published violations assigning
  `nondetDouble` in methods that read no nondet input at all. Replay refuted
  them, but a refuted violation still blocks the TRUE another engine proved.
  An Under engine may now only publish witnesses naming inputs the program
  actually reads.

## IEEE-754 float comparisons (2026-08-28)

The SMT layer had no floating-point theory: floats were bitvectors and
comparisons used `bveq`/`bvslt` on raw IEEE-754 bit patterns, which gets NaN
and signed zero wrong (NaN compares equal to itself; -0.0 differs from 0.0).
A `float_tainted` set existed to suppress the resulting garbage.

Added `Sort::Fp(32|64)` and the FPA operations, with `dcmpl`/`dcmpg` encoded via
`fp.eq`/`fp.lt`/`fp.isNaN` including the NaN asymmetry the two instructions
exist to express.

**Arithmetic deliberately stays on the bitvector path.** Encoding it in FPA is
more faithful but measured ~2.5x slower end-to-end (smoke 874s -> 2194s), which
pushed transcendental benchmarks past the timeout and lost more than the
precision gained. Comparisons are where bitvectors are *wrong* rather than
merely imprecise, and they cost nothing. The infrastructure is in place if the
performance picture changes.

## Soundness fixes found by our own benchmark suite (2026-08-28)

`ajave-benchmarks/` (see below) found six wrong TRUEs the SV-COMP corpus never
surfaced, in three distinct classes:

1. **Modelled calls dropped exceptions.** `math_call_modelled` claimed
   `addExact` and encoded it as a plain bitvector add — the exact thing
   `addExact` exists to detect. Modelling a *value* is not licence to assume
   totality (#49).
2. **`PURE_OWNERS` erased throwing calls entirely.** `System.arraycopy` and
   `Integer.valueOf(String)` classified as `Pure`, which makes the lifter
   rewrite the call to a `Havoc` — so no engine ever saw a call, and neither the
   allowlist nor any guard could fire. The call simply vanished from the IR.
3. **TRUE by vacuity.** With no obligation seeded, the blackboard held *zero*
   obligations and the verdict was TRUE before any engine ran. The CLI now
   refuses a no-runtime-exception TRUE when a reachable call has unmodelled
   exception behaviour.

## Our own benchmark suite: `ajave-benchmarks/` (2026-08-28)

57 benchmarks / 81 property instances across 13 categories, in SV-COMP task
format so existing tooling works unchanged. Each isolates **one** JVM semantic
rule or engine capability, so a wrong answer names the broken feature instead of
reporting that some large program changed verdict.

Categories: `jvm-integers` (overflow wraparound, `MIN_VALUE / -1`, shift
masking, narrowing casts), `jvm-floats` (NaN, signed zero, non-associativity),
`jvm-null`, `jvm-arrays`, `jvm-exceptions`, `jvm-types`, `jvm-boxing`,
`jvm-strings`, `jdk-contracts`, `engine-ai`, `engine-bmc`, `engine-recursion`,
`witness`. Both TRUE and FALSE variants where meaningful — a one-sided suite
rewards a tool that always answers one way.

**Ground truth is verified, not asserted.** `tools/validate_own_benchmarks.py`
compiles and runs each benchmark on a real JVM: deterministic ones are fully
checked, nondeterministic ones checked for contradictions over many runs (one
execution can neither confirm a FALSE nor establish a TRUE). A wrong
`expected_verdict` would be worse than no benchmark at all.

This is the independent signal issue #47 called for: every other measurement we
have comes from the corpus we also score on.

## AI: array lengths, bitwise ops, real widening, and an exceptional-edge soundness fix (2026-08-27)

Motivated by measurement rather than intuition. Bucketing the *open* obligations on every
benchmark we answer UNKNOWN showed NRE unknowns are 90.6% `NullDeref` and 7.4% `ArrayBounds`,
while 76% of valid-assert unknowns have **no open obligations at all** — they are violations
found but rejected by JVM witness replay. A second survey counting heap usage *per method*
(the granularity engines bail at, and the only honest one: a whole-program count flags ~100%
of tasks because every benchmark has `main(String[])` and every enum a synthetic `$values()`)
found 64% of obligation-bearing methods use no heap ops, 29% only fields, and just 7% need
array theory. That killed the plan to build array theory first.

1. **Array-length tracking.** `IState` gains `array_lens: VarId -> Interval`, seeded at
   `NewArray` (met with `[0, MAX]`, since a negative length throws rather than allocating)
   and propagated through copy chains, with full `leq`/`join`/widening support. A JVM array's
   length is immutable after allocation, so this is ordinary constant propagation. Also added
   the `Interval::meet` the domain was missing.

2. **Bitwise `&`/`|`/`^` on intervals.** This was the actual blocker for array bounds: javac
   lowers `idx >= 0 && idx < len` to a *bitwise* `&` of two 0/1 values, and `eval_rvalue`
   returned Top for it, so no constant-index bounds check could ever be discharged. Exact on
   `{0,1}` operands; sound bounds for non-negative ranges; Top when either side may be
   negative, where the two's-complement result is not interval-representable.

3. **Widening that actually widens.** `WideningIntervalCpa` never overrode `merge`, so it ran
   with the default `merge_sep` — purely path-sensitive, no widening. Both `widen_state`
   and `widen_state_thresholded` were dead code and `widen_delay`/`join_counts` were never
   read; the earlier float-loop gain came from the float *domain*, not from widening. It now
   joins at loop headers and switches to threshold widening after `widen_delay` joins.
   Subtlety: `merge` must return `Sep` once the result adds nothing, because the driver skips
   its `stop` check whenever a merge fires — returning `Joined` unconditionally re-enqueues
   forever. The two CPAs were also unified: `WideningIntervalCpa` now holds a `base:
   IntervalCpa` and delegates `initial`/`transfer`, inheriting the nullness and array-length
   tracking its own copy lacked (which is why it had been safe only for float bodies).
   `ai.rs` runs the precise CPA first and retries under widening only when it reports
   incomplete, so bodies that already converge keep their sharper bounds.

4. **Exceptional edges from calls (soundness).** `successors()` emitted exceptional edges only
   from `Stmt::Check` positions and `Terminator::Throw`, so a call propagating an exception
   from its callee produced no edge and any handler reachable only that way was invisible.
   Because `discharge_obligations` treats a never-visited check as vacuously safe, obligations
   inside such handlers were silently discharged. The bug was masked because those methods
   returned `complete=false` and were skipped; making widening work exposed it as two wrong
   TRUEs on `*-MemUnsat01`, where the assertion sits in a `catch` guarding a throwing call.
   Calls now emit exceptional edges — well-founded, since a call genuinely can throw, unlike
   the `Assign`/`Assume` positions the original restriction was guarding against.

Net effect: MinePump NRE goes from 0/64 solved to TRUE. Removing the unsoundness costs one
previously-correct smoke answer, which is the right trade.

## Cross-engine improvements: return-nullness summaries + NRE-safe expansion (2026-08-26)

Three improvements across the engine portfolio:

1. **Interprocedural return-nullness summaries**: `analyze_return_nullness()` scans method bodies
   to identify methods that always return non-null (via New, string constants, non-null params,
   non-null field loads, or non-null static loads). The interval AI now recognizes Call results
   from such methods as `NonNull`, enabling NullDeref discharge for patterns like
   `p.getEnv().isMethaneLevelCritical()` where `getEnv()` returns `this.env` (a constructor-initialized field).

2. **Expanded NRE-safe call list**: added Enum, Collection/Map/List, Iterator, Stack/Queue,
   and Scanner methods to `could_throw_runtime_exception()`. These don't throw RuntimeException
   and were blocking NRE discharge when havoced.

3. **BMC concrete witness validation (attempted and reverted)**: tried using the concrete engine
   to pre-validate BMC witnesses before publishing. Too many false rejections — the concrete
   engine doesn't model virtual dispatch, float bit ops, or JDK methods precisely enough.
   The JVM replay certifier remains the authoritative validator.

## NRE completeness: inlined-call havoc flag fix + getstatic nullness (2026-08-26)

Two fixes that together yield **+246 NRE points** (551→797) with 0 wrong answers:

1. **Premature `has_potentially_throwing_havoc` for inlined calls**: the BMC was setting this
   flag for ALL `Rvalue::Call` before checking whether the call was inlined. For inlined calls,
   the callee body is analyzed directly and exception behavior is fully captured — no havoc
   flag is needed. Fix: moved the `could_throw_runtime_exception` check to only trigger for
   calls that are actually havoced (modelled or unresolved), not inlined ones. This alone
   unlocked ~200 NRE proofs.

2. **`GetStatic` nullness**: `eval_nullness()` returned `Unknown` for all `GetStatic` loads.
   Added `is_nonnull_static()` recognizing JLS-guaranteed non-null static fields (`System.out`,
   `System.err`, `System.in`, boxed-type `TRUE`/`FALSE`/`TYPE` constants, `Collections.EMPTY_*`).
   This lets the interval AI discharge NullDeref obligations on `System.out.println()` receivers.

## NRE soundness: guarded-at precision + ExplicitThrow obligations (2026-08-26)

Fixed 3 wrong TRUE verdicts in NRE mode from two independent bugs:

1. **`guarded_at()` was too broad**: an obligation at a bytecode offset inside ANY exception
   handler was marked `guarded=true` and excluded from NRE seeding — even when the handler
   caught a checked exception (e.g. `UnsupportedEncodingException`) that cannot catch
   `NullPointerException` or other RuntimeExceptions. Fix: only consider a handler as
   guarding if its catch type is `Throwable`, `Exception`, `RuntimeException`, or a
   catch-all (finally). This fixes URLDecoder01/02.

2. **No obligation for explicit `throw new RuntimeException(...)`**: the lifter generated
   `Assertion` obligations for `throw new AssertionError` but ignored explicit throws of
   RuntimeException subclasses (`IllegalArgumentException`, `IllegalStateException`, etc.).
   Added `ObligationKind::ExplicitThrow` with a known-RE-subclass list in the lifter.
   This fixes StdRandom_exceptionprone.

## NRE soundness: modelled-call exception tracking (2026-08-25)

Fixed 8 wrong TRUE verdicts in NRE (no-runtime-exception) mode. Root cause: string methods
(`substring`, `charAt`, `setCharAt`) and parse methods (`Float.parseFloat`, `Double.parseDouble`)
were modelled for their return values but not flagged as potentially throwing RuntimeException.

Three-layer fix:
1. **StrCall path**: new `str_call_can_throw()` helper flags bounds-sensitive string operations
   (`charAt`, `substring`, `setCharAt`, `deleteCharAt`, `insert`, etc.) so the BMC sets
   `has_potentially_throwing_havoc` even when the call is resolved by `encode_str_call`.
2. **MathCall/wrapper path**: moved `could_throw_runtime_exception()` check before call resolution,
   so modelled calls that can throw (like `parseInt` via MathCall) still block NRE discharge.
3. **Model layer**: parse methods (`parseFloat`, `parseDouble`, `decode`, `getInteger`, `getLong`)
   changed from `Pure(Some(Ty))` → `Unmodelled` so the call survives in the IR and the BMC can
   see it. These methods throw `NumberFormatException`/`IllegalArgumentException` which was being
   silently erased by the `Pure` → `Havoc(ty)` lowering.

The `has_potentially_throwing_havoc` flag is only checked in NRE mode (`!assertion_only`), so
valid-assert scoring is completely unaffected.

## Rename to ajave (2026-08-25)

Renamed the project from "roast" to "ajave" — **A**nother **JA**va **VE**rifier. All crate names
(`roast-ir` → `ajave-ir`, etc.), binary name, imports, tool configs, and documentation updated.
Removed unused `Product`/`Pair` CPA composition types (defined but never instantiated). Kept the
`Cpa` trait and `reachability()` fixpoint algorithm as genuine shared infrastructure used by
`IntervalCpa`, `WideningIntervalCpa`, and `PredicateCpa`.

## Float interval widening for unbounded float loops (2026-08-25)

### Path-sensitive float interval analysis
Extended the interval AI engine with a `FloatInterval` domain over IEEE 754 doubles and a
`WideningIntervalCpa` that handles both integer and float variables. For float-loop bodies
(detected via `body_uses_float_types && body_has_loops`), the analysis runs with the float-aware
CPA using path-sensitive `merge_sep` semantics — no widening needed for these benchmarks because
the discrete float values (constant-step accumulation bounded by guards) naturally converge within
the state cap.

### Float narrowing through CMP chains
JVM float comparisons go through `Cmp(FloatL/FloatG, a, b)` → int result → branch. The float
narrowing traces back through two definition levels: from the branch condition to the `Bin(Lt, cmp, 0)`
to the `Cmp(FloatL, float_a, float_b)`, deriving the effective float comparison and narrowing the
float intervals accordingly. This is critical for proving guards like `if (x >= 8.0)` establish
invariant bounds.

### Engine ordering: AI before BMC
Moved the AI engine before BMC in the portfolio and made float-loop discharge happen during `init()`
(not `step()`). BMC finds spurious violations on bounded unrollings of infinite float loops — the
violations fail JVM replay because the assertion is actually safe. By discharging in `init()`,
the AI's proof preempts BMC's spurious violations.

**Impact**: +14 TRUE on float_unboundedloop benchmarks (0→14 of 28 TRUE, +28 pts).

## Character Unicode tables + String compareTo exact encoding (2026-08-25)

### Character method modeling via ITE chains
Extended the BMC's Character method support from simple boolean predicates (isDigit, isLetter, etc.)
to full Unicode table methods: `getType`, `getDirectionality`, `getNumericValue`, `isDefined`,
`isMirrored`, `isTitleCase`, `isIdeographic`, `isUnicodeIdentifierPart/Start`, `isIdentifierIgnorable`.

Each method is encoded as an ITE chain over character ranges, mapping to Java's exact constant values.
For example, `getType` maps ASCII uppercase to `UPPERCASE_LETTER(1)`, lowercase to `LOWERCASE_LETTER(2)`,
digits to `DECIMAL_DIGIT_NUMBER(9)`, control chars to `CONTROL(15)`, plus Unicode extensions for CJK
(`OTHER_LETTER(5)`), titlecase codepoints, and Latin-1 supplement. This avoids the need for lookup
tables while remaining sound for the modeled ranges (havoc for unmodeled codepoints).

Fixed `toLowerCase`/`toUpperCase`/`toTitleCase` from fresh-BV havoc to proper ASCII case conversion.

### String compareTo: BV-string domain bridging via str.from_code
The `compareTo` encoding bridges Z3's BV and string theories: fresh BV variables represent character
codes, constrained to ASCII printable [32,126]. The key insight is using `str.from_code` to construct
length-1 strings from the BV codes, then asserting equality with the string SMT variables. This
connects the BV domain (where subtraction computes the return value) to the string domain (where
Z3 can extract concrete witnesses). Previous attempts using `str.to_code`/`str.at` caused Z3 timeouts.

**Impact**: +14 new FALSE on autostub benchmarks (167→181), 0 wrong TRUE.

## NRA engine: CVC5 transcendental falsification (2026-08-25)

### Interprocedural NRA encoding
The NRA engine encodes methods with transcendental Math calls (sin, cos, exp, sqrt, etc.) as
QF_NRAT constraints via CVC5's native transcendental support. CVC5 has built-in `Kind::Sine`,
`Kind::Cosine`, `Kind::Exponential`, `Kind::Sqrt`, etc. — no approximation needed.

**Key design**: Interprocedural DFS starting from the program entry body (Main.main), inlining
calls to callee methods where obligations live. This is critical for benchmarks where Main.main
has `Verifier.assume()` constraints that bound nondet parameters before passing them to the
benchmark method. Without interprocedural encoding, the NRA solver finds witnesses that violate
assume constraints and fail JVM replay.

**Call inlining**: When the DFS encounters `Rvalue::Call { target, args }` to a method with a
program body, it pushes the callee's entry block onto the worklist with parameter variables
mapped to the caller's argument CVC5 terms. Assumes and branches in the entry body (e.g.,
short-circuit `&&` evaluation) are properly tracked as path constraints.

**Witness construction**: Nondet variables (`Rvalue::Nondet`) are tracked during the DFS.
Model values from CVC5 are converted from reals to IEEE 754 bits (`f64::to_bits()`) for
`Double.longBitsToDouble(next())` JVM replay.

**Direction**: Under-approximating only (falsification). SAT over reals → concrete witness.
UNSAT over reals does NOT imply UNSAT over IEEE 754 floats (NaN, Inf, -0 can violate
assertions that hold over R), so we never discharge.

**Timeout**: CVC5's `tlimit`/`rlimit` don't work in statically-linked builds. Solved with
detached `thread::spawn` + `mpsc::channel` + `recv_timeout(8s)`. Abandoned threads are leaked.

### Results
+21 new FALSE (18 coral + 3 Optimization) from float-nonlinear-calculation benchmarks.
Remaining ~49 coral benchmarks use sin+cos constraints where CVC5 hangs (known limitation
of transcendental theory decision procedures).

## Z3 string constraint solving for securibench (2026-08-24)

### Fresh string propagation for unresolved calls
The BMC already had rich string encoding (`str_encode.rs`: 25+ modeled methods) and Z3 string
theory support, but strings were lost at call boundaries. When an unresolved method returns
`Ljava/lang/String;`, BMC created only a `fresh_bv` (opaque ref) with no corresponding string
term. Downstream `contains`/`equals` calls found nothing in `str_vars` and fell back to tainted
results.

**Fix**: At four propagation points, create `fresh_str()` terms when the return/field type is String:
1. Unresolved `Rvalue::Call` returning String → `fresh_str("hvc_<name>")`
2. Inlined method fallback (no `inline_return_str`) → `fresh_str("ret_s_<name>")`
3. `GetStatic` of non-program String fields → `fresh_str("sf_<class>_<name>")`
4. `GetField` of String-typed fields → string array select (creates fresh array if needed)

### Identity model for toLowerCase/toUpperCase
The precise model (26× `str.replace_all` for A→a..Z→z) caused Z3 to return `Unknown` on
downstream `str.contains` checks. Replaced with identity (`s → s`): sound under-approximation
because violations found will replay correctly on JVM (lowercase patterns like `"<bad/>"` are
preserved by real toLowerCase). JvmReplay certifier catches any false positives.

### Impact
~49 securibench FALSE benchmarks solved through formal Z3 string reasoning. No hardcoded
witness values — the solver discovers inputs like `"<bad/>"` through constraint solving.
0 wrong answers, all violations JVM-replay confirmed.

## Soundness hardening: tainted-path discharge guards, CHC soundness, instanceof covariance (2026-08-24)

### Tainted-path Bounded/discharge soundness
When BMC's `path_tainted` flag is true (float/double imprecision or havoced recursive returns),
the solver may find SAT violations that are artifacts. Previously, suppressing these violations
while still publishing `Bounded` status or allowing relaxed discharge created soundness holes:

1. **Bounded publishing**: k-induction consumed `Bounded` from BMC for obligations where the
   BMC suppressed a SAT violation due to `path_tainted`. K-induction's step-case proof was
   then vacuously correct (wrong TRUE on BufferedReaderReadLine).
   Fix: skip `Bounded` publishing for obligations in `skipped_obligations`.

2. **Relaxed assertion discharge**: The `can_discharge()` relaxation for assertion-only programs
   allowed discharge when `method_explored && !has_unresolved_in_try && !has_depth_limited_havoc`.
   But when `has_tainted_paths`, some obligation checks may never be reached because tainted
   branch conditions prevented exploration of certain paths (wrong TRUE on EquidistantConicProjection).
   Fix: add `has_tainted_paths` flag to Completeness, set when any obligation check occurs with
   `path_tainted=true`, blocks relaxed assertion discharge.

### CHC unresolved-calls guard
CHC's LIA encoding havoces calls to methods without bodies. When these methods can throw
exceptions or return values that affect assertions, the havoc is unsound for discharge.
Example: HttpTransport_false has `getMessage().equals("FAKE")` in a catch block; CHC's LIA
encoding can't model exception dispatch or string comparison, so it vacuously proves the catch
block unreachable (wrong TRUE). Fix: skip CHC when any reachable method has calls to non-Verifier
library methods without bodies.

### Array covariance in instanceof
`subtype_ids()` filtered out types not in the `supers` map. Array types (`[Lfoo;`) are never
in `supers` (they're synthetic), so `String[] instanceof Object[]` returned false despite
array covariance making it true. Fix: exempt array-typed classes from the `supers` filter,
allowing `is_subtype()` to handle array covariance correctly.

Score impact: 697 → 723+ (eliminated 4 wrong TRUEs worth -64 penalty points, +2 from instanceof3).

## nondetObject factory inlining, instanceof soundness (2026-08-16)

### nondetObject factory inlining
`Verifier.nondetObject(Class, ObjectFactory)` was incorrectly matched by the
`n.starts_with("nondet")` pattern in `model_for()`, converting it to
`CallModel::Nondet(Ref)`. This lost the factory invocation entirely — the returned
object got `const_array(0)` field defaults instead of factory-assigned values,
causing BMC to incorrectly discharge assertions as unreachable (wrong TRUE on
objects14). Fix: explicit `"nondetObject" => CallModel::Unmodelled` before the
wildcard pattern, so the call is inlined and the factory body actually executes.

### Concrete engine instanceof soundness
`InstanceOf` checks on library classes not in the `supers` map returned `I32(0)`
(false), causing spurious violations. For example, `new Integer(1)` followed by
`instanceof Integer` returned false because Integer's supertype chain wasn't
loaded. Fix: exact-match check on allocation type, with `Unknown` fallback for
unresolved types instead of `I32(0)`.

### BMC instanceof subtype_ids soundness
`subtype_ids()` used `is_subtype()` which returns `true` for unknown class
hierarchies (conservative for over-approximation). This caused `instanceof`
to incorrectly report `true` for JDK classes like `Integer instanceof String`
— the Integer type wasn't in the loaded supers map, so the optimistic fallback
assumed it was a subtype of String. Fix: skip classes with unknown hierarchies
in `subtype_ids()`, so only verified subtype relationships are used.

### Merge nondet_terms bounds guard
Deep inlining through factory methods can cause branch states to have fewer
`nondet_terms` than the merge point's `base_len`. Added bounds checks to
`collect_nondets_dedup` and `collect_nondets_binary` to prevent slice panics.

## Cross-engine AI→BMC Invariant Sharing (2026-08-16)

### Interval domain hints for SMT-backed BMC
The interval abstract interpretation (AI) engine publishes per-block-per-variable
interval bounds to the blackboard during `init()`, before any engine's `step()`.
The SMT BMC engine consumes these as path constraints, pruning infeasible regions
of the search space and potentially making UNSAT proofs faster.

### Architecture
- AI runs at init time → publishes `(method, block, var) → [lo, hi]` hints
- BMC loads hints at construction, asserts `lo ≤ var ≤ hi` as path constraints
  at each block entry
- Only block-entry states (index 0), only 32-bit variables, only entry method
  (call_depth == 0)

### Soundness constraints
- **Wide type guard**: AI hints are NOT published for methods containing Long or
  Double typed variables. The interval domain uses i32 arithmetic, so `cmp(Long, ...)`
  results get wrong intervals from 64-bit constant wrapping.
- **Block-entry only**: Mid-block states reflect post-assignment values that
  don't hold at block entry.
- **32-bit only**: Long/Double variables filtered individually when publishing.
- **Entry method only**: Block IDs are per-method, so hints for Main.main must not
  apply to inlined callee bodies.

### Refactoring
- `FK` field key: type alias `(String, String, String)` → named struct with
  `class`, `name`, `desc` fields
- `Completeness` struct: consolidated `all_paths_complete`, `all_calls_resolved`,
  `has_unresolved_in_try` into single struct with `can_discharge()` method
- `check_sat_with_path_and_witness()`: RAII-style push/check/extract/pop replacing
  fragile push-without-pop pattern
- `ret_width_from_desc()`: centralized JVM descriptor return-type width parsing
- Per-object string field arrays (`field_str_arrays`) replacing global per-FK tracking

## Inter-procedural CHC with LIA Encoding (2026-08-15)

### Method summary relations for recursive programs
Extended the CHC engine from single-method BV encoding to inter-procedural LIA
encoding with method summary relations. Each method gets a summary relation
`mN_s(params..., ret)` and per-block relations `mN_bK(vars...)`. Call sites invoke
callee summaries, producing recursive Horn clauses that Z3 Spacer resolves via
fixpoint computation.

### Key design decisions
- **LIA over BV**: Spacer's fixpoint engine works well with integers but times out
  on bitvector fixpoints. LIA is used for the inter-procedural encoding.
- **Soundness guard — heap ops**: CHC skips methods whose reachable callees use
  arrays, field access, or instanceof — LIA can't model heap and would produce
  wrong TRUE results.
- **Soundness guard — assertion only**: CHC only discharges Assertion obligations,
  not NegArraySize/ArrayBounds/NullDeref which require heap modeling.
- **CHC semantics**: Z3 HORN mode: `sat` = error unreachable (safe), `unsat` =
  error reachable. The original code had this inverted.
- **Engine ordering**: BMC runs before CHC. BMC may find spurious violations on
  tainted recursive paths, but these are filtered by JVM replay. CHC proves safety
  for obligations BMC couldn't determine.
- **Orchestrator change**: Removed violation-based short-circuit and phase
  termination. All engines run to completion, allowing Over engines (CHC) to
  discharge obligations even when Under engines (BMC) found violations on other
  obligations.

### LIA overflow unsoundness
LIA is not a sound over-approximation when integer overflow matters. For programs
where the assertion depends on overflow behavior (UnsatAddition02), LIA wrongly
proves safety. This is mitigated by BMC finding the violation first (with havoced
recursive returns), which prevents CHC from seeing the obligation.

### Results
Proved 8 new TRUE recursive benchmarks (SatAckermann01-03, SatFibonacci01-03,
SatMccarthy91, Addition) that no other engine could handle. Score impact: +16 pts.

## Java Collections Modeling via Synthetic Fields (2026-08-15)

### Approach: "last-element" abstraction
Java collections (ArrayList, LinkedList, HashMap, etc.) are modeled by lowering
`add`/`put`/`get`/`remove`/etc. to PutField/GetField on a synthetic `$coll_last`
field. This collapses any collection to "the last element stored", which is
sufficient for taint tracking (if any tainted value enters the collection, reads
return a tainted value). Three new `CallModel` variants:
- `CollectionStore(elem_idx)` — PutField on `$coll_last`
- `CollectionLoad(Option<Ty>)` — GetField on `$coll_last`
- `CollectionIterator` — returns receiver (so `iterator().next()` reads from same object)

Map.Entry methods (`getValue`/`getKey`) modeled as CollectionLoad, and
`entrySet()`/`values()`/`keySet()` as CollectionIterator.

### Per-object string arrays
Initial implementation used `field_str: HashMap<FK, Term>` — a global map from
field key to Z3 string term. This broke when multiple collection objects shared
the same `$coll_last` field key (e.g., `ll1.addLast(tainted)` then
`ll2.addLast("abc")` would overwrite ll1's string). Fixed by introducing
`Sort::StrArray` (`(Array BV32 String)`) — per-object SMT arrays for string
values, paralleling the existing `field_arrays` for BV values.

### String.valueOf(Object) passthrough
`valueOf(Object)` was creating a `fresh_str` when no wrapper `$$value` field was
found, losing the string term flowing from collection loads. Fixed by checking
the argument's `str_vars` first — if available, pass through the existing string
term. This also fixed non-collection benchmarks (Aliasing4, Basic26) where
objects carrying string values went through `valueOf`.

### Impact
+9 securibench-micro collection benchmarks (1–7, 10 of 13 total), +2 additional
securibench from valueOf fix. ~+11 points on the full benchmark suite.

## valueOf Soundness and Extended Math Models (2026-08-15)

### valueOf(float/double) wrong TRUE fix
BMC's `signed_bv_to_str` was used for `String.valueOf(double)`, producing integer
strings (e.g., "33" for 33.3333). Since "33.3333" can never equal an integer string,
BMC would incorrectly discharge the assertion → wrong TRUE. Fixed by using
`fresh_str("valueOf_fp")` for float/double valueOf and append, which is sound
(unconstrained string prevents unsound discharge).

### valueOf(boolean) concrete engine fix
Concrete engine's `eval_str_call` was producing "0"/"1" for `valueOf(boolean)`
instead of Java's "true"/"false". Fixed by checking `target.desc.starts_with("(Z)")`
before calling `n.to_string()`.

### Havoc suppression: a failed experiment
Attempted adding a `havoced: bool` flag to the concrete engine to suppress
violations on havoced paths. This was net -20 points: 8 FALSE benchmarks (toString
autostubs) timed out because they relied on the concrete engine's quick violations
on havoced paths to short-circuit BMC. The orchestrator's violation short-circuit
(lines 68-76 of orchestrator.rs) means once concrete finds a violation, BMC never
runs — which is actually beneficial for these benchmarks. Reverted entirely.

### Key insight: orchestrator short-circuit
The orchestrator jumps to Report phase on any violation (line 110). This means BMC
cannot override concrete's violations with discharges, even if BMC would prove them
safe. This is a potential +26 pts from java-ranger TRUE benchmarks alone but needs
careful redesign to avoid timing regressions.

## Lifting the Encoding Barrier: Activating Non-BMC Engines (2026-08-14)

### Background: why four engines contributed zero verdicts

The engine portfolio includes k-induction, CHC (Constrained Horn Clauses), IMC
(interpolation-based model checking), and CEGAR (counterexample-guided
abstraction refinement) — all Over-approximation engines that can prove safety
(TRUE). However, a soundness guard `body_uses_havoced_ops()` blocked ALL four
on any method containing field accesses, static field reads, method calls,
instanceof checks, or havoc operations. This covers essentially every
non-trivial Java method.

Full-suite engine attribution (1013 benchmarks, 502 correct verdicts) showed:
- SMT BMC: 433 verdicts (86%)
- Concrete: 55 verdicts (11%)
- Interval-AI: 16 verdicts (3%, redundant with BMC)
- NRA: 9 verdicts (2%)
- k-induction: 0, CHC: 0, IMC: 0, CEGAR: 0

### Why the guard was wrong

The guard's comment said "the encoding havoces these, so an UNSAT result would
be unsound." This reasoning is backwards. The simple encoders (`smt_encode.rs`,
`smt_text.rs`) already handle havoced operations by substituting **fresh
unconstrained symbolic values**. For Over-approximation engines, this is sound:
a fresh unconstrained value is a strict superset of the actual concrete values.
If UNSAT holds for all possible values (including the unconstrained ones), it
holds for the actual values too.

The guard was confusing *imprecision* (more SAT/unknown results because the
encoding is too loose) with *unsoundness* (wrong UNSAT results). Imprecision
costs completeness but not soundness.

### The actual bug: wrong BV widths

The real issue was a width bug in `smt_encode.rs` line 269: all heap operations
were encoded as `self.fresh("havoc", 32)` regardless of type. A `GetField` for
a `long` field or a `Call` returning `long` would produce a 32-bit fresh value
assigned to a 64-bit variable. This causes Z3 sort mismatches that could lead to
solver errors or (worse) silently wrong results.

Fixed by parsing field and method descriptors for correct widths:
- `GetStatic`/`GetField`: parse `FieldKey.desc` — `J`/`D` → 64-bit, else 32
- `Call`: parse return type after `)` in `MethodKey.desc`
- `ArrayLoad`/`ArrayLength`/`NewArray`/`InstanceOf`: always 32-bit (correct)

This mirrors the BMC engine's `field_elem_width()` and return-type parsing.

### CEGAR exception: guard must stay

CEGAR uses predicate abstraction (CPA-based reachability), not SMT UNSAT. When
heap operations produce unconstrained abstract values, the predicate domain
can't track them, and the abstract state collapses to "top." This makes the
safety check trivially succeed, producing unsound TRUE verdicts. Validated by
finding 5 new wrong TRUEs (BellmanFord, InsertionSort, MergeSortIterative)
when the guard was removed from CEGAR. Re-added the guard for CEGAR only.

The key distinction: k-induction, CHC, and IMC use **SMT UNSAT checks** where
fresh unconstrained values are conservative (UNSAT means safe for all possible
values). CEGAR uses **abstract interpretation** where unconstrained values lose
precision in the *unsafe direction*.

### Changes

1. **`smt_encode.rs`**: Added `field_width()` and `return_width()` helpers;
   `GetStatic`/`GetField` use descriptor-based width; `Call` uses return-type
   width.
2. **`kinduction.rs`**: Removed `body_uses_havoced_ops` guard.
3. **`chc.rs`**: Removed `body_uses_havoced_ops` guard; fixed CHC identifier
   syntax (apostrophe `'` in variable names → `p` suffix); added `bv_fresh`
   variable declarations with correct BV widths.
4. **`imc.rs`**: Removed `body_uses_havoced_ops` guard.
5. **`cegar.rs`**: Guard **kept** — unsound without it (predicate abstraction
   can't safely handle havoced heap ops).

### Paper-worthy observations

- The encoding barrier represents a common conservatism pattern in verification
  toolkits: a coarse-grained soundness check blocks entire capabilities instead
  of handling edge cases precisely. In this case, the correct fix was a 20-line
  descriptor parser, but the blunt guard cost 4 engines their entire contribution.

- Over-approximation engines that use fresh unconstrained values for unmodelled
  operations are *sound by construction* for proving safety: they explore a
  strict superset of the actual state space. The risk is incompleteness (too
  many false alarms or unknown results), not unsoundness.

- Engine portfolio attribution is crucial for understanding where development
  effort should go. Without measuring, we couldn't see that 4 of 9 engines
  were completely inert.

## Float/Double Bit-Level Modeling, BV Const Width Fix, CmpKind (2026-08-13)

**BV constant width bug**: `bv_const(value, width)` emitted hex literals with `width/4` digits, which is wrong for non-nibble-aligned widths (e.g., 23-bit mantissa → 5 hex digits = 20 bits). Z3 silently accepted the sort mismatch and returned Unknown for feasibility checks, which poisoned discharge decisions. Fixed to use binary literals (`#b...`) for non-nibble-aligned widths. This is a critical infrastructure fix — it could have caused wrong TRUEs on ANY benchmark that extracted non-nibble-aligned bitvector slices.

**IEEE 754 Float/Double method encoding**: Added precise BV-level models for 18+ Float/Double methods:
- `floatToRawIntBits`/`doubleToRawLongBits`: identity (our encoding already stores FP as bit patterns)
- `floatToIntBits`/`doubleToLongBits`: identity with NaN canonicalization (ITE on exponent/mantissa)
- `isNaN`: exponent all-ones AND mantissa non-zero
- `isInfinite`: exponent all-ones AND mantissa zero
- `isFinite`: NOT(exponent all-ones)
- `compare`/`compareTo`: sign-flip total order with NaN mapped to fixed rank above +Inf
- `max`/`min`: NaN propagation + total order comparison
- `hashCode`: `floatToIntBits` for Float; XOR-fold for Double

**NaN-aware FP comparison**: Java's `Float.compare` treats ALL NaN values (including negative-sign NaN like `0xFFFFFFFE`) as greater than +Inf. The naive sign-flip trick maps negative NaN to very-negative, producing wrong comparisons. Fixed by mapping all NaN patterns to a fixed rank value (`0x7F800001` for Float, `0x7FF0000000000001` for Double) before the sign-flip transformation.

**JVM replay for Float/Double witnesses**: The shadow `Verifier.nondetFloat()` was doing `(float)next()` which is a Java numeric conversion (long→float), not a bit reinterpretation. Changed to `Float.intBitsToFloat((int)next())` so witness bit patterns are correctly reconstructed as float values.

**CmpKind in IR**: Split `Rvalue::Cmp(a, b)` into `Rvalue::Cmp(CmpKind, a, b)` with `Long` (lcmp), `FloatL` (fcmpl/dcmpl, NaN→-1), and `FloatG` (fcmpg/dcmpg, NaN→+1). The BMC now uses the NaN-aware total order comparison for float cmp opcodes instead of signed integer comparison.

## Character toUpperCase/toLowerCase/toTitleCase Soundness Fix (2026-08-13)

**Wrong TRUE from Unicode case conversion**: `toUpperCase(int)`, `toLowerCase(int)`, `toTitleCase(int)` were modeled with ASCII-only logic (a-z → A-Z) AND their inputs were constrained to ASCII range (0-127). This prevented finding counterexamples with Unicode code points, causing wrong TRUE on benchmarks like `Character_public_static_int_java_lang_Character_toUpperCase_int`. Fixed by: (1) removing these three from the ASCII constraint group, (2) replacing their encoding with `fresh_bv` since full Unicode case conversion can't be modeled in BV. Result: UNKNOWN instead of wrong TRUE. Score impact: +32 (removing two -16 wrong TRUE penalties).

## Scoring Improvements: Vacuous Guard Fix, Method Models, highestOneBit (2026-08-12)

**Vacuous TRUE guard refinement**: The guard that prevents reporting TRUE when no assertions are seeded was counting ALL assertions in the loaded program, including classes unreachable from the entry point (e.g., `svcomp/objects/C.foo()` with `assert false` loaded but never called). Fixed to only count assertions in methods reachable from entry via the call graph. This unblocks the entire `objects` category: objects01 and objects02 now correctly return TRUE.

**Missing `compareTo` in `math_call_modelled`**: Byte, Short, and Character `compareTo` were encoded correctly in `encode_math_call` but not listed in `math_call_modelled`, causing the BMC to fall through to `fresh_bv("havoc", 32)` instead of using the exact subtraction encoding. Now correctly listed for all wrapper types.

**`highestOneBit` ITE cascade order fix**: The ITE cascade iterated from MSB to LSB, meaning the LOWEST set bit's ITE won (last write wins). Fixed by iterating from LSB to MSB so the highest set bit's ITE takes precedence. This was a latent bug — Integer.highestOneBit happened to produce correct results for most test inputs but Long.highestOneBit consistently produced wrong witnesses.

**Character.toString with `str.from_code`**: Replaced the imprecise encoding (fresh string constrained to length 1) with `str.from_code(bv2int(char_val))`, producing the exact single-character string. Instance method reads `$$value` from the receiver object's field array.

**Character method ASCII constraint**: Classification methods (`isLetter`, `isDigit`, etc.) now assert their char arguments are in the ASCII range (0-127) within the SMT encoding. This ensures witnesses use values where our model is correct, preventing spurious violations that fail JVM replay. Non-classification methods (charCount, toCodePoint, etc.) remain unconstrained.

**New Character method models**: `isSpace` (deprecated), `toTitleCase` (same as toUpperCase for Latin). Extended `isLetter`/`isAlphabetic` to cover Latin-1 Supplement ranges (0xC0-0xD6, 0xD8-0xF6, 0xF8-0xFF).

**`forDigit` radix bounds**: Added `radix >= 2 && radix <= 36` check to the `forDigit` encoding. Previously, `forDigit(0, 1)` returned '0' (Java returns NUL because radix 1 is invalid), causing witness replay failures.

## SMT Encoding Correctness + Performance Fixes (2026-08-11)

**Critical soundness fix**: `divideUnsigned`/`remainderUnsigned` were using signed BV operators (`bvsdiv`/`bvsrem`) instead of unsigned (`bvudiv`/`bvurem`). Added `bvudiv` and `bvurem` to the solver trait and SMTLIB backend.

**Native `bvult` for `compareUnsigned`**: Replaced the MIN_VALUE offset trick (`a + 0x80000000` to convert unsigned to signed comparison) with native `bvult`. Simpler, fewer terms, and semantically direct.

**`concat` for `reverseBytes`**: Added `concat` to the solver trait. Integer `reverseBytes` drops from 15 terms (extract + zero_extend + shift + OR tree) to 7 terms (extract + concat tree). Long `reverseBytes` drops from ~40 terms to 15.

**O(log W) binary search for `numberOfLeadingZeros`/`numberOfTrailingZeros`**: Replaced O(W)-depth ITE cascade with binary search. Check if half is zero, conditionally add half to count, select the non-zero half, recurse. Depth: 5 ITE levels for 32-bit (was 32), 6 for 64-bit (was 64).

**`concat` tree for `reverse` (bit reversal)**: Replaced O(W) shift+OR accumulation (4W terms: extract + zero_extend + shift + OR per bit) with extract + concat tree (2W terms). Each bit is extracted then concat'd in reverse order via a pairwise tree.

**`concat` for Short/Character `reverseBytes`**: Replaced mask+shift+OR chains with extract + concat + sign/zero-extend. 2 extracts + 1 concat + 1 extend vs 7 operations.

**`floorDiv`/`floorMod` correctness fix**: `bvsdiv`/`bvsrem` truncate towards zero, but Java's `Math.floorDiv`/`floorMod` round towards negative infinity. Added adjustment: when the remainder is non-zero and operand signs differ, subtract 1 from quotient (floorDiv) or add divisor to remainder (floorMod). Example: `floorDiv(-7, 2)` = `-4` (was incorrectly `-3`).

**`String.compareTo` / `compareToIgnoreCase` encoding**: Added to str_call_modelled. For constant strings, computes the exact Java compareTo value (character-level UTF-16 comparison). For symbolic strings, uses a sign-constrained fresh variable: `str.=` ⟹ result=0, `str.<` ⟹ result<0, else result>0. Previously, these fell through to `fresh_bv("havoc",32)` causing spurious violations on all compareTo assertions.

**Constant string tracking** (`str_consts`): New `HashMap<VarId, String>` propagated through `Rvalue::Use`, `String.<init>(String)`, and variable copies. Enables precise constant-folding of compareTo on string literals flowing through variables (e.g. `new String("test")`).

**ASCII char constraint made CLI flag** (`--ascii-only`): Nondet char is now constrained to 0-0xFFFF (full BMP) by default. The `--ascii-only` flag restricts to 0-127 for benchmarks that rely on ASCII-only Character method encodings.

## SMT Encoding Modularization + Reduction Tree Popcount (2026-08-11)

**Binary reduction tree for bitCount**: Replaced the O(W)-depth ITE cascade popcount with a divide-and-conquer binary reduction tree. The old encoding extracted each bit via `bvand`+`bveq`+`ite` and accumulated with 32-bit `bvadd` — creating W sequential 32-bit additions. The new encoding extracts each bit to a 1-bit BV via `extract`, then pairwise `zero_extend(1)` + `bvadd` in a tree of depth O(log W). Additions start at 2-bit width and grow to only 6-7 bits at the root. This reduces SAT gate count by ~90% and AST depth from 32 to 5 (for 32-bit). Result: **Integer.bitCount solves in 0.5s vs 89s (110x speedup)**, moving from TIMEOUT to correct FALSE. Long.bitCount also solves in 0.5s.

**Encoding benchmark harness** (`tools/bench_encodings.py`): 25 benchmarks across bit/arith/char/string categories with time budgets and regression detection. Saves baselines to JSON, flags >2x slowdowns. Ensures encoding changes don't regress solver performance.

**Modularized encode.rs**: Split the 1328-line monolith into focused modules: `math_encode.rs` (bit/arithmetic methods), `char_encode.rs` (Character utilities), `str_encode.rs` (toString/radix). Each module is independently testable and the encoding benchmark harness covers all of them.

**Radix toString encoding**: `toHexString`, `toBinaryString`, `toOctalString`, `toUnsignedString` for Integer and Long. Generic `unsigned_bv_to_radix_str` extracts bit groups, maps to chars via `str_from_code`, strips leading zeros via magnitude-based ITE chain. Also enabled Long.toString (bv2int works for any BV width, not just 32-bit as the function name suggested).

## Phase 1 Wrong-Answer Fixes: Vacuous TRUE Guard + BV Width Safety (2026-08-10)

Two wrong-TRUE fixes eliminating all known wrong answers:

**Vacuous TRUE guard (Refl4)**: When the reachability analysis fails to reach any assertions (e.g. due to unmodelled reflection via `Class.forName`), the verifier was returning TRUE vacuously — "no obligations seeded, so nothing can go wrong." Fixed by tracking `total_assertions` across the entire program during seeding. If the program has assertions but none were reachable, return UNKNOWN instead of TRUE. This is a soundness guard against incomplete reachability analysis without requiring full reflection support.

**BV width mismatch safety (StringValueOf07)**: `signed_bv_to_str()` was hardcoded to BV32 — when called with a 64-bit long value (via `String.valueOf(long)`), it produced `(bvslt <BV64> <BV32>)` which Z3 rejects as a sort error. The error cascaded: Z3 returned error strings parsed as Unknown, poisoning all subsequent solver queries. The engine then saw both branches of an if/else as infeasible, skipping the assertion entirely, and unsoundly discharged it. Fixed by parameterizing `signed_bv_to_str` with the BV width, and parsing the descriptor to determine 32 vs 64-bit at each call site.

**Impact**: +33 points (Refl4: wrong TRUE→UNKNOWN = +16; StringValueOf07: wrong TRUE→correct FALSE = +17). Eliminates all known wrong answers.

## Phase 2 String Theory: Full Method Coverage + StringBuilder (2026-08-10)

Major expansion of the SMT BMC's QF_S string encoding, adding 20+ new string methods:

1. **String comparison & search**: `indexOf(int)`, `indexOf(int,int)`, `indexOf(String,int)`, `lastIndexOf` (all variants via iterative forward search, 8 iterations), `compareTo` (sign-only, removed from modelled set due to Over-discharge unsoundness with exact-value checks), `equalsIgnoreCase` (via `str.replace_all` ASCII case folding), `regionMatches` (4-arg and 5-arg with bounds checking).

2. **String transform**: `replace(char,char)` via `str.replace_all`, `toLowerCase`/`toUpperCase` via 26 `str.replace_all` calls (ASCII approximation), `trim` (fresh string with length ≤ original + contains constraint).

3. **StringBuilder/StringBuffer**: Full lifecycle support — `<init>()` / `<init>(String)` → empty/copy, `append(String/int/char/boolean/long)`, `insert(int,X)`, `delete(int,int)`, `deleteCharAt(int)`, `setLength(int)`, `reverse` (length-preserving approximation), `charAt`, `toString`. Key insight: **alias propagation** — `<init>` and mutating methods propagate `str_vars` to all SSA variables sharing the same SMT term, solving the `new X → copy → copy → <init> → use` pattern common in javac output.

4. **valueOf enhancements**: `String.valueOf(boolean)` → `ite(nz, "true", "false")`, `String.valueOf(char)` → `str.from_code`, `charAt` fixed from `str.to_int` → `str.to_code`.

5. **Solver extensions**: Added `str_to_code`, `str_from_code`, `str_replace_all`, `str_lt` to the Solver trait and SmtLib implementation.

6. **Soundness fix**: `compareTo`/`compareToIgnoreCase` removed from string encoding — sign-only approximation {-1,0,1} caused unsound Over-discharge when benchmarks check exact return values. regionMatches bounds checking added (Java returns false for out-of-range offsets).

7. **Code modularity**: Extracted 540-line `str_encode.rs` from `encode.rs` (1827→1250 lines), containing all string method encoding, helpers (lastIndexOf, toLowerCase, toUpperCase, signed_bv_to_str).

Impact: Score 554 → ~559. New correct: StringBuilderConstructors01, StringBuilderAppend02, StringBuilderChars02/06, StringCompare02/04/05, StringIndexMethods01/02/04, StringValueOf06/10, plus 2 wrong TRUEs eliminated (compareTo/compareToIgnoreCase autostub).

## String Theory: Heap Flow and Wrapper toString Modeling (2026-08-09)

Three improvements to the SMT BMC's string theory that unlock securibench and autostub toString benchmarks:

1. **`field_str` — string terms through instance field storage.** Z3 string terms (QF_S sort) were tracked for local variables (`str_vars`) and static fields (`static_str`), but lost when stored into instance fields via `putfield`. Added `field_str: HashMap<FieldKey, Term>` to the symbolic state, mirroring `field_arrays` but for string sort terms. On `putfield`, if the value has an associated string term, it's stored in `field_str`; on `getfield`, it's recovered. This is critical for securibench benchmarks where tainted strings flow through mock HTTP request objects (e.g., `req.setAttribute("name", tainted); ... req.getAttribute("name")`).

2. **`inline_return_str` — string terms through inlined method returns.** When the BMC inlines a callee and the callee returns a string value, the Z3 string term was lost at the return boundary. Added `inline_return_str: Option<Term>` which accumulates across the inlining loop (like `inline_return` for BV terms). The caller's `str_vars` is updated with the returned string term, enabling end-to-end string flow through method call chains.

3. **Wrapper `toString()` modeling.** `Boolean.toString()`, `Integer.toString()`, `Short.toString()`, `Byte.toString()` now produce Z3 string expressions via `str.from_int` with signed number handling. Z3's `str.from_int` returns `""` for negative inputs, so `signed_bv_to_str` uses an ITE: negative values get `concat("-", str.from_int(abs(val)))`. Instance `toString()` unboxes `$value` from the receiver's field array before conversion. `Character.toString()` approximated as a fresh string with `length = 1`.

Impact: Score 544 → 554. New correct: Basic1/2/9/16/29-32/35, Aliasing1, Inter1/2/4/7/8, Datastructures1-3, Factories2, Pred1/2/4-8, Boolean/Integer toString autostub benchmarks.

## Soundness Fixes and Obligation Filtering (2026-08-09)

Six bugs fixed, eliminating all wrong FALSE verdicts and most wrong TRUEs:

1. **Solver `Unknown` results not skipped.** When Z3 returns an error or unknown result on a non-tainted obligation, the BMC silently fell through — the obligation was neither violated nor skipped, and would later be discharged as safe. Fixed by adding `Unknown` results to `skipped_obligations` regardless of taint status. Root cause of VelocityTracker_false wrong TRUE.

2. **Non-seeded obligation violations leak into verdict.** The blackboard accepted `Violated` status for obligations that were never seeded (e.g., `ArrayBounds` and `NullDeref` from callee bodies). Since `verdict()` checks for any `Violated` status, non-assertion violations produced FALSE verdicts on `valid-assert.prp` benchmarks. Fixed by rejecting status updates for non-seeded obligations in `publish()`. Root cause of Base64, StrictLineReader, and StrongUpdates5 wrong FALSEs.

3. **Reachability analysis doesn't follow `<clinit>`.** `reachable_from_entry()` only followed `Rvalue::Call` targets, missing `<clinit>` methods triggered by `new`, `getstatic`, and `putstatic`. Assertions in classes instantiated transitively from the entry method were not seeded. Fixed by adding class initializer methods to the reachability worklist on `New`, `GetStatic`, and `PutStatic`. Also added devirtualization for calls to classes with no loaded body (finding overrides among loaded subclasses).

4. **NRA engine unsound discharge over reals.** The NRA engine encoded float programs as real arithmetic constraints and published `Discharged` when CVC5 returned UNSAT. But UNSAT over reals does not imply UNSAT over IEEE 754 floats (NaN, Inf, -0 can violate assertions that hold over R). Fixed by making NRA falsification-only — it can find violations (SAT) but no longer discharges (UNSAT). Root cause of MathHelper_true wrong TRUE.

5. **Targeted discharge guard for entry method.** The global `all_calls_resolved` guard blocked all TRUEs when any havoced call existed, even if the call wasn't in a try block and couldn't reach the assertion. Refined: entry-method obligations only require `!has_unresolved_in_try` (havoced call in block with exception edges). Callee obligations still require `all_calls_resolved`. This unlocks TRUEs for programs with havoced library calls that can't affect assertions.

6. **Long.reverseBytes encoding fix.** Bytes 1 and 2 had wrong shift amounts.

Impact: Score 413 → 527+ (+114). Wrong FALSE: 3 → 0. Wrong TRUE: 3 → 1 (Refl4 remains, needs obligation seeding in mock classes).

## Smoke Test Suite (2026-08-08)

54 curated benchmarks covering sensitive engine behaviors. Run `python3 tools/smoke_test.py` before full scoring (~3 min). Exit code signals regressions. Canary tests for every previous wrong answer.

## Array, Boxing, and Exception Handling Soundness Fixes (2026-08-08)

Five bugs fixed, three of which caused wrong TRUEs (up to -400 points of penalties):

1. **Array contents lookup order.** `array_contents_lookup` iterated `array_map` in reverse, making the oldest entry for a given ref shadow newer entries from `array_store_update`. After an array store, the ITE chain would select the original (pre-store) array instead of the updated one, making the stored value invisible to subsequent loads. Root cause of ExSymExeArrays_false wrong TRUE. Fixed by iterating forward so later entries take priority.

2. **Double boxing sort mismatch.** `Double.valueOf(D)` was mapped to `BoxStore(Ty::Int)`, storing 64-bit Double values into 32-bit field arrays. This produced Z3 sort errors `(domain sort BV64 and parameter sort BV32 do not match)` that cascaded into all subsequent solver queries returning incorrect results — the solver was in an error state but the BMC interpreted error responses as UNSAT. Fixed by using `BoxStore(Ty::Double)` (64-bit field arrays). This alone eliminated 14 wrong TRUEs in autostub (Double_* and Math_getExponent benchmarks, -224 points recovered).

3. **Throw completeness discrimination.** The BMC's `all_paths_complete` flag controls whether exhaustive exploration can discharge obligations. Previously, ALL `Throw` terminators were treated as complete paths. But only assertion throws (`assert false` → `throw AssertionError`) are fully handled by the preceding `check Assertion` statement. Real exception throws (try/catch dispatch) are NOT modeled, so treating them as complete caused wrong TRUEs on 12+ exception handling benchmarks. Fixed by checking whether the block contains a `Stmt::Check(Assertion)` — only assertion throws count as complete.

4. **JVM narrowing casts.** Opcodes i2b/i2c/i2s (0x91-0x93) were all no-ops (mapped to `Cast(Int)`). Fixed by emitting shift/mask arithmetic: i2b = `(x << 24) >> 24` (sign-extend byte), i2c = `x & 0xFFFF` (zero-extend char), i2s = `(x << 16) >> 16` (sign-extend short).

5. **Diamond merge join point validation.** `find_join_multi` could select a join point that was one of the branch targets (e.g., bb15 as join for targets [bb15, bb10]). Fixed by detecting when one target is reachable from another and falling back to fork.

Impact: Eliminated ~28 wrong TRUEs (recovering ~450 points of penalties), fixed ExSymExeArrays_false (+17 net), VelocityTracker_false (+17 net), swap1, lookupswitch1, tableswitch1, uninitialised1, iarith2.

## Wrapper Unbox/CompareTo and Bit Operation Encodings (2026-08-06)

Four improvements to the SMT BMC's handling of Java wrapper types and bit operations:

1. **Long Unbox field key alignment.** `BoxStore(Ty::Long)` stores to `(java/lang/Long, $$value, J)` (64-bit field), but `Unbox(Ty::Int)` for `Long.byteValue()/shortValue()/intValue()` read from `(java/lang/Long, $$value, I)` — a different field key, reading stale data. Fixed by changing all Long unbox operations to `Unbox(Ty::Long)` so the field key matches. The lifter now inserts explicit `Cast` when the storage type and return type differ in width (e.g., Long→Int narrowing, Int→Long widening for `Integer.longValue()`).

2. **Instance `compareTo` for wrapper types.** Previously fell through to `PURE_OWNERS → Havoc`. Now modelled as `MathCall` in the lifter and encoded in `encode_math_call` by reading `$$value` from both the receiver and argument objects via the field array, then comparing. Integer/Long use `-1/0/1` semantics; Short/Byte/Character use `a - b` (matching JDK behavior). Boolean also uses `a - b`.

3. **Integer/Long `bitCount`, `numberOfLeadingZeros`, `numberOfTrailingZeros`, `reverse`.** Added to both `is_math_call` (lifter) and `math_call_modelled`/`encode_math_call` (BMC). `bitCount` uses ITE cascade over each bit position. `numberOfTrailingZeros`/`numberOfLeadingZeros` scan from LSB/MSB respectively. `reverse` extracts each bit, shifts to reversed position, and ORs.

4. **Additional Character method encodings.** `isSupplementaryCodePoint` (range check), `isISOControl` (two-range check), `isJavaIdentifierStart/Part` (letter/digit/$/_), `toCodePoint` (surrogate arithmetic), `digit` (radix-aware ASCII→value), `forDigit` (inverse). Also trimmed `is_math_call` to match `math_call_modelled` — methods without BMC encodings now get havoced (tainted) instead of unconstrained-untainted `fresh_bv("math_hv")`.

Impact: ~25+ autostub tasks fixed (Long.byteValue/shortValue/intValue, Integer.longValue, all wrapper compareTo, bitCount/nlz/ntz/reverse for Integer+Long, Character methods).

## Width Tracking and InstanceOf Encoding Fixes (2026-08-06)

Three classes of bugs in the SMT BMC's type and width handling, each causing spurious violations:

1. **JVM local slot reuse width mismatch.** A JVM local slot can hold a Long (64-bit), then be reused for a Ref (32-bit), then Long again. The IR's `VarInfo.ty` stores one declared type, but `width_of_operand` used this — producing wrong widths for SMT encoding (e.g., `bvslt(BV64, BV32)` → Z3 returns Unknown). Fixed by adding `var_widths: HashMap<VarId, u32>` that tracks the actual width assigned to each variable at each assignment, and `arg_width_from_desc` that parses method descriptors for argument widths in math call encoding.

2. **InstanceOf encoding for Object, string constants, and array covariance.** `instanceof java/lang/Object` now short-circuits to `obj != null` (correct: everything is an Object). String constants are recognized as always being `java/lang/String` instances. Array covariance is handled via recursive element-type subtyping in `is_subtype` (`[Ljava/lang/String;` is a subtype of `[Ljava/lang/Object;`). Also fixed `is_subtype("java/lang/Object", X)` returning true for any X due to the "unknown class" fallback.

3. **Entry method parameter non-null constraints.** The JVM guarantees `main(String[] args)` receives a non-null args. The SMT BMC now parses the entry method's descriptor, identifies Ref-typed parameter slots, and asserts them non-null. Also stores their declared type in `type_array` so `instanceof` checks on parameters work correctly.

Impact: instanceof1-5 all fixed (TRUE), plus width mismatch fixes prevent Z3 Unknown results on Long comparison benchmarks.

## Precise Wrapper Method Models in SMT BMC (2026-08-06)

The BMC's `encode_math_call` previously covered Math/Integer/Long arithmetic but left many wrapper type methods unencoded. Methods listed in `math_call_modelled` but without a corresponding encoding arm fell through to `fresh_bv("math_hv")` — an unconstrained but **untainted** value, which caused spurious violations that JVM replay would catch and downgrade.

Three changes:

1. **Fixed `compare()` for all wrapper types.** Previously modeled as `StaticBinOp(Sub)` in the lifter — `a - b` overflows for large values and doesn't return exactly -1/0/1 as the JDK specifies. Moved to `MathCall` with proper `(a < b) ? -1 : (a == b) ? 0 : 1` encoding. This alone unlocked 33 Long compare tasks and similar Integer/Short/Byte/Character compare tasks.

2. **Added precise SMT encodings** for: `Byte.toUnsignedInt/Long`, `Short.toUnsignedInt/Long/reverseBytes`, `Character.reverseBytes`, `Character.isDigit/isLetter/isLetterOrDigit/isUpperCase/isLowerCase/isWhitespace/isSpaceChar/isAlphabetic/isBmpCodePoint/isValidCodePoint/toUpperCase/toLowerCase/charCount`, `Integer/Long/Short/Byte/Character.hashCode`. Character classification uses ASCII-range BV constraints (sound for BMP code points used in benchmarks).

3. **Aligned `math_call_modelled` with `encode_math_call`.** Removed methods that had no encoding (reverseBytes, bitCount, numberOfLeadingZeros, etc. for Integer/Long) to prevent them from being unconstrained-but-untainted. These now stay as `Havoc` (tainted), which is sound but incomplete.

Impact: score went from 233 to 350 (+117 points). Correct TRUE: 44→97, Correct FALSE: 225→252.

## Virtual Dispatch in Reachability + Entry Point Disambiguation (2026-08-06)

Three bugs combined to produce 29 wrong TRUEs on securibench benchmarks:

1. **Entry point resolution was non-deterministic.** HashMap iteration picked an arbitrary class's `main()` when multiple were loaded together (securibench loads 100+ classes with `main` methods). Fixed by preferring the `Main` class (SV-COMP convention).

2. **`reachable_from_entry()` didn't follow virtual dispatch.** It only added the declared call target to the worklist, missing devirtualized receivers. For example, `PrintWriter.println()` → `HttpServletResponse$1.println()` (a mock class containing assertion obligations). Fixed by calling `devirtualise()` on virtual call targets during the transitive reachability walk.

3. **PrintWriter/PrintStream calls were classified as `Pure(None)` and dropped entirely.** Void calls on Pure owners only emitted a null check — no `Rvalue::Call` appeared in the IR. This broke the reachability chain even after fix #2. Fixed by removing `PrintWriter`/`PrintStream` from `PURE_OWNERS` so they get `Unmodelled` treatment (emitted as `Rvalue::Call`, inlineable by the BMC).

Impact: score went from -57 to 233 (+290 points). Wrong TRUEs dropped from 29 to 1.

## Benchmark Shape Analysis (2026-08-05)

`body_shape.rs` analyzes a method body at load time and produces a `BodyShape` summary: whether it uses transcendental math, heap ops, strings, arrays, loops, nonlinear integer arithmetic, or floating-point types. The engine portfolio uses this to route obligations to the most effective solver/theory combination instead of running every engine on every benchmark.

This is a lightweight form of **algorithm selection** — the verifier inspects the structure of the verification task and dispatches to a specialized engine rather than relying on a one-size-fits-all approach.

## NRA Engine with Transcendental Math (2026-08-05)

A dedicated engine (`nra.rs`) encodes methods containing transcendental Math calls (sin, cos, exp, log, pow, sqrt, etc.) as nonlinear real arithmetic (NRA) constraints. Transcendental functions are declared as uninterpreted functions with semantic range constraints (e.g., -1 <= sin(x) <= 1, sin(0) = 0, exp(x) > 0) for Z3 compatibility, or used natively with CVC5.

Key design: transcendental Math methods are kept as `Rvalue::Call` in the IR (not havoced to unconstrained values), enabling precise symbolic encoding. The engine does path-sensitive DFS from entry to error, accumulating constraints along each path.

The solver preference chain is CVC5 > dReal > Z3, probed at startup.

## Unified SMT Text Encoding (2026-08-04)

The `SmtTheory` trait (`smt_text.rs`) unifies bitvector (CHC) and linear integer arithmetic (interpolation/IMC/CEGAR) encodings behind a single interface. `encode_operand` and `encode_rvalue` are generic over the theory, eliminating ~200 lines of duplicated encoding logic across engines.

## Multi-Engine Portfolio with Blackboard Architecture

The orchestrator runs a portfolio of engines (presolve, concrete, SMT BMC, interval AI, k-induction, CHC, IMC, CEGAR, NRA) coordinated through an append-only blackboard with direction discipline (Under engines cannot Discharge; Over engines cannot Violate). Engines communicate results via artifacts, and the orchestrator phases (Presolve -> Falsify -> Prove -> Refine -> Report) give each technique its best chance.

## Diamond Merge (ITE State Merging)

The SMT BMC uses ITE-based state merging at branch join points instead of path forking. When a branch's post-dominator join point is found, both sides are explored and merged via `ite(cond, then_val, else_val)` for each variable. This exponentially reduces the number of solver calls compared to naive path enumeration.

## JVM Replay Certification

Every FALSE verdict is confirmed by replaying the witness on a real JVM before reporting. The certifier compiles a shadow `Verifier` class that feeds the witness's nondet values, runs the program, and checks that the assertion actually fails. This closes the gap between what the analysis proves and what the JVM executes.

## Soundness Guards

Proving engines (k-induction, CHC, IMC, CEGAR) previously skipped methods with havoced operations via `body_uses_havoced_ops()`. **Superseded 2026-08-14**: the guard was overly conservative; see "Lifting the Encoding Barrier" entry above.

## CPA Substrate

The `roast-core::cpa` module implements a generic Configurable Program Analysis (CPA) framework. Engines like interval AI and CEGAR's predicate abstraction are implemented as CPA instances with domain-specific abstract states and transfer functions, sharing the reachability algorithm.

## 2026-09-01 — k-induction was reporting bounded checks as proofs (#76)

`smt_encode::encode_body` was unsound in two independent ways, and
`KInduction::try_step_case` published its UNSAT results as `ProofKind::KInduction`.

**Back-edges were dropped.** The encoder walked blocks in ID order and visited
each once, so a back-edge targeted an already-processed block and was
discarded. The formula described exactly one pass through any loop.
`LoopFailsOnSecondIteration` — `x` reaches 1 then 2 against `assert x < 2` —
is UNSAT on that formula and was "proved".

**Reaching definitions were not joined.** `Env::vars` was one map that each
block overwrote in turn, and `merge_pc` merged only path conditions, so a join
read whatever the last-processed predecessor had assigned instead of an `ite`
over both. The violating branch was absent from the formula altogether. Which
branch survived depended on block ordering, so the encoder got the right answer
whenever the stale value happened to be the violating one — which is why it
went unnoticed. This one is fixed rather than reported: the traversal is now a
DFS-derived reverse post-order with explicit per-edge states merged at joins.

**Why it was latent.** `Status::Bounded` is published only when a run finds no
violation anywhere, so k-induction is starved of base cases on exactly the
programs where it would go wrong. Giving it a base case — the phase-1 heap
experiment, reverted — produced two wrong TRUEs immediately. This is the same
shape as CHC, whose LIA encoding is unsound for Java's 32-bit arithmetic and is
masked by `bb.open()` gating: two over-approximating engines that are harmless
only because they are gated out.

**`Bounded { k }` cannot supply the base case anyway.** Its `k` is the BMC's
`max_depth`, a bound on path length, not on loop iterations; loop unrolling is
bounded separately by `MAX_LOOP_UNROLL = 5`. Consuming it as an iteration count
is the same category error in a different place. Real k-induction will have to
establish its own base case.

### What changed

- `Encoding::complete` reports whether the encoding covers every execution.
  False on a back-edge, on a reachable `Diverge`, or on a reachable block with
  exceptional successors (handler code is not encoded). `try_step_case` returns
  inconclusive unless it is true, so a body with loops is now declined.
- An obligation *missing* from `violation_terms` no longer counts as proved.
  Absence means the encoder never reached it.
- Loop-freeness is now transitive over the reachable call graph
  (`reachable_has_loops`). The old test inspected only the entry body, so a
  loop-free `main` calling a looping helper was discharged on a search that
  stopped at five unrollings. A call with no body counts as looping.
- Four tests in `kinduction.rs` pin all of this, including a positive case —
  an engine made sound by declining everything would pass the rest.

### Benchmarks

`benchmarks/ajave/kinduction/` (new set): `LoopFailsOnSecondIteration` (FALSE,
survives one unrolling), `LoopInvariantNeedsInduction` (TRUE, no finite
unrolling establishes it), `LoopFreeEntryCallsLoopingHelper` (FALSE, loop is
one frame down).

The third records a measurement worth keeping: before the fix it returned
UNKNOWN rather than a wrong TRUE, because the BMC cuts the loop off and reports
a *spurious* violation (witness `n = 6`, which does not fail), JVM replay
refutes it, and the spurious violation suppresses `Bounded`. The unsound
discharge was guarded by another engine's imprecision, not by design.

### `tools/validate_own_benchmarks.py` was dead

It defaulted to `ajave-benchmarks/`, renamed to `benchmarks/ajave/` some time
ago, and exited with "no tasks found". Every generator and scorer in `tools/`
had the same stale default. Restored, and three real defects fixed:

- A benchmark that hangs crashed the whole run with `TimeoutExpired`. Deadlock
  benchmarks are *supposed* to hang. Now recorded as an observation, capped at
  two repeats since a hang is stable.
- An exception in a spawned thread leaves `main`'s exit status 0 and does not
  match `thread "main"`, so `ThreadBodyThrows` was reported as a defective
  benchmark. Now any thread's exception is seen.
- Racy programs have no `Verifier.nondet` call, so the input-nondeterminism
  test called them deterministic and ran them **once**. A race is FALSE because
  the JMM permits a violating execution, not because a JVM will show you one;
  eight benchmarks were flagged as wrong on a single benignly-interleaved run.
  Anything that can start a thread now takes the contradiction-only path, where
  an unobserved violation proves nothing but an observed one against an
  expected TRUE still fails.

## 2026-09-01 — a real k-induction, and a heap for it to reason about

Follows the entry above, which removed the unsound discharge without replacing
the capability. These two changes are one piece of work: an induction with no
heap cannot prove anything about an array, and a heap with no induction has no
consumer, since every looped body was being declined.

### The heap (`smt_encode`)

Reads were fresh unconstrained values and writes were dropped. Sound in the
direction that matters — an arbitrary value covers whatever is really stored —
but it made every heap property unprovable, and left the encoder unable to tell
`ArrayInvariantHoldsForAllElements` from `ArrayInvariantViolated`.

Instance fields use Burstall–Bornat splitting: one SMT array per `FieldKey`,
indexed by the object reference. Two objects separate for free because their
references are distinct terms, so no alias analysis is needed to keep `p.f` from
`q.g`, and `p.f` against `q.f` is decided by the solver on the references
themselves — which is exactly right.

Java arrays cannot be handled that way. The natural index is the pair
(reference, element index) and `Solver::fresh_array` fixes the index width at
32 bits, so the pair does not fit. They are split by allocation site instead,
which needs a points-to map carried alongside the SSA state and merged at joins:
sites that disagree across incoming edges collapse to "unknown". A store through
an unknown reference havocs every array rather than being dropped, because the
unknown reference may be the array a later load reads.

Allocations get successive constant addresses rather than fresh symbols with
pairwise disequalities, which would be quadratic. Sound because nothing in Java
observes an address — only reference equality is visible, and distinct constants
preserve exactly the disequalities the JLS guarantees between a `new` object and
every reference that already exists. References the encoder did not allocate stay
unconstrained and can still alias anything, which costs precision only. Addresses
start at `0x1000`: `Const::Str` encodes as the literal 1, and an allocation
sharing that value would alias every string constant in the body.

A call not known pure (via `ajave_models::contract_of`) havocs the whole heap.
Array lengths survive it — an array's length is immutable in Java.

### The induction (`encode_k_induction`)

`base` asks whether the obligation fails in any of the first k iterations from
the real entry state; `step` asks whether there is any state at all from which
it survives k iterations and fails on the next. Both UNSAT proves it for every
iteration. They are returned as two terms rather than one because a caller that
conflates them proves nothing: the step case alone is vacuously true of a
property that never held.

Three pieces made this possible:

- **`walk_region`.** The traversal is now parameterised by a block set and an
  entry, and treats a successor outside the set *or equal to the entry* as an
  exit. Making the entry an exit is what turns a loop body into a transition:
  the back-edge leaves the region and its state becomes the next iteration's
  input instead of being dropped.
- **`loop_region`, not the natural loop.** The natural loop is the blocks that
  reach the back-edge, and in lifted Java the interesting obligation is never
  among them: `assert c;` compiles to a branch into a block that constructs an
  `AssertionError` and throws, which has no path back to the header. Measured on
  `LoopInvariantNeedsInduction`, whose `Check` sits in `bb11` behind a `throw`
  while the natural loop is `bb4..bb12`. Inducting over a region that cannot
  contain the property is vacuous, and it reported "0 obligations to induct
  over" until the region became "one pass from the header, exit and back edges
  excluded".
- **No `Bounded` dependency.** The base case is established here, so waiting for
  `Status::Bounded` only starved the engine — it is published solely when a run
  finds no violation anywhere. `k_induction_applicable` screens shapes without
  touching a solver so the wider reach does not cost a process spawn per
  obligation.

Scope, enforced by declining rather than by assumption: exactly one back-edge,
no nested loop, the obligation inside the loop, and a prefix the encoder
describes completely. Depths 1, 2, 3.

### Result

`LoopInvariantNeedsInduction` is proved at k=1 — a property no finite unrolling
establishes, and one the engine could not previously reach at all. Smoke: 123
correct, 0 wrong.

`ArrayInvariantHoldsForAllElements` is still UNKNOWN, and will stay that way.
It has two sequential loops, so there is no single transition relation, and its
property is `∀i. a[i] == 0` — established by the *first* loop and read by the
second. That needs a quantified invariant over the array, not an induction at
fixed depth. The heap is a prerequisite for reaching it; it is not sufficient.

## 2026-09-01 — measuring the k-induction change: −13 VA, and what it bought

Valid-assert **800** (664 correct, 43 timeouts, 1 wrong), no-runtime-exception
**1057** (537 correct, 0 wrong). NRE is identical to baseline; VA is down 13
from 813. The single wrong answer is still `ReverseInterpolator_true`, the
benchmark defect in #72, unchanged.

### The bug was live, not latent

The earlier entry called it latent, on the grounds that `Status::Bounded` is
starved. That was wrong, and the corpus diff says so: **seven** valid-assert
tasks were being discharged by the unsound `try_step_case` and now are not.

`jbmc-regression/array1` is the clearest. Its `main` contains the loop, so the
loop-free path never applied to it — it was going through `try_step_case`, whose
one-pass encoding returned UNSAT, and that was published as
`ProofKind::KInduction`. The same for `aastore_aaload1`, `list1`,
`jdart-regression/list2`, and `algorithms/{BellmanFord,InsertionSort}-MemSat01`
and `RedBlackTree-FunSat01`.

All seven expect TRUE, so no wrong answer resulted. That is luck, not design:
the identical mechanism on a task expecting FALSE is −16. **The 13 points are
the price of removing a proof rule that was wrong by construction**, and the
right way to win them back is a quantified invariant over arrays, which is what
those tasks actually need — `array1` asserts `int_array[7] == 7` after a loop
writing `a[i] = i`, and its `Check` sits *after* the loop, where an induction at
fixed depth has nothing to say.

### The cost of the wider reach, and a fitted constant

Dropping the `Bounded` requirement made the engine attempt far more
obligations, and three tasks went UNKNOWN → TIMEOUT. `argv-tasks/ActiveCheck`
reproduced standalone: a ~20,900-term encoding whose base-case query z3 did not
answer in over six minutes.

A solver query timeout (`with_query_timeout(5_000)`, the same treatment `f3`
already had) did **not** stop it, so the fix does not rely on one:
`MAX_ENCODING_COST` refuses an attempt whose encoding would exceed ~8,000 terms.
Recorded as a fitted constant per the overfitting rules above, with the reason
it is not load-bearing: successful proofs encode at ~10³ terms
(`LoopInvariantNeedsInduction` is 1,026) and the pathological case is ~2×10⁴, so
any cap between them behaves identically. ActiveCheck returns to 1.2s and
UNKNOWN.

The measurement to repeat after this is whether those three timeouts revert and
whether the seven losses are exactly the set above — if a different task moved,
the cap is doing something other than what is claimed here.

### Confirmed after the cap

The re-run predicted above came back exactly as stated, which is the point of
having written the prediction down first:

- The three UNKNOWN → TIMEOUT regressions are **gone**. `ActiveCheck`,
  `VelocityTracker_false` and `VelocityTracker_true` no longer differ from the
  pre-change run, and the timeout count fell to 40 (pre-change 42, uncapped 43).
- The seven TRUE → UNKNOWN losses are **exactly** the predicted set. No other
  task moved, so the cap is doing what is claimed and not silently declining
  work elsewhere.

Score is 800 either way, because a timeout and an UNKNOWN both score zero — the
cap bought time and determinism, not points. The −13 decomposes as seven
discharges lost at −2 each and `autostub/Long...toString` gained at +1.

Both properties re-measured on the shipping build, idle machine: **VA 800**
(664 correct, 40 timeouts, 1 wrong = #72) and **NRE 1057** (537 correct, 0
wrong, identical to baseline). Combined 1857.

## 2026-09-01 — obligation ids collided across methods, blocking unrelated discharges

**NRE 1057 → 1089 (+32), 553 correct, 0 wrong.** 16 tasks went UNKNOWN → TRUE,
ten of them securibench.

`ObligationId` is an index into one `Body`'s obligation list, so id 3 exists in
every method that has four obligations. Both per-obligation guards at the BMC's
discharge site were keyed by the id alone:

```rust
let violated_oids: HashSet<ObligationId> =
    violations.iter().map(|(_, oid, _)| *oid).collect();   // method discarded
...
&& !ctx.skipped_obligations.contains(&oref.id)             // method ignored
&& !violated_oids.contains(&oref.id)
```

The discharge loop iterates `ObligationRef { method, id }` and tested only the
id, so a violation or an untrusted check in *one* method blocked discharge of an
unrelated obligation that happened to share an index in *another*. The method
was available at both sites — `violations` is `Vec<(MethodKey, ObligationId,
Witness)>` and the map expression threw it away.

Keyed by `(MethodKey, ObligationId)` now. This is a precision fix with no
soundness question in it: both sets record a fact about a *specific* check —
"this obligation's check could not be trusted", "this obligation had a candidate
violation" — and blocking a different obligation on that basis was never
justified by the record. The change restores the intended semantics rather than
relaxing anything, which is why it can gain 32 points with 0 wrong.

### Why it showed up on NRE and in securibench

Valid-assert was unchanged. The property seeds one obligation kind, so a method
rarely has enough obligations for indices to collide across methods.
No-runtime-exception seeds six kinds, so ids run high in every method and
collisions are common. securibench is the most multi-method corpus we score
against, which is why ten of the sixteen gains are there — a collision needs two
methods to collide *between*.

### How it was found

Not by reading the code, but by instrumenting it. An earlier attempt tallied
*which completeness flags were set* on blocked tasks and concluded
`has_tainted_paths` was the top blocker at 22/50. That was wrong:
`has_tainted_paths` is consulted only in the assertion-only branch of
`can_discharge`, so on no-runtime-exception a set taint flag blocks nothing at
all. Counting set flags instead of refusing ones would have put the effort in
the wrong place entirely.

`Completeness::discharge_blocker` now reports which condition actually refuses,
and is deliberately kept beside `can_discharge` in the same order so a
measurement of where the points are cannot drift from what the code tests. The
corrected tally over 80 blocked tasks in the two largest pools:

| blocker | NRE | VA |
|---|---|---|
| discharge never attempted | 15 | 5 |
| `violated` | 8 | 12 |
| `skipped_obligation` | 4 | 13 |
| `all_paths_complete` | 7 | 10 |
| `has_potentially_throwing_havoc` | 6 | 0 |

`violated` and `skipped_obligation` together are the largest bucket, and this
change is why: a large share of them were collisions rather than real blocks.

### The +32 exposed a wrong TRUE, and the wrong TRUE was pre-existing

Measuring the collision fix on **both** properties, as the discipline above
requires, gave NRE 1089 with 0 wrong and VA **786 with 2 wrong** — a new wrong
TRUE on `securibench/Basic15`.

The analysis script nearly hid it. Its diff regex was `^  [+.x]` and the WRONG
marker is a capital `X`, so it reported "1 task differs" while a soundness
regression sat in the same file. The regex now includes `X` and says why.

Reduced to five lines
(`benchmarks/ajave/jvm-strings/StringBufferFromUnknownStringIsNotEmpty`):

```java
String s2 = s + ";";                                    // untracked
StringBuffer buf = new StringBuffer(s2);
if (buf.toString().contains("<bad/>")) { assert false; }  // said TRUE, is FALSE
```

`handle_assign` modelled `new StringBuffer(x)` as the **empty string** whenever
`x`'s symbolic content could not be resolved:

```rust
args.get(1).and_then(|a| self.encode_str_operand(a))
    .unwrap_or_else(|| self.solver.str_const(""))
```

An unknown argument is not an empty one. Asserting `buf == ""` is a claim about
content the program never made, and it is strong enough to prove
`contains("<bad/>")` false — so the branch holding the assertion was pruned as
infeasible, the obligation was **never checked**, and it was then discharged as
unreachable.

The `else` arm had the same defect for `(Ljava/lang/CharSequence;)`, which is
specified to hold the argument's characters. Only `()V` and `(I)V` genuinely
start empty. This is the descriptor-blind default the modelling rules warn
about: testing part of a signature and letting everything else fall into one
bucket that happens to assert something false.

**The bug was pre-existing and masked by the collision.** The id collision was
over-blocking discharge, and one of the things it over-blocked was this wrong
one. That is the third time today the same pattern has appeared — k-induction's
one-unrolling proof, CHC's LIA arithmetic, and now this — a wrong answer held
back by an unrelated conservative gate rather than by design. Removing a gate
does not create these; it reveals them.

Concat matters and is not decoration: `s + ";"` compiles to its own
StringBuilder chain, which is what leaves the result untracked at the point the
StringBuffer is built. `new StringBuffer(s)` directly resolves and was always
answered FALSE correctly.

### Final, both properties, idle machine

**VA 802** (665 correct, 40 timeouts, 1 wrong = the #72 benchmark defect),
**NRE 1089** (553 correct, 0 wrong). Combined **1891**, against 1857 before this
change and 1870 at the start of the day. Smoke 125 correct, 0 wrong, with
`Basic15` and both reductions added as canaries.

## 2026-09-02 — per-obligation taint: correct, and measured inert

Reverted. `has_tainted_paths` is a whole-run flag, and on securibench's
valid-assert tasks it was the refusing condition in 11 of 18 sampled blocks, so
charging taint to the individual obligations whose checks met it looked like the
obvious win. It is sound — the same predicate, evaluated per obligation — and it
changed **nothing**: valid-assert 802 with 0 tasks differing, no-runtime-exception
1089 with one score-neutral timeout flip.

The reason is worth keeping. On those programs the taint is on the obligations'
*own* paths, not elsewhere in the program, so the per-obligation record blocks
exactly what the global flag blocked. Reading "blocked by `has_tainted_paths`" as
"taint somewhere else in the program" was the error. **The win on securibench is
producing less taint, not gating it better** — `rvalue_tainted` taints any call
that is not a modelled string call, not a modelled math call, and not inlinable.

Kept from the attempt, because both earned their keep:

- **`Completeness::discharge_blocker`**, which reports the condition that
  actually refuses. It sits beside `can_discharge` in the same order so a
  measurement of where the points are cannot drift from what the code tests.
  Two orderings this session were wrong before it existed: one counted flags
  that were *set* rather than conditions that *refused* (`has_tainted_paths` is
  read only in the assertion-only arm, so on no-runtime-exception a set flag
  blocks nothing at all), and one sampled "the first 40 unknowns" across two
  categories when the first sorts before the second and supplies more than 40 —
  so the sample was entirely one category and said nothing about the other.
- **`mark_incomplete`**, routing all eleven truncation sites through one place
  that records which method was truncated. That is the hook for making
  `all_paths_complete` per-obligation, which the stratified measurement says is
  the dominant blocker: 73 of 144 sampled tasks, and nearly every task in
  `algorithms` and `java-ranger-regression`.

### What the stratified measurement changed

| blocker | count / 144 |
|---|---|
| `all_paths_complete` | 73 |
| discharge never attempted | 21 |
| `violated` | 18 |
| `skipped_obligation` | 16 |
| `has_tainted_paths` | 11 (all securibench valid-assert) |
| `has_potentially_throwing_havoc` | 5 |

And a follow-up that decided what *not* to build: of the tasks blocked at the
outer `all_paths_complete` gate, the share with open obligations in a method
that was never truncated is **24 of 24** in `java-ranger-regression` and **2 of
27** in `algorithms`. So per-obligation completeness targets java-ranger, and
`algorithms` needs quantified invariants over arrays — which is the same
boundary the heap and k-induction work hit from the other side.

### Also

`tools/validate_own_benchmarks.py` ran its JVMs through `subprocess.run`, which
kills only the process it spawned. A deadlock benchmark's JVM outlived it and
was still running seven hours later, invisible to `tools/cleanup.sh` because its
stray patterns match `ajave-*` rather than a bare `java -cp /tmp/... Main`.
`procguard` exists in this repo for exactly that and the file was not using it.
Now routed through `run_guarded`.

## 2026-09-02 — string contents through arrays: +21 valid-assert, +5 NRE

**VA 802 -> 823** (681 correct, 1 wrong = the #72 benchmark defect),
**NRE 1089 -> 1094** (556 correct, 0 wrong). Combined **1917**. Smoke 129, 0 wrong.

Seventeen valid-assert tasks went UNKNOWN to correct, twelve of them FALSE.

### What was missing

String contents were tracked through *fields* — `field_str_arrays`, which the
`$$coll_last` collection lowering uses — and not through Java arrays. `array_map`
holds a 32-bit element per index, which models the element *reference* and says
nothing about its characters, so `a[0] = s; t = a[0];` lost the contents.

The cost was not imprecision, it was **taint**. `rvalue_tainted` taints any call
that is not a modelled string call, and `str_call_modelled` requires *both*
operands of `contains` to have tracked strings. With `t`'s contents gone the call
is unmodelled, the path is tainted, and `has_tainted_paths` blocks discharge for
the entire run.

`str_array_map: Vec<(Term, Term)>` now mirrors `array_map` over the
`(Array BV32 String)` sort the `Solver` trait already had — `array_select`
already mapped `Sort::StrArray` to `Sort::Str`, so no solver work was needed.
The fresh-per-lookup default is copied deliberately from
`array_contents_lookup`: a *shared* default would force two unrelated arrays to
hold equal strings, which can make a guard provably false when it is not.

`Rvalue::ArrayLoad` produces a string view for any reference-typed element,
because the IR does not carry the element descriptor and cannot distinguish
`String[]` from `Object[]`. That is harmless — nothing reads the view unless a
`String` method is applied to it, and it is unconstrained until something was
stored.

### How it was found, since inference failed three times

1. securibench valid-assert is 11/18 blocked by `has_tainted_paths`. Read as
   "taint elsewhere in the program", which motivated the per-obligation taint
   split — **measured inert**, because the taint is on the obligations' own paths.
2. So the win is producing *less* taint. Assumed unmodelled `String` methods —
   **wrong**, every method securibench calls is already modelled.
3. Assumed the collection surface (`LinkedList` x14, `HashMap`, `ArrayList`,
   `StringTokenizer`) — **wrong again**.

Instrumenting `rvalue_tainted` gave `String.contains` in 12 of 12 blocked tasks;
instrumenting `str_call_modelled` gave `recv_str=false, arg1_str=true`, so the
receiver, not the argument, had no string. That is what pointed at arrays.

### On witnesses

Twelve of the gains are FALSE verdicts, each confirmed by JVM replay. Finding
them requires the solver to produce a string satisfying
`contains(t, "<bad/>")` — the string theory deciding it, not a constant embedded
in an engine. That is the distinction that sank the taint-engine experiment of
2026-08-24, which gained similar benchmarks only by hardcoding the trigger
string.

### Cost

Two tasks tipped into TIMEOUT: `autostub/Long...toString` went FALSE -> TIMEOUT
(-1 point) and `jbmc-regression/StringValueOf05` went UNKNOWN -> TIMEOUT on both
properties. String-array terms are not free on string-heavy programs. Recorded
rather than absorbed: if more of these appear, the string view on `ArrayLoad`
should be produced lazily rather than on every reference-typed load.

## 2026-09-02 — exception guards are kind-aware: NRE 1094 -> 1112

**Target met on no-runtime-exception** (goal 1100). 565 correct, 0 wrong. Nine
tasks went UNKNOWN -> TRUE. Valid-assert is unchanged at 823, which is the
expected result rather than a disappointing one: `guarded` is consulted *only*
when seeding no-runtime-exception, so a change to it must not move valid-assert
at all, and it did not.

### The bug

`guarded_at(off)` did not take the obligation's kind. It accepted a handler only
for `Throwable`, `Exception`, `RuntimeException`, or a catch-all — so

```java
try { int j = 10 / i; } catch (ArithmeticException e) { }
```

did not guard the `DivByZero` obligation, which was then seeded as escaping. The
BMC found `i == 0`, published a violation, JVM replay refuted it (the JVM
catches it and exits 0), and the task sat UNKNOWN with an unconfirmed violation
that nothing could discharge. `jbmc-regression` is built out of that shape, and
this was the blocker on 8 of 20 sampled tasks there.

`guarded_at` now takes the kind and tests the JLS-fixed hierarchy exactly:
`DivByZero` is an `ArithmeticException`, `ArrayBounds` an
`ArrayIndexOutOfBoundsException` (so `IndexOutOfBoundsException` also catches
it), and so on.

### Direction of risk, stated in the code

Marking an obligation guarded **removes** it from no-runtime-exception seeding,
so an over-eager guard loses a real violation and yields a wrong TRUE at −16.
The subtype test is therefore exact and drawn from the JLS, never from which
handlers look close enough. `AssertionError` is handled separately because it is
an `Error`: `catch (Exception)` and `catch (RuntimeException)` do **not** catch
it, which the old code got wrong in the permissive direction.

The paired benchmarks are discriminating rather than illustrative:
`SpecificHandlerCatchesItsOwnException` catches `ArithmeticException` around a
division and must be TRUE; `WrongSpecificHandlerDoesNotCatch` catches
`NullPointerException` around the same division and must be FALSE — they are
siblings under `RuntimeException`, so treating any specific handler as guarding
passes the first and produces a wrong TRUE on the second.

Smoke 129 -> 133, 0 wrong. `tools/validate_own_benchmarks.py` checks all 153 of
our benchmarks against a real JVM with no contradictions.

### Score

| property | before today | now | target |
|---|---|---|---|
| valid-assert | 800 | **823** | 900 |
| no-runtime-exception | 1057 | **1112** | 1100 ✓ |
| combined | 1857 | **1935** | 2000 |

## 2026-09-02 — per-obligation completeness: sound, nearly inert, and it exposed a stale-block bug

VA 823 -> **824**, NRE 1112 -> **1114**, 0 wrong. One genuine gain
(`argv-tasks/HotspotIntegerGenerator_false`, whose *no-runtime-exception*
verdict is TRUE — the suffix refers to valid-assert); the rest is timeout noise.

`all_paths_complete` is a whole-run boolean **and** the outer gate on discharge,
so one cut anywhere stopped every obligation in the program from being
considered. `cut_points` now records where each truncation happened, as
(method, block), together with every call site on the stack at that moment — a
cut inside a callee means the caller never returned, so its continuation is
unexplored too. `obligations_at_risk` walks forward from those points and
charges only the obligations a cut could actually have hidden.

### Why it buys so little, which is the useful part

Measured on `java-ranger-regression`, its predicted beneficiary:

```
cut_points=["alarmFunctional#bb65", "main#bb135"]  at_risk=718  open=1
```

The cut is the loop-unroll cap **in `main`**, so essentially every obligation is
downstream and the one open obligation genuinely *is* at risk. The accounting was
never the problem.

The earlier measurement that motivated this — "24 of 24 java-ranger tasks have
open obligations in a method that was never truncated" — compared *method sets*
and ignored interprocedural reachability. It was a proxy, and the proxy was
wrong. Recorded because the same mistake is easy to repeat: a method-level
measurement cannot answer a question about reachability.

This is the second gate refinement in a row to come back near-zero, after
per-obligation taint. Both point the same way: **for these pools the cut itself
has to go, not be accounted for more precisely.** That is loop invariants, and
it is why `algorithms` (+48 VA, +67 NRE) is gated behind CHC rather than behind
better bookkeeping.

### The bug it exposed

`explore.rs` restored `self.body` after inlining a callee but not
`self.current_block`. The statement loop then reached

```rust
if let Some(bid) = self.current_block {
    if !self.body.block(bid).exceptional.is_empty() {
        self.completeness.has_unresolved_in_try = true;
```

which indexes the **caller's** block list with a **callee's** block id — reading
some unrelated block's exception edges, or panicking when the callee had more
blocks. Wrong in either direction, and the permissive one risks a wrong TRUE.
The same class of defect as the obligation-id collision fixed earlier today:
an index that is only meaningful relative to one method, used as though it were
global.

Not separately benchmarked. The effect is a silent misread rather than a verdict
I could reproduce on a corpus task, and claiming a benchmark that does not
demonstrate it would be worse than saying so.

## 2026-09-02 — one encoder for the text-SMT engines, and IMC's missing guards

The CHC work turned up the same defects in a second engine, which is the
argument for centralising rather than patching twice.

### IMC had three of CHC's five defects

`imc` is `Direction::Over`, discharges `ProofKind::Exhaustive`, and encodes via
`encode_body_lia` over unbounded `Int`. So its proofs held for mathematical
integers and not for Java's: no overflow handling at all, `div`/`mod` Euclidean
where Java truncates toward zero, and `encode_cast` the identity so `l2i` never
truncated. Like k-induction it also consumes `Status::Bounded { k }` and ignores
`k`, and like CHC it is harmless mainly because that starves it.

It had a fourth of its own. `try_imc` selected the error formula with `find`,
taking the **first** clause for an obligation and dropping the rest — so an
obligation checked in more than one block was proved on whichever path came
first. Now every clause is disjoined.

### `Encoder`: naming, side conditions and sharing in one place

The theories were pure string functions, which left each consumer to solve the
same three problems differently:

- **Naming.** `SmtTheory::encode_fresh` minted names from a process-global
  counter that the theory could not declare, so consumers recovered them by
  *string prefix* — `expr.starts_with("bv_fresh")` in one, `"chc_fresh"` in the
  other. A theory that allocates a name it cannot bind is an interface to be
  worked around. `encode_fresh` is gone; theories now answer `models_binop`,
  `models_cast`, `sort_of` and `needs_overflow_guard`, and `Encoder` allocates.
- **Side conditions.** Overflow has to reach the consumer's `error` and there
  was nowhere to put it, so CHC collected it out of band and IMC did not collect
  it at all. `Encoder::side_conditions` carries it, from
  `smt_text::lia_overflow_cond`, shared so the two cannot drift.
- **Sharing.** Both consumers substituted expression *text* per variable, so
  `x = a + b; y = x * x;` became `(* (+ a b) (+ a b))` and a chain of
  assignments duplicated whole subtrees.

### The encoding was exponential in assignment depth

That last point was not cosmetic. Measured on the programs CHC exists for:

| task | before | after |
|---|---|---|
| `SatFibonacci01` | 24,364 bytes | **15,947** |
| `SatAckermann01` | 48,643 bytes | **30,359** |

A formula shaped by textual sharing rather than by the program. `Encoder::bind`
names each computed value, making the encoding linear in statements.

It does **not** recover the seven tasks lost to soundness, and that is the
useful part: their blocker is that proving the property now also requires
proving no overflow, which needs a bound on `fib(46)` that Spacer cannot infer.
Size was never the obstacle, so the smaller encoding does not move them — which
is worth recording, because "make the formula smaller" is the obvious next guess
and it is wrong here.

`Body::is_static` is now carried from `ACC_STATIC` rather than assumed. CHC's
`find_param_var_indices` hardcoded "assume all methods are static (jayhorn
benchmarks are static)", so for an instance method every parameter bound one
slot early and the summary related the wrong variables.

Smoke 131, 0 wrong.

## 2026-09-02 — Eldarica removed; the blocker was never the solver

Reverted. The integration worked — native build, 14 ms startup, `chc-eldarica`
registered beside `chc-spacer` and selected by the portfolio rather than by a
heuristic — and it changed nothing: valid-assert 809 with it and 809 without,
`jayhorn-recursive` identical at 4 FALSE / 1 TRUE / 1 TIMEOUT / 17 UNKNOWN.

The experiment that settles why, on hand-written Fibonacci clauses:

| encoding | z3-spacer | z3-bmc | eldarica |
|---|---|---|---|
| unbounded integers | **sat** | timeout | **sat** |
| overflow routed to `error` | timeout | timeout | unknown |
| exact 32-bit wrapping | timeout | timeout | no verdict |

Three things follow, and the second is the important one.

**No solver discharges the overflow obligation.** So a second backend cannot
recover the seven tasks soundness cost us, and neither can exact wrapping —
which is worth knowing, because wrapping is the semantically correct model and
the obvious next thing to try. It is still worth doing eventually (the guard
wrongly rejects every `hashCode`-style method that overflows harmlessly) but it
adds a variable and two inequalities per operation, and that is the wrong
direction while formulas are already too large.

**Spacer proves the unbounded version instantly.** An earlier entry claimed
Spacer could not find `ret >= n-1`. It finds it immediately on a clean
encoding. The failure was never the algorithm — it is **our encoding**, which
is why a different algorithm changed nothing.

**JayHorn preprocesses; we do not.** Its own trace reduces 93 clauses over 76
relations to 14 over 6 before solving. We hand the solver everything.

Kept in git history rather than in the tree: `HornBackend`, the runner, and
`tools/install_eldarica.sh`. Re-adding a backend is worth doing once there is
evidence a second algorithm is what is missing. Today the evidence says
otherwise, and carrying an engine that demonstrably changes no verdict is
complexity without justification.

## 2026-09-02 — ajave-opt: IR reduction built, and measured to be unsafe to enable

`ajave-opt` exists, is tested, and is **off by default**. The differential found
verdict changes at both levels, the transformed IR is verifiably correct in
every case examined, and that makes this a finding about the engines rather
than about the passes.

### What was built

A crate between lifting and the portfolio, on SeaHorn's split: `Normalise`
(copy propagation — rewrites reads, removes nothing) and `Optimise` (adds dead
assignment elimination and variable compaction). Separate crate because dead
assignment elimination needs `ajave_models::contract_of` to know a call is pure,
and `ajave-models` already depends on `ajave-ir`, so a pass module inside the IR
crate would be a dependency cycle.

`ajave_ir::validate` states what a well-formed `Body` is — ids equal to their
index, operands in range, every obligation reached by exactly one `Check` — and
runs after every pass under `debug_assertions`. It belongs with the type, not
the optimiser, so the lifter can use it too.

### The exclusions are the safety argument, and each has a test that catches it

Dead assignment elimination never removes a `Nondet` (a witness is a *sequence*
replayed on a real JVM, so removing one renumbers every later value), a `Call`
that is not `Effect::Pure`, an allocation (observable through `NegArraySize` and
reference identity), or anything an obligation's condition reads.

Each exclusion was mutation-tested: flipping it to `true` must make its test
fail. The first attempt reported the allocation exclusion as untested — that
turned out to be the harness, not the code, because the delimiter in the
mutation script was `|` and the Rust pattern `New(_) | NewArray` contains one,
so the replacement silently never applied. All four now verified to fail on
mutation.

### Measured: correct, and not safe to turn on

`tools/ir_opt_differential.py` compares verdicts across `AJAVE_IR_OPT` levels.
An IR reduction cannot change what is true of a program, so a changed verdict is
a defect and needs no expected-verdict label.

| level | effect |
|---|---|
| `Normalise` | **2 changes**: `float-widen/Bounded-Reset-Linear-Growth` and `Saturating-Integrator`, TRUE → UNKNOWN |
| `Optimise` | **7 more**: all securibench — `Aliasing3`, `StrongUpdates1/5`, `Collections1–4` |

The `getWriter` case was examined statement by statement: three dead copies
removed, the surviving three feeding the constructor with the same values, the
renumbering consistent. The IR is right. So an engine is sensitive to IR shape
in a way it should not be — the interval AI's float widening to statement count
or variable identity, and the BMC's string and collection tracking likewise.
**That is worth more than the optimisation would have been**, and it is what an
IR reduction was always going to surface.

### A gap in the harness, found the same way

The differential initially reported `Normalise` clean. It was reading
`benchmarks/sets/smoke.set`, while `tools/smoke_test.py` has its own hardcoded
`TESTS` list — two different sets with the same name. `float-widen` is in the
second and not the first, so the two lost tests were invisible. A harness that
covers a different set than the gate it is trusted to protect is not protecting
it.

### CHC, since that was the motivating case

| task | encoding off | `Normalise` | `Optimise` |
|---|---|---|---|
| `SatFibonacci01` | 15,947 | 15,947 | **12,762** |
| `SatAckermann01` | 30,359 | 30,359 | **23,802** |
| `SatMccarthy91` | 10,368 | 10,368 | **7,974** |
| `SatPrimes01` | 68,788 | 68,788 | **55,080** |

A consistent 20–23% smaller, and **no verdict moves**. Two things follow.

`Normalise` buys CHC exactly nothing: the encoding's size is set by predicate
arity and clause count, and copy propagation removes no variables. All of the
benefit is in compaction, which is the level that changes securibench.

And 35–47% of statements removed yields 20–23% of bytes, which is the stopping
condition the plan wrote down in advance — the noise is not mostly where the
cost is. The verdicts confirm it independently: the blocker on these tasks is
the overflow guard, and nobody solves that encoding at any size.

## 2026-09-02 — why JayHorn proved these and we did not: two things, one of them ours

Answered by experiment, and the first half is a bug I introduced earlier today.

### The missing measurement

Earlier entries compared *hand-written* clauses (unbounded → `sat`, guarded →
timeout) against *our* clauses (guarded → timeout) and concluded the guard was
the blocker. The cell never filled in was **our encoding without the guard** —
and it does not prove them either. So the guard was never the only difference.

Removing the guard also changed the solver's answer from `timeout` to `unsat`,
which is a different diagnosis entirely: not "too hard" but "our clauses admit a
violation the program does not have".

### The bug: an unconstrained return

Dumping the clauses (`AJAVE_CHC_DUMP`, added for this) showed it immediately:

```
(=> (m1_b1 …) (m1_s v0 0))     base case → 0            ✓
(=> (m1_b3 …) (m1_s v0 1))     base case → 1            ✓
(=> (m1_b6 …) (m1_s v0 _f0))   recursive → unconstrained ✗
```

`fibonacci` returned an **arbitrary integer** on its recursive path, so no
property of its result was provable and the assertion was trivially violable.

The cause is this session's `bind` optimisation. It names each computed value
`_fN` and records `(= _fN expr)` in `bindings`; the transition, check and
overflow clauses all conjoin those, and the **return** clause did not. The base
cases return literals, so they looked correct, which is why nothing structural
caught it — `validate` checks well-formedness, not that a clause carries the
equalities its operands depend on.

Over-approximating, so it cost precision and not soundness: a free return value
admits more behaviour, never less. But it made CHC unable to discharge anything
recursive at all, which is most of what CHC is for.

### With it fixed, the gap is exactly the guard

| task | guard on | guard off |
|---|---|---|
| `SatFibonacci01` | UNKNOWN | **TRUE** |
| `SatAckermann01` | UNKNOWN | **TRUE** |
| `SatMccarthy91` | UNKNOWN | **TRUE** |
| `SatPrimes01` | UNKNOWN | **TRUE** |

So our encoding is now demonstrably as capable as JayHorn's: given the same
assumption, it proves the same programs. The whole remaining difference is the
assumption itself — JayHorn's documented unbounded-integer model, whose
SV-COMP 2019 failure is `UnsatAddition02`, the same benchmark that caught us.

**We are not behind JayHorn on these. We are strictly stricter.** The
`AJAVE_CHC_EXPERIMENT_NO_GUARD` switch used for the table was removed rather
than kept: an environment variable that silently disables a soundness guard is
the thing this file warns about.

## 2026-09-04 — Baseline re-established: VA 823 / NRE 1112 at a 180s budget

### The number that was being over-claimed

The standing figure was VA 809 / NRE 1114 with "0 wrong", measured at a **60s**
task budget. Raising the budget to 180s — closer to SV-COMP's 900s — showed
NRE at 1082 with **one wrong answer**: `apachecli_eqchk` said FALSE on a task
expecting TRUE, costing -32. At 60s it timed out, so the clock had been acting
as a soundness gate and the "0 wrong" described the timeout, not the analysis.

Two certifier defects caused it (#86), both found by instrumenting refutations
rather than reasoning about them:

- The replay ran `java -ea` for **every** obligation kind. `assert e;` evaluates
  `e` only with assertions enabled, so for no-runtime-exception — a property
  evaluated with them off — the replay executed code the property excludes. The
  harness ends `assert outSPF.equals(outJR)`, `outSPF` is null when parsing
  fails, and *evaluating the condition* threw the NPE we then reported.
- Confirmation matched an accepted exception name **anywhere in stderr**,
  including one the program caught and printed. This task prints two
  `UnrecognizedOptionException` traces from a catch block before dying of
  something else.

Fixing both moved NRE from 1082 to **1112 with 0 wrong**: +32 for the removed
wrong answer, -2 for two legitimate FALSEs the stricter match now refuses.

So the position is the same score at three times the budget, without a latent
-32 — which is a real improvement over the number it replaces, not a regression
from it.

### Valid-assert: 812 -> 823

Every gain came from replacing a havoc with real semantics. The recurring shape
is that **`fresh_bv` is not a model**: an unconstrained result is not an
approximation, it is a licence for the solver to claim whatever an assertion
wants, and the witness then cannot replay.

- `encode_l2f` was `fresh_bv` with a `TODO`. SMT-LIB expresses long-to-float
  directly as `((_ to_fp 8 24) RNE bv)`, exactly the JVM's `l2f`.
- `Math.round` had an encoder arm that was **dead**: a second allowlist,
  `math_call_modelled`, gates entry to `encode_math_call`, and its own comment
  warns that a method missing from it silently gets `fresh_bv`.
- `Integer.getInteger`/`Long.getLong` were grouped with `parseInt` as throwing
  and lifted to `Unmodelled`. They do not throw; they return their default when
  the named system property is absent, which it always is here.
- `multianewarray` lifted to `Rvalue::Nondet`, which the BMC reads as a value
  the *program* chose rather than one *we* invented, so its taint gate never
  fired (#88).

Two gains were unplanned: `jpf-regression/ExSymExeComplexMath_true` became
**provable**, because an exact `l2f` helps the over-approximating side too.

Measured cost elsewhere: none. `float-nonlinear` 0 of 87 changed,
`float_unboundedloop` 0 of 30, despite the new FP terms landing in the BMC's
default path.

### A partial model with a free fall-through is still a havoc

Worth stating on its own, because the first `Math.round` attempt failed exactly
this way. Encoding only the exactly-specified cases — NaN to 0, clamping,
`[-0.5, 0.5)` to 0 — bought nothing: the solver went straight to the
unconstrained branch and claimed `MAX_VALUE` for an input of 2.0000019.

The general case is now stated as a *relation*, `|x - round(x)| <= 0.5`, rather
than as `floor(x + 0.5)` — the pre-Java-7 formula, changed by JDK-6430675
because it rounds `0.49999999999999994` up. Committing to that identity would
have been a wrong model producing wrong answers.
`benchmarks/ajave/jvm-floats/RoundIsNotFloorOfPlusHalf` pins it, and ajave
proves it.
