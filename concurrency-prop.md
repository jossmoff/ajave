Absolutely. Below is a consolidated implementation/research plan for **AJAVE's Java concurrency verification engine**, taking the ideas we've discussed and turning them into one coherent technical roadmap.

# AJAVE Java Concurrency Verification Engine

## 1. Introduction

AJAVE should treat concurrency verification not as an isolated checker, but as a **first-class verification engine within a cooperative portfolio**.

The central architectural idea is:

> **Concurrency analysis discovers semantic facts about concurrent executions and publishes them to AJAVE's blackboard; other engines, particularly BMC, consume those facts to construct smaller and more precise verification problems. Conversely, BMC and other analyses feed feasibility, aliasing, invariant, and path information back into the concurrency engine.**

This gives AJAVE a fundamentally different architecture from a verifier that simply runs a concurrency algorithm independently.

The intended system is:

```text
                         Java program
                              │
                              ▼
                    AJAVE semantic representation
                              │
                              ▼
                       ┌─────────────┐
                       │  Blackboard │
                       └──────┬──────┘
                              │
             ┌────────────────┼─────────────────┐
             │                │                 │
             ▼                ▼                 ▼
       Abstract           Concurrency          BMC
       Analysis             Engine            Engine
             │                │                 │
             │                │                 │
             └────────────────┼─────────────────┘
                              │
                              ▼
                     new semantic facts
                              │
                              └──────► refinement
```

The **research hypothesis** is that this cooperation can make Java concurrency verification substantially more effective than applying concurrency exploration, BMC, or static analysis independently.

The concurrency engine should therefore be designed from the beginning as both:

1. a **standalone sound concurrency verifier**, and
2. a **producer/consumer of semantic knowledge for the rest of AJAVE**.

---

# 2. Research objectives

The project should ultimately answer four questions.

### RQ1 — Can strong stateless concurrency verification be transferred to Java?

Can techniques such as:

* partial-order reduction;
* DPOR;
* source-DPOR;
* optimal-DPOR;
* observers;
* happens-before reasoning;

be adapted to Java's execution model and particularly the **Java Memory Model (JMM)**?

### RQ2 — Can Java-specific semantic information improve concurrency reduction?

Can:

* points-to information;
* alias analysis;
* lock information;
* escape analysis;
* call-graph information;
* invariants;

be used to improve dependency detection and schedule reduction?

### RQ3 — Can symbolic verification and concurrency exploration cooperate?

Can BMC answer questions such as:

> "Can these two apparently conflicting events actually occur together?"

and feed that information back into DPOR?

### RQ4 — Can this cooperation outperform isolated verification?

Ultimately:

```text
             Individual engines
                  vs.
          cooperative AJAVE
```

should be evaluated on:

* number of schedules;
* states explored;
* SAT/SMT problem size;
* runtime;
* memory;
* bugs found;
* proofs completed;
* timeouts.

---

# 3. What the concurrency engine is responsible for

The engine should reason about **concurrent executions**, not try to duplicate every other AJAVE analysis.

Its core responsibilities are:

### Execution structure

Determine:

* threads;
* thread creation;
* thread termination;
* runnable states;
* synchronization events;
* memory accesses;
* blocking;
* waking;
* waiting;
* notification.

### Memory interaction

Identify:

* reads;
* writes;
* conflicting accesses;
* shared objects;
* shared fields;
* array accesses;
* volatile accesses;
* atomic operations.

### Synchronisation

Model:

* `synchronized`;
* monitors;
* `wait`;
* `notify`;
* `notifyAll`;
* `java.util.concurrent` primitives;
* locks;
* unlocks;
* volatile operations;
* thread lifecycle operations.

### Ordering

Maintain:

* program order;
* synchronizes-with;
* happens-before;
* reads-from;
* synchronization order where applicable;
* candidate execution relations.

### Exploration

Use this information to:

* identify dependent events;
* avoid equivalent schedules;
* generate race candidates;
* detect deadlocks;
* detect assertion failures;
* generate counterexamples.

---

# 4. The fundamental semantic model

The most important design decision is to **avoid modelling concurrency merely as "multiple threads executing instructions."**

Instead, represent an execution as an **event structure**.

For example:

```text
Thread 1                    Thread 2

e1: write(x, 1)             e3: read(x)
e2: unlock(m)               e4: write(y, 1)
```

with relations:

```text
program-order:
e1 → e2
e3 → e4

and potentially:

e2 → e3
```

if the lock operations establish the appropriate synchronisation.

The execution graph therefore becomes something like:

```text
             ┌───────────┐
             │ Execution │
             │   Graph   │
             └─────┬─────┘
                   │
       ┌───────────┼────────────┐
       ▼           ▼            ▼
   Events       Relations     State
       │           │            │
    reads        po             heap
    writes       hb             locks
    locks        sw             threads
    unlocks      rf             ...
```

This execution graph should be a central internal representation of the concurrency engine.

---

# 5. Events

Define a common event abstraction.

Conceptually:

```java
interface ConcurrentEvent {
    ThreadId thread();
    ProgramLocation location();
    EventKind kind();
}
```

with event kinds such as:

```text
READ
WRITE
VOLATILE_READ
VOLATILE_WRITE

LOCK
UNLOCK

WAIT
NOTIFY
NOTIFY_ALL

THREAD_START
THREAD_JOIN

ATOMIC_READ
ATOMIC_WRITE
ATOMIC_RMW

METHOD_ENTER
METHOD_EXIT

ASSERTION
THROW
RETURN
```

The precise event set can evolve.

The important thing is that **DPOR should operate over semantic events**, not arbitrary bytecode instructions.

---

# 6. Program order

Within each thread:

```text
e1 →po e2 →po e3 →po e4
```

This gives the execution its sequential structure.

Program order should be immutable and cheap to query.

For every event:

```text
previous event
next event
thread
program location
```

should be readily available.

---

# 7. Happens-before

The concurrency engine should explicitly represent the happens-before relation.

At minimum:

```text
program order
        +
synchronizes-with
        ↓
happens-before
```

For example:

```text
Thread A                    Thread B

write(x)
  │
unlock(lock)
  │
  │       synchronizes-with
  └──────────────────────────►
                              lock
                                │
                              read(x)
```

This distinction is critical.

Two accesses may look conflicting but may not represent a race if the JMM establishes the necessary ordering.

---

# 8. Alias and shared-memory modelling

This is where AJAVE's portfolio architecture becomes extremely valuable.

The concurrency engine should **not necessarily own points-to analysis**.

Instead:

```text
Abstract/Heap Analysis
          │
          ▼
     Blackboard
          │
          ▼
Concurrency Engine
```

For example:

```text
AliasFact(a, b, MUST_ALIAS)
AliasFact(x, y, NO_ALIAS)
PointsToFact(x, allocationSite42)
SharedFact(object42)
```

The concurrency engine can then construct a more precise dependency relation.

Without alias information:

```text
a.f ↔ b.f
```

may conservatively be considered dependent.

With:

```text
a ≠ b
```

the dependency disappears.

That directly improves DPOR.

---

# 9. Dependency relation

DPOR fundamentally depends on identifying which events are dependent.

The basic idea is:

```text
Independent events
      ↓
their ordering need not be explored separately
```

while:

```text
Dependent events
      ↓
their ordering may affect behaviour
      ↓
must potentially be explored
```

For example:

```text
T1: read(x)
T2: read(x)
```

are normally independent.

But:

```text
T1: write(x)
T2: read(x)
```

are potentially dependent.

The AJAVE dependency engine should consider:

```text
same memory location
+
at least one write
+
possible alias
+
synchronisation semantics
+
JMM semantics
```

rather than using a simplistic variable-name comparison.

---

# 10. Start with conservative dependency

The first implementation should deliberately be conservative.

For example:

```text
mayAlias(a, b)
AND
conflictingAccess(a, b)
```

→ dependent.

This gives:

**soundness first, precision later.**

Once this is working, introduce increasingly sophisticated reductions.

---

# 11. DPOR roadmap

The concurrency exploration should evolve incrementally.

## Phase 1 — naïve exhaustive exploration

Implement:

```text
state
  ↓
enabled transitions
  ↓
execute transition
  ↓
new state
```

with no reduction.

This is essential because it provides the correctness baseline.

---

## Phase 2 — basic partial-order reduction

Detect independent transitions.

If:

```text
A || B
```

and:

```text
independent(A, B)
```

then avoid exploring both:

```text
A → B
B → A
```

when one representative suffices.

---

## Phase 3 — DPOR

Introduce backtracking points.

Conceptually:

```text
exploration tree

        A
       / \
      B   C
     / \
    D   E
```

When a later event reveals that an earlier scheduling choice could have changed behaviour, add the necessary alternative to the backtracking set.

---

## Phase 4 — stronger DPOR

Investigate:

* source-DPOR;
* sleep sets;
* wakeup trees;
* optimal-DPOR;
* event structures.

The precise choice should follow benchmarking.

The research contribution does **not** need to invent DPOR from scratch.

The contribution can instead be:

> **A JMM-aware implementation and integration of strong DPOR techniques using information produced by a Java verification portfolio.**

---

# 12. JMM should be treated as a first-class research problem

This is probably the deepest technical part.

Do not simply assume:

```text
Java thread execution = sequential consistency
```

Java permits behaviours that a naïve sequentially consistent model does not.

The engine therefore needs to distinguish:

```text
program order
synchronization order
happens-before
reads-from
visibility
```

and account for:

* volatile semantics;
* monitor operations;
* final-field semantics;
* atomic classes;
* memory effects of thread operations.

The first implementation can deliberately restrict the supported Java subset.

For example:

> Phase 1: sequentially consistent synchronisation plus a conservative JMM model.

Then progressively expand JMM coverage.

---

# 13. A useful internal representation

A possible execution graph:

```java
class ExecutionGraph {
    List<Event> events;

    Relation programOrder;
    Relation synchronizesWith;
    Relation happensBefore;
    Relation readsFrom;

    Map<MemoryLocation, List<WriteEvent>> writes;
    Map<ThreadId, List<Event>> threadEvents;
}
```

The actual implementation can be more efficient, but conceptually this separation is valuable.

It allows algorithms to ask:

```text
happensBefore(a, b)
```

rather than repeatedly reconstructing it.

---

# 14. Thread state

Each explored thread should have a state resembling:

```text
ThreadState
 ├── Thread ID
 ├── Program counter
 ├── Call stack
 ├── Local variables
 ├── Held monitors
 ├── Status
 │    ├── RUNNABLE
 │    ├── BLOCKED
 │    ├── WAITING
 │    ├── TERMINATED
 │    └── ...
 └── pending exception
```

The global state contains:

```text
GlobalState
 ├── heap
 ├── static fields
 ├── threads
 ├── monitors
 ├── wait sets
 ├── execution graph
 └── scheduler state
```

---

# 15. The Java heap

Concurrency exploration requires a representation of the shared heap.

At minimum:

```text
Object ID
Class
Fields
Array contents
```

with a distinction between:

```text
thread-local
```

and:

```text
potentially shared
```

objects.

Escape analysis can later establish:

```text
object O never escapes T1
```

and therefore eliminate a huge amount of unnecessary concurrency reasoning.

This should be exposed through the blackboard:

```text
ThreadLocalFact(O, T1)
SharedObjectFact(O)
EscapesFact(O, T1)
```

---

# 16. Synchronisation model

The first-class synchronization layer should model:

### Intrinsic monitors

```java
synchronized (x) { ... }
```

as:

```text
LOCK(x)
...
UNLOCK(x)
```

### `wait`

```text
WAIT(x)
```

with the corresponding monitor release/reacquisition semantics.

### Notifications

```text
NOTIFY(x)
NOTIFY_ALL(x)
```

### Thread lifecycle

```text
START(t)
JOIN(t)
```

### Volatile

```text
VOLATILE_READ(x)
VOLATILE_WRITE(x)
```

### `java.util.concurrent`

Eventually:

```text
ReentrantLock
ReadWriteLock
Semaphore
CountDownLatch
CyclicBarrier
Phaser
Atomic*
ConcurrentHashMap
ExecutorService
CompletableFuture
```

These should initially be handled through **library models**, rather than attempting to execute all implementation details.

---

# 17. Library models

This is particularly important.

Don't explore:

```text
ReentrantLock.lock()
```

by blindly executing hundreds of library instructions.

Instead define semantic models:

```text
Lock.acquire()
Lock.release()
```

that generate the appropriate concurrency events.

For example:

```text
ReentrantLock.lock()
       ↓
LOCK(lockObject)
       ↓
blackboard
       ↓
execution graph
```

This keeps the concurrency semantics manageable.

---

# 18. The blackboard interface

The concurrency engine should publish facts such as:

```text
ThreadFact
SharedObjectFact
MemoryAccessFact
LockFact
RaceCandidateFact
DeadlockCandidateFact
HappensBeforeFact
DependencyFact
ScheduleConstraintFact
ExecutionGraphFact
CounterexampleFact
```

and consume:

```text
AliasFact
PointsToFact
InvariantFact
PathConditionFact
FeasibilityFact
CallTargetFact
ThreadLocalFact
```

This is where AJAVE becomes substantially more interesting than a standalone DPOR implementation.

---

# 19. Race detection

Initially, race detection can be expressed as:

```text
two conflicting accesses
+
different threads
+
possible same location
+
neither ordered by happens-before
```

Conceptually:

```text
Race(a,b) =
    DifferentThreads(a,b)
    ∧ Conflicting(a,b)
    ∧ MayAlias(a,b)
    ∧ ¬HB(a,b)
    ∧ ¬HB(b,a)
```

This candidate should go onto the blackboard.

But **do not immediately call every candidate a real race**.

Call it:

```text
RaceCandidate
```

and allow BMC to establish feasibility.

---

# 20. The crucial concurrency → BMC interaction

Suppose concurrency discovers:

```text
T1.write(x)
T2.read(x)
```

with no known happens-before relation.

It publishes:

```text
RaceCandidate(e1, e2)
```

BMC can then ask:

> Is there a feasible execution in which both events occur and are unordered as required?

If UNSAT:

```text
RaceCandidate
     ↓
BMC
     ↓
UNSAT
     ↓
InfeasibleConcurrencyInteractionFact
```

The concurrency engine learns that it does **not** need to explore that case.

This is one of the key feedback loops.

---

# 21. BMC → concurrency

The reverse direction is equally important.

BMC can publish:

```text
PathConditionFact
FeasibilityFact
OrderingFact
AliasFact
ReachabilityFact
```

For example:

```text
event e1 reachable only when x > 10
event e2 reachable only when x < 0
```

BMC establishes:

```text
x > 10 ∧ x < 0 = UNSAT
```

so the concurrency engine can eliminate the apparent interaction.

This is **feasibility-guided partial-order reduction**.

That is a potentially strong research contribution.

---

# 22. Abstract interpretation → concurrency

Abstract interpretation should publish coarse global knowledge.

Examples:

```text
x is thread-local
object O cannot escape thread T
a and b cannot alias
lock L always held at program point P
method foo() cannot throw
condition C is unreachable
```

Concurrency can use this to reduce its search.

The most immediately valuable facts are probably:

### Thread locality

```text
ThreadLocal(x,T1)
```

→ no cross-thread dependency.

### No-alias

```text
NoAlias(a,b)
```

→ no memory dependency.

### Lockset

```text
HeldLocks(T1,P) = {L}
```

→ stronger ordering reasoning.

---

# 23. Concurrency → abstract interpretation

The feedback should work in the other direction too.

Concurrency can establish:

```text
under all explored schedules:
    lock L protects x
```

or:

```text
T2 can never reach P while T1 holds L
```

These become useful invariants.

This interaction can be introduced later; don't make it a Phase 1 dependency.

---

# 24. Counterexample-guided refinement

The engines should be able to communicate counterexamples.

For example:

```text
AI says:
    no race

BMC finds:
    race
```

Then the blackboard records:

```text
Counterexample
```

and AI can refine its abstraction.

Or:

```text
DPOR assumes:
    e1 and e2 independent

BMC finds:
    feasible interaction

```

→ dependency relation needs refinement.

This gives you a CEGAR-like architecture across **different verification engines**.

---

# 25. Verification obligations

Don't make every engine return only:

```text
PASS / FAIL / UNKNOWN
```

Use explicit obligations.

For example:

```java
record VerificationObligation(
    Property property,
    ProgramRegion region,
    Formula condition,
    Set<FactId> dependencies
)
```

A concurrency engine might produce:

```text
RaceFreedom(e1,e2)
```

BMC consumes it.

A BMC engine might produce:

```text
Feasibility(e1,e2)
```

Concurrency consumes it.

This makes the blackboard genuinely useful.

---

# 26. Deadlock detection

Once locks and wait states are modelled, construct a wait-for graph:

```text
T1 → L1 → T2 → L2 → T1
```

or more directly:

```text
T1 waits for L1
L1 held by T2

T2 waits for L2
L2 held by T1
```

→ cycle.

The initial detector can be straightforward.

Later research can investigate:

* lock-order analysis;
* dynamic deadlock detection;
* conditional deadlocks;
* BMC-confirmed deadlocks;
* wait/notify deadlocks.

Again, emit:

```text
DeadlockCandidate
```

before claiming a concrete bug.

---

# 27. Atomicity

Another natural property.

A transaction-like region:

```text
lock
   ...
unlock
```

can be checked for interference.

The engine could identify:

```text
expected atomic region
```

and detect:

```text
other thread modifies relevant state
```

This becomes particularly interesting for:

* unsynchronised compound operations;
* check-then-act patterns;
* lazy initialisation;
* collection operations.

---

# 28. The concurrency engine's internal pipeline

A good implementation structure would be:

```text
Java program
     │
     ▼
Semantic extraction
     │
     ▼
Thread/event model
     │
     ▼
Memory + synchronisation model
     │
     ▼
Execution graph
     │
     ├─────────────► Race analysis
     │
     ├─────────────► Deadlock analysis
     │
     ├─────────────► Dependency analysis
     │
     └─────────────► DPOR scheduler
                         │
                         ▼
                    State exploration
                         │
                         ▼
                    Verification
```

With the blackboard intersecting every stage:

```text
                   BLACKBOARD
                       ▲
                       │
   ┌───────────────────┼───────────────────┐
   │                   │                   │
Extraction         Analysis             BMC
   │                   │                   │
   └───────────────────┴───────────────────┘
```

---

# 29. Implementation roadmap

## Phase 0 — Architecture

Implement:

* concurrency package;
* event abstraction;
* thread abstraction;
* global state;
* execution graph;
* blackboard facts;
* concurrency-specific obligations.

No sophisticated reduction yet.

---

## Phase 1 — Sequentially consistent baseline

Implement a deliberately simple scheduler.

Support:

* threads;
* thread start/join;
* reads/writes;
* monitors;
* basic locks;
* assertions.

Build exhaustive exploration.

This is your **ground truth implementation**.

---

## Phase 2 — Basic race detection

Implement:

```text
conflicting accesses
+
same location
+
different threads
+
no HB ordering
```

Produce counterexamples.

Benchmark against hand-written examples.

---

## Phase 3 — Basic POR

Introduce:

* independence;
* transition dependency;
* sleep sets;
* basic reduction.

Measure:

```text
states
schedules
runtime
```

against exhaustive exploration.

---

## Phase 4 — DPOR

Implement proper dynamic partial-order reduction.

Start with a well-understood algorithm such as source-DPOR, then investigate stronger alternatives.

The implementation should expose:

```text
backtracking set
sleep set
execution prefix
dependent event
```

for debugging and experimentation.

---

# 30. Phase 5 — JMM semantics

Gradually introduce:

* volatile;
* synchronizes-with;
* happens-before;
* reads-from;
* final-field semantics;
* atomic classes.

Build dedicated litmus tests.

This stage is extremely important scientifically.

You need to be able to demonstrate:

> AJAVE is not merely a sequentially-consistent Java model with threads bolted on.

---

# 31. Phase 6 — Blackboard integration

Connect:

```text
AI → concurrency
```

Initially consume only:

* alias;
* points-to;
* thread-locality;
* escape information.

Measure the improvement.

This gives you your first major portfolio experiment.

---

# 32. Phase 7 — Concurrency → BMC

Generate obligations such as:

```text
RaceCandidate
DeadlockCandidate
ScheduleConstraint
```

and have BMC validate them.

The basic workflow:

```text
Concurrency
    ↓
candidate
    ↓
BMC
 ┌──┴──┐
SAT  UNSAT
 │      │
bug    prune
```

This should be one of the most visible AJAVE features.

---

# 33. Phase 8 — BMC → concurrency

Feed back:

* infeasible paths;
* impossible event pairs;
* alias information;
* schedule constraints;
* reachability.

Now implement:

> **Feasibility-guided DPOR.**

This is where the research story becomes particularly compelling.

---

# 34. Phase 9 — Strong DPOR

Once the basic system is stable, investigate:

* source-DPOR;
* optimal-DPOR;
* wakeup trees;
* sleep sets;
* observers;
* event structures.

Don't implement every algorithm merely for completeness.

Benchmark them and select the strongest combination.

---

# 35. Phase 10 — Modern Java concurrency

Extend semantic models to:

```text
ReentrantLock
ReadWriteLock
Semaphore
CountDownLatch
CyclicBarrier
Phaser
AtomicInteger
AtomicReference
ConcurrentHashMap
ExecutorService
Future
CompletableFuture
ForkJoinPool
```

The important principle is:

> **Model the concurrency semantics, not necessarily the implementation internals.**

---

# 36. Phase 11 — Async/task concurrency

Eventually represent:

```text
task submission
task execution
callback
completion
exceptional completion
cancellation
```

as events.

For:

```java
future
    .thenApply(...)
    .thenCombine(...)
```

construct a task dependency graph.

This could become a later research extension.

---

# 37. Phase 12 — Adaptive portfolio planning

Once several engines cooperate reliably, introduce a planner.

For each outstanding obligation:

```text
Which engine should run next?
```

Potential inputs:

* estimated cost;
* precision;
* previous success;
* size of obligation;
* available facts;
* expected reduction.

For example:

```text
RaceCandidate
      │
      ├── static analysis → cheap
      │
      └── BMC → expensive
```

Run static analysis first.

This eventually transforms AJAVE into an **adaptive verification portfolio**.

---

# 38. Testing strategy

You need several different benchmark classes.

### Unit-level concurrency tests

Tiny programs testing:

* locks;
* volatile;
* wait/notify;
* thread lifecycle;
* atomics.

### Litmus tests

Specifically designed JMM behaviours.

### Algorithmic benchmarks

Programs with:

* many equivalent schedules;
* high dependency;
* deep synchronization;
* race patterns.

### Real Java projects

Eventually test on realistic code.

### Competition benchmarks

Where possible, use SV-COMP Java benchmarks and relevant external concurrency suites.

---

# 39. What to measure

Do not just measure:

```text
verified / not verified
```

Record:

### Effectiveness

* bugs found;
* proofs completed;
* false alarms;
* unknowns.

### Scalability

* runtime;
* memory;
* number of states;
* number of schedules.

### Reduction

* raw schedules;
* schedules after POR;
* schedules after DPOR;
* schedules after alias information;
* schedules after BMC feedback.

### Cooperation

Most importantly:

```text
standalone BMC
standalone concurrency
AI + concurrency
concurrency + BMC
AI + concurrency + BMC
```

This is what validates the blackboard hypothesis.

---

# 40. The critical ablation experiments

These should be designed from the beginning.

For a benchmark:

```text
Configuration A:
BMC

Configuration B:
Concurrency

Configuration C:
AI + BMC

Configuration D:
AI + Concurrency

Configuration E:
Concurrency + BMC

Configuration F:
AI + Concurrency + BMC
```

Then compare.

The strongest result would be something like:

```text
                 states       time
BMC              10m         timeout
DPOR             2m          timeout
AI               --          unknown

AI + DPOR        400k        180s
DPOR + BMC       120k         75s
AI + DPOR + BMC   18k         12s
```

The exact numbers obviously don't matter now.

**The experimental structure does.**

---

# 41. Soundness boundary

This needs to be explicit.

At every stage, document exactly what is guaranteed.

For example:

### Phase 1

Sound for:

> bounded, sequentially consistent Java subset.

### Phase 2

Add:

> monitor synchronisation.

### Phase 3

Add:

> volatile/JMM semantics.

Eventually:

> sound with respect to a defined subset of the Java Memory Model and supported library semantics.

Do not claim full Java/JMM soundness until it is genuinely established.

---

# 42. Suggested package architecture

Conceptually:

```text
ajave-concurrency/
│
├── model/
│   ├── Event
│   ├── ThreadState
│   ├── GlobalState
│   ├── Heap
│   ├── Monitor
│   └── ExecutionGraph
│
├── jmm/
│   ├── ProgramOrder
│   ├── SynchronizesWith
│   ├── HappensBefore
│   ├── ReadsFrom
│   └── MemorySemantics
│
├── scheduler/
│   ├── Scheduler
│   ├── ExplorationState
│   ├── Backtracking
│   ├── SleepSet
│   └── DPOR
│
├── dependency/
│   ├── DependencyAnalysis
│   ├── MemoryDependency
│   ├── LockDependency
│   └── AliasDependency
│
├── properties/
│   ├── RaceDetection
│   ├── DeadlockDetection
│   └── Atomicity
│
├── models/
│   ├── Thread
│   ├── Locks
│   ├── Atomics
│   ├── Executors
│   └── Futures
│
└── blackboard/
    ├── ConcurrencyFacts
    ├── Obligations
    └── ConcurrencyResults
```

The exact package names should follow AJAVE's existing architecture, but the conceptual separation is useful.

---

# 43. The implementation philosophy

There are three principles I'd keep throughout.

### 1. Soundness before cleverness

Start conservative.

A false dependency is expensive.

An unsound independence decision can invalidate the verifier.

---

### 2. Semantic events rather than bytecode

Don't make DPOR dependent on JVM instruction details.

The abstraction should be:

```text
read
write
lock
unlock
wait
notify
start
join
...
```

with bytecode/JVM instructions mapped into those events.

---

### 3. Facts rather than hard-coded dependencies

Don't write:

```text
if (bmc says X) {
    do Y;
}
```

Instead:

```text
BMC publishes FeasibilityFact
```

and:

```text
Concurrency consumes FeasibilityFact
```

This preserves AJAVE's architecture and makes future engines possible.

---

# 44. The eventual research contribution

The implementation itself is not the entire research contribution.

The strongest paper/thesis story would be:

> **AJAVE introduces a cooperative verification architecture for Java in which static, symbolic, bounded and concurrent analyses exchange semantic information through a shared verification blackboard. We instantiate this architecture with a JMM-aware concurrency engine based on dynamic partial-order reduction and demonstrate that cross-engine information substantially reduces concurrent state-space exploration.**

Then the individual contributions could be:

1. **A common semantic representation for Java concurrency.**
2. **A JMM-aware dependency model.**
3. **Alias/escape-guided partial-order reduction.**
4. **BMC-confirmed concurrency feasibility.**
5. **Bidirectional DPOR/BMC cooperation.**
6. **A portfolio architecture for combining heterogeneous Java verification engines.**
7. **An empirical evaluation demonstrating when cooperation provides substantial benefits.**

---

# 45. The paper structure

The eventual paper could naturally become:

## 1. Introduction

Java concurrency remains difficult for automated verification because of:

* state explosion;
* heap aliasing;
* dynamic dispatch;
* JMM semantics;
* modern concurrency libraries.

Existing approaches attack individual parts of this problem.

AJAVE instead proposes **cooperative verification**.

---

## 2. Background

Explain:

* Java concurrency;
* JMM;
* execution graphs;
* happens-before;
* partial-order reduction;
* DPOR;
* BMC;
* abstract interpretation.

---

## 3. AJAVE architecture

Describe:

```text
engines
blackboard
facts
obligations
refinement
```

---

## 4. Java concurrency model

Define:

* events;
* threads;
* memory;
* locks;
* execution graphs;
* JMM relations.

---

## 5. JMM-aware dependency analysis

Describe the dependency relation.

---

## 6. DPOR

Describe the exploration algorithm and modifications required for Java.

---

## 7. Cross-engine cooperation

This is potentially the most novel section.

Describe:

```text
AI → DPOR
DPOR → BMC
BMC → DPOR
```

---

## 8. Implementation

Describe the actual AJAVE implementation.

---

## 9. Evaluation

Compare:

```text
baseline
DPOR
AI + DPOR
DPOR + BMC
full portfolio
```

---

## 10. Limitations

Be explicit about:

* unsupported JMM features;
* library models;
* reflection;
* native code;
* fairness;
* weak memory edge cases.

---

## 11. Related work

Compare against:

* JPF;
* JBMC;
* CBMC-derived concurrency research;
* VeriFast;
* CIVL;
* Nidhugg;
* Dartagnan;
* GenMC;
* CDSChecker;
* other DPOR/JMM work.

---

# 46. The ultimate AJAVE vision

The concurrency engine should be the first major demonstration of a much larger idea.

Eventually:

```text
                         AJAVE
                           │
                     Verification
                      Blackboard
                           │
      ┌────────────┬───────┼─────────┬────────────┐
      ▼            ▼       ▼         ▼            ▼
     AI           BMC   Concurrency  SE       Deductive
      │            │       │         │            │
      └────────────┴───────┼─────────┴────────────┘
                           │
                           ▼
                       refinement
                           │
                           └──────────────►
```

The concurrency work is therefore both:

**a substantial standalone verifier**, and

**the hardest proof-of-concept for AJAVE's cooperative verification architecture.**

That is the key strategic point.

---

# 47. Recommended implementation order

If actually starting tomorrow, I would **not** attempt the entire roadmap.

I'd build this vertical slice first:

```text
Java program
     │
     ▼
AJAVE IR
     │
     ▼
Thread/event extraction
     │
     ▼
Execution graph
     │
     ▼
Naïve scheduler
     │
     ▼
Exhaustive concurrency verification
     │
     ▼
Race detection
     │
     ▼
Basic POR
     │
     ▼
DPOR
     │
     ▼
Blackboard integration
     │
     ├──────────► AI alias/escape facts
     │
     ▼
BMC race feasibility
     │
     ▼
BMC → concurrency feedback
     │
     ▼
JMM strengthening
     │
     ▼
stronger DPOR
```

**That is the core research spine.**

Everything else—deadlocks, atomics, executors, `CompletableFuture`, richer JMM semantics, adaptive scheduling—can grow around it.

The most important thing is to get to the first compelling experiment:

> **Can AJAVE use information from its other verification engines to explore dramatically fewer Java concurrent executions while preserving soundness?**

If the answer is demonstrably **yes**, you have both a strong engineering foundation and a very plausible research contribution to build the rest of the project around.
