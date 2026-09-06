# concolic

**Direction:** Under
**Tier:** 2
**Status:** working
**Source:** `ajave-engines/src/concolic.rs`

## What it proves or finds

Concolic execution runs the program for real on a concrete input, records the
branch conditions it met along the way, then asks the solver for an input that
would have taken one of those branches the other way. Each answer is a new
input, and the loop repeats. This is the DART/CUTE method (Godefroid et al.
2005; Sen et al. 2005).

The engine reports `Status::Violated` when a run reaches a `Check` and the
check fails. The witness is the input sequence that run executed on.

It starts from the all-zero input, so it subsumes what `concrete` finds on its
first iteration, and diverges only once a branch needs flipping.

## Why it exists

Forward symbolic execution enters a call knowing only what it has learned
*before* that point. When the fact that pins the input lies after the call,
it knows nothing, and a recursive callee over an unconstrained argument forks
until its budget is gone. The `jayhorn-recursive` `Unsat*` tasks have exactly
this shape:

```java
int x = Verifier.nondetInt();
int result = fibonacci(x);      // explored with x unconstrained: exponential
if (x != 5 || result == 3) return; else assert false;
```

Three measurements on 2026-09-06 isolate the cause:

| change | result |
|---|---|
| unchanged | UNKNOWN |
| fork budget raised 8x | UNKNOWN |
| `if (x != 5)` moved above the call | FALSE |

So the blocker is evaluation order, not budget and not the solver.

Concolic execution reverses the roles. The concrete run decides control flow,
which costs six additions rather than an exponential tree, and the solver only
ever sees the branch conditions along one path. On `UnsatFibonacci01` it finds
`x = 5` on the second run.

## What it assumes, and where it is unsound if the assumption breaks

The engine reports a violation only when a real execution reached the check
and the check failed. The solver proposes inputs; it never decides that
something is violated. The witness is the input that execution ran on, so it
reproduces by construction.

That property is what makes an incomplete symbolic shadow harmless.
`sym_rvalue` declines any operation it cannot model faithfully:

- **Integer division and remainder.** SMT-LIB's are Euclidean, Java's truncate
  toward zero (JLS 15.17.2).
- **Every bitwise and shift operator.** Linear integer arithmetic has none.

Declining loses branch flips, and therefore paths. It cannot produce a wrong
answer, because the concrete run is the arbiter.

Solver-proposed inputs are constrained to the `int` range. Without that the
model can name a value no Java `int` holds, and the next run would execute
something the JVM never could.

## Known incompleteness

- **Only the entry frame carries a symbolic shadow.** `VarId`s are numbered per
  body, so one map cannot serve two frames — and the recursion this engine
  exists to defeat is precisely what should run concretely. A branch inside a
  callee therefore yields no flip.
- **A branch on a call result cannot be flipped.** The result is concrete, so
  it has no shadow. `UnsatAddition02` needs `m, n >= 100` with `m + n < 200`,
  which requires overflow, and the deciding branch tests the result of
  `addition(m, n)`. The engine correctly reports UNKNOWN. Solving it needs a
  summary of the callee, which is CHC's job, not this engine's.
- **Bounded search.** `MAX_ITERATIONS` (60) caps runs and
  `MAX_FLIPS_PER_PATH` (24) caps how many branches one path contributes. Both
  are fitted constants, recorded as such: they were chosen to walk a handful
  of guards deep, not raised until a benchmark passed.

## How it is certified

Every `Violated` status goes to `core::certify::JvmReplay` before it reaches a
verdict, the same as `concrete`. A deterministic shadow `Verifier` replays the
recorded input sequence against the real classpath, and only
`CertResult::Confirmed` survives; anything else is downgraded to UNKNOWN in
`ajave-cli`.

On `UnsatFibonacci01` the census line reads:

```
concolic: violation after 2 run(s), choices=[5]
REPLAY_CENSUS result=Confirmed thrown=java.lang.AssertionError
```

## Measured effect

Registering the engine moved `jayhorn-recursive` valid-assert from 5 correct to
9, and the full corpus from 857 to **862** (724 correct, no new wrong answers)
with no-runtime-exception unchanged at 1118. Wall time rose about 1.7%, since
the engine runs on every task.

`benchmarks/ajave/engine-recursion/ConstraintBelowRecursiveCall` isolates the
shape in ten lines and fails without this engine.
