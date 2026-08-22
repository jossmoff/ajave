# NRA (nonlinear real arithmetic)

**Direction:** Under
**Tier:** 5 (specialist)
**Status:** working
**Source:** `roast-engines/src/nra.rs`
**Build:** behind the `nra` Cargo feature (on by default; links CVC5 statically)

## What it proves or finds

Targets the one benchmark family the bitvector engines cannot express at all:
methods calling transcendental `Math` functions — `sin`, `cos`, `exp`, `log`,
`pow`, `sqrt` and friends. Those are kept as `Rvalue::Call` in the IR rather
than havoced (see `roast-models`' `MathCall`) precisely so this engine can
encode them.

Selection is by `body_shape::analyze`: a body qualifies when
`suitable_for_nra()` holds — it uses transcendental math and does not use
heap operations the encoding cannot model. The engine then does a
path-sensitive DFS from entry to each error location, accumulating NRA
constraints, capped at `MAX_NRA_DEPTH = 50`.

With CVC5 the transcendentals are native. For solvers without them they are
declared as uninterpreted functions plus semantic range constraints
(`-1 ≤ sin(x) ≤ 1`, `sin(0) = 0`, `exp(x) > 0`, …). Solver preference chain:
CVC5 > dReal > Z3.

## What it assumes / where it's unsound if the assumption breaks

**This engine is `Under` and only ever publishes violations.** That is not a
limitation of the implementation, it is the honest reading of what NRA gives
you here, and it is worth spelling out because the arithmetic is subtle:

- **SAT is trustworthy.** A satisfying assignment yields concrete inputs, which
  become a witness, which `JvmReplay` runs on a real JVM before any FALSE is
  reported. The encoding being approximate cannot produce a wrong FALSE,
  because the JVM has the final say.
- **UNSAT is deliberately *not* acted on.** The encoding is over the reals;
  Java's `float` and `double` are IEEE 754. NaN, ±Inf and −0 are values a real
  does not have, and they can violate an assertion that genuinely holds over
  ℝ. So UNSAT over reals does not imply safety over floats, and the engine
  logs it and moves on rather than discharging. Discharging here would be a
  false TRUE on exactly the benchmarks this engine exists to handle.

Because it never discharges, `direction()` reports `Under` — matching what it
actually publishes. (It previously declared `Over` while passing
`Direction::Under` at the publish site; the blackboard gate reads the
caller-supplied direction, so the mismatch was invisible. The `Engine`
direction is now registered with the blackboard at init and checked on every
publish, so a declaration that disagrees with behaviour is rejected rather
than ignored.)

## Known incompleteness

- Only bodies whose shape passes `suitable_for_nra()`.
- Never proves safety, by design — see above. A transcendental benchmark that
  is TRUE has to be reached by some other engine, or comes back UNKNOWN.
- `MAX_NRA_DEPTH = 50` bounds path length.
- Requires the `nra` feature at build time and a solver at run time.

## How it's certified

Every violation goes through `JvmReplay` like any other FALSE — the witness is
replayed against the real bytecode with a shadow `Verifier` feeding the model's
values, and the verdict is downgraded to UNKNOWN if the expected exception does
not fire. This is the strongest certification in the system, and it is why an
approximate real-arithmetic encoding is safe to falsify from.
