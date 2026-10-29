// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: an implicit exception reachable only on *some* inputs
// Expected: valid-assert=false, no-runtime-exception=true
//
// The third of a trio, and the only one ajave gets wrong. Together they
// separate three different mechanisms that all look like "an assertion in a
// catch block":
//
//   AssertionInCatchBlock                   explicit `throw` in a callee.
//                                           Handled: explore.rs's
//                                           `dispatch_exception`.
//   AssertionReachedOnlyByAnImplicitThrow   implicit throw, deterministic.
//                                           Handled, but by the *concrete*
//                                           engine executing it exactly.
//   this one                                implicit throw, input-dependent.
//                                           Not handled by anything.
//
// Ground truth (by construction, from the JVMS, NOT by observation):
//   `d` is unconstrained except for `d != 0`. At d == 7 the divisor `d - 7` is
//   zero, and JVMS 6.5 `idiv` throws ArithmeticException when the divisor is
//   zero. javac covers the try range with an exception-table entry for
//   java/lang/ArithmeticException, so control transfers to the handler and
//   `assert false` throws AssertionError. d == 7 is a legal input, so the
//   assertion is violated on a real execution.
//
//   valid-assert = false, witnessed by d = 7. Confirmed on a real JVM: the
//   handler is reached and AssertionError is thrown under -ea.
//
//   no-runtime-exception = true: ArithmeticException is caught, and
//   AssertionError is an Error rather than a RuntimeException, so nothing that
//   property cares about escapes main.
//
// What ajave does (2026-10-29): UNKNOWN. A precision loss, not a wrong answer.
//   Two engines could decide this and neither does.
//
//   The concrete engine probes the all-zero nondet sequence, which gives
//   d == 0 and returns at the guard -- `--interpret` prints `INTERPRET CLEAN`.
//   By design it does not search for d == 7: hunting input values is the SMT
//   engine's job (CLAUDE.md, "no hardcoded nondet patterns").
//
//   The BMC is the engine that should find d == 7, and it cannot reach the
//   handler at all. `explore.rs::handle_check` asks the solver whether the
//   obligation's condition can fail, records a violation if so, and then
//   continues *straight-line* to the next statement. A failing check never
//   forks control along the block's exceptional edge. The lifter does emit
//   that edge -- `! exc: java/lang/ArithmeticException -> bb<handler>` -- and
//   the handler's Assertion obligation is seeded and reported open; the
//   explorer simply never goes there. `handle_throw` and `dispatch_exception`
//   cover `athrow` and cross-method propagation respectively, so an explicit
//   throw works and an implicit one does not.
//
//   The shape is invisible in the blocker census: the BMC publishes nothing
//   about the obligation -- no discharge, no violation, and no refusal naming
//   a blocker, because it never evaluated it. Such a task lands in
//   `tools/blocker_census.py`'s `no-candidate` bucket rather than under any
//   nameable cause.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    int d = Verifier.nondetInt();
    // Keeps the all-zero probe away from the violation, so the concrete
    // engine cannot carry this task the way it carries the deterministic
    // sibling. Nothing else depends on the guard.
    if (d == 0) {
      return;
    }
    try {
      // Throws ArithmeticException exactly when d == 7. Implicit: there is no
      // `throw` statement in this method.
      int q = 1 / (d - 7);
      assert true;
    } catch (ArithmeticException e) {
      // Reachable, for d == 7.
      assert false;
    }
  }
}
