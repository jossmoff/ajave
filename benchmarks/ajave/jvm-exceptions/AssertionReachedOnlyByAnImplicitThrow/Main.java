// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a deterministic implicit exception reaches its handler
// Expected: valid-assert=false, no-runtime-exception=true
//
// The pair to `AssertionInCatchBlock`, and the contrast is the whole point.
// That benchmark reaches its handler from an *explicit* `throw` inside a
// callee, which the BMC dispatches (`explore.rs::dispatch_exception`). This
// one reaches the handler from an exception the JVM raises *implicitly* at a
// single instruction, with no `athrow` anywhere in the method.
//
// Ground truth (by construction, from the JVMS, NOT by observation):
//   JVMS 6.5 `idiv`: "if the value of the divisor is zero, idiv throws an
//   ArithmeticException". `d` is 0 on every execution, so the division throws
//   on every execution. javac emits an exception-table entry covering the try
//   range with catch_type = java/lang/ArithmeticException, so control
//   transfers to the handler, and `assert false` there throws AssertionError.
//   The assertion is therefore violated on every execution -- there is no
//   nondeterminism in this program at all.
//
//   valid-assert = false. And no-runtime-exception = true: the
//   ArithmeticException is caught, and AssertionError is an Error, not a
//   RuntimeException, so nothing that property cares about escapes main.
//
// What ajave does (2026-10-29): correct, and the engine that gets it is the
// finding.
//   ajave answers FALSE, and JVM replay confirms the witness. But neither the
//   BMC nor CHC reports a violation (`violated=0` for both): the *concrete*
//   engine carries this task. The program is deterministic, so the all-zero
//   probe executes it exactly -- `--interpret` prints
//   `INTERPRET ESCAPED java.lang.AssertionError` -- and walks into the handler
//   the way a JVM does.
//
//   So this benchmark pins the concrete path, and it deliberately does *not*
//   demonstrate the gap it was first written to demonstrate. Writing it was
//   what disproved the hypothesis that implicit exceptions never reach their
//   handlers. See `ImplicitThrowReachesItsHandlerOnlyForSomeInputs` for the
//   case the concrete engine cannot reach, which is where the BMC's limit
//   becomes visible.

public class Main {

  public static void main(String[] args) {
    int d = 0;
    try {
      // JVMS idiv: divisor zero throws ArithmeticException. Implicit -- there
      // is no `throw` statement in this method.
      int q = 1 / d;
      // Unreachable: the division above always throws.
      assert true;
    } catch (ArithmeticException e) {
      // Reachable on every execution, so this always fires.
      assert false;
    }
  }
}
