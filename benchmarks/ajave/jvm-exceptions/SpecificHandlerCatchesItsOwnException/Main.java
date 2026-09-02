// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a handler for the exact exception class guards the obligation
// Expected: no-runtime-exception=true
//
// Ground truth (by construction, NOT by observation):
//   `10 / i` throws ArithmeticException exactly when i == 0, and the enclosing
//   handler catches ArithmeticException, so nothing propagates out of main.
//   For every other i the division completes. No RuntimeException escapes on
//   any path, so the property holds.
//
// Why this benchmark exists:
//   `guarded_at` did not take the obligation kind, and accepted only
//   `Throwable`, `Exception`, `RuntimeException` and a catch-all. A handler for
//   the *specific* class did not count, so the DivByZero obligation was seeded
//   as escaping. The BMC then found i == 0, published a violation, JVM replay
//   refuted it -- the JVM catches it and exits 0 -- and the task sat UNKNOWN
//   with an unconfirmed violation nothing could discharge.
//
//   Measured as the blocker on 8 of 20 sampled no-runtime-exception tasks in
//   jbmc-regression, a category built out of exactly this shape.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    try {
      int i = Verifier.nondetInt();
      int j = 10 / i;
    } catch (ArithmeticException e) {
      // swallowed on purpose
    }
  }
}
