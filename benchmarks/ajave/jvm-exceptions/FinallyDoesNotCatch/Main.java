// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: `finally` runs on the exceptional path but does not catch
// Expected: no-runtime-exception=false
//
// Ground truth (by construction, NOT by observation):
//   `10 / i` throws ArithmeticException at i == 0. A `finally` block executes
//   and then **rethrows**: JLS 14.20.2 says if the try block completes
//   abruptly for reason R and the finally block completes normally, the try
//   statement completes abruptly for reason R. So the exception propagates out
//   of main and the property is violated. Run with i = 0 to see it.
//
// Why this benchmark exists:
//   In the JVM exception table a `finally` handler has `catch_type == 0`, and
//   `guarded_at` returned true for that case with the comment "catch-all /
//   finally". A true catch-all -- `catch (Throwable t)` -- does not have
//   catch_type 0; it points at Throwable. Entry 0 means *finally*, which is
//   compiled as a handler that runs the cleanup and rethrows via `athrow`.
//
//   Treating it as catching removes the obligation from no-runtime-exception
//   seeding entirely, so a genuinely escaping exception is never looked for.
//   That is the dangerous direction: guarding can only lose violations, and a
//   lost violation on a task expecting FALSE is a wrong TRUE at -16.
//
//   Paired with SpecificHandlerCatchesItsOwnException, where the handler really
//   does catch and the expected verdict really is TRUE.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  static int sink = 0;
  public static void main(String[] args) {
    int i = Verifier.nondetInt();
    try {
      sink = 10 / i;
    } finally {
      sink = sink + 1;
    }
  }
}
