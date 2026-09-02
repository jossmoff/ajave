// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a handler for a *different* exception class does not guard
// Expected: no-runtime-exception=false
//
// Ground truth (by construction, NOT by observation):
//   `10 / i` throws ArithmeticException at i == 0. NullPointerException is not
//   a supertype of ArithmeticException -- they are siblings under
//   RuntimeException -- so the handler does not catch it and it propagates out
//   of main. Run with i = 0 to see it.
//
// Paired with SpecificHandlerCatchesItsOwnException so the two cannot be passed
// by the same wrong mechanism. Treating any specific handler as guarding gives
// the right answer on the first and a wrong TRUE here, and that is the
// dangerous direction: marking an obligation guarded removes it from
// no-runtime-exception seeding, so an over-eager guard loses a real violation.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    try {
      int i = Verifier.nondetInt();
      int j = 10 / i;
    } catch (NullPointerException e) {
      // does not catch ArithmeticException
    }
  }
}
