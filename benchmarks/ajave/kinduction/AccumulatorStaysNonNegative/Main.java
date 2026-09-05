// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: induction over a nondeterministic accumulator
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   `sum >= 0` is inductive. Assume it for an arbitrary sum:
//     * If the guard holds, then sum <= 1000 and 0 <= d <= 100, so
//       sum' = sum + d lies in [0, 1100]. The bounds rule out overflow, so
//       the JVM's wrapping addition agrees with the mathematical one here.
//     * If the guard fails, sum is unchanged.
//
//   Unlike the other TRUE cases in this directory the loop body reads a fresh
//   nondeterministic value each iteration, so the step case has to hold for
//   every `d` rather than for a single trace. That is what separates an
//   induction from an unrolling: no finite number of unrollings pins down `d`.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int sum = 0;
    while (Verifier.nondetBoolean()) {
      int d = Verifier.nondetInt();
      if (d >= 0 && d <= 100 && sum <= 1000) {
        sum = sum + d;
      }
      assert sum >= 0;
    }
  }
}
