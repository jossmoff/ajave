// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a guarded counter whose bound is 1-inductive
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The invariant `x <= 100` is inductive exactly as written. Assume it at
//   the loop head for an ARBITRARY x, not merely a reachable one:
//     * x < 100  =>  x' = x + 1 <= 100.
//     * x >= 100 =>  the guard fails, x' = x, still <= 100.
//   Both cases land back in the invariant, so no strengthening is needed and
//   the step case closes at k = 1.
//
//   No overflow is possible: x only increases while x < 100, so it never
//   exceeds 100 and never approaches Integer.MAX_VALUE.
//
//   The loop bound is nondeterministic and unconstrained, so no finite
//   unrolling covers every execution -- a BMC can only report Bounded { k }.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int x = 0;
    while (Verifier.nondetBoolean()) {
      if (x < 100) {
        x = x + 1;
      }
      assert x <= 100;
    }
  }
}
