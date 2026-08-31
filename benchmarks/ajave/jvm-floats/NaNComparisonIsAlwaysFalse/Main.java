// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NaNComparisonIsAlwaysFalse
// Expected: valid-assert=true, no-runtime-exception=true
//
// Regression for a real divergence between the concrete interpreter and the
// JVM (found 2026-08-31 while making search-based float falsification work).
//
// Ground truth (by construction, NOT by observation):
//   Math.asin(x) is NaN for |x| > 1. Every ordered comparison against NaN is
//   false in IEEE-754, so `a < 999.0` does not hold and the assertion is never
//   reached. javac compiles `<` on doubles to `dcmpg; ifge`, and dcmpg yields
//   +1 for NaN, so the branch jumps over the body.
//
//   ajave reported a violation here: it computed asin(1000.0) and then got the
//   NaN comparison wrong, proposing x=1000 as a counterexample that JVM replay
//   duly refused. The verdict was never wrong — replay arbitrates — but the
//   engine wasted its search on an unreachable path.

public class Main {

  public static void main(String[] args) {
    double a = Math.asin(1000.0);
    // NaN < anything is false, so this assertion is unreachable.
    if (a < 999.0) {
      assert false;
    }
    // The same in the other direction: NaN > anything is also false.
    if (a > -999.0) {
      assert false;
    }
    // And NaN is not equal to itself.
    if (a == a) {
      assert false;
    }
  }
}
