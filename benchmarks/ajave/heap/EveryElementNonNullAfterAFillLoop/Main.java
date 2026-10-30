// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: EveryElementNonNullAfterAFillLoop
// Expected: valid-assert=true, no-runtime-exception=true
//
// The gate the whole heap effort runs into, reduced from `aastore_aaload1` to
// the smallest program that still needs it.
//
// Proving the second loop's assertion requires the invariant
//
//     ∀j. 0 ≤ j < i → a[j] ≠ null
//
// synthesised from the *first* loop and consumed in the second. Modelling
// array contents (A1–A3, B3) made that property *expressible*; it is not the
// proof. Nothing in the portfolio infers a universally quantified invariant
// over an array, which is why this is UNKNOWN with every engine enabled and
// full contents modelling in place.
//
// The bound is nondeterministic on purpose. With a constant bound the BMC
// unrolls both loops and proves the assertion without any invariant at all,
// so a constant-bound version of this program tests nothing — it would pass
// and the capability would still be missing. The guard keeps `n` small enough
// that the task is not merely about `NegativeArraySizeException`.
//
// Ground truth (by construction, from the JLS, NOT by observation):
//   The first loop assigns a fresh `A` to every index in `0..n`, and `new`
//   never yields null (JLS 15.9.4), so every element is non-null when the
//   second loop reads it. Both assertions hold for every `n` reaching them.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  static class A {
    int x;
  }

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    if (n < 1 || n > 1000) {
      return;
    }
    A[] a = new A[n];
    for (int i = 0; i < n; i++) {
      a[i] = new A();
    }
    for (int i = 0; i < n; i++) {
      assert a[i] != null;
    }
  }
}
