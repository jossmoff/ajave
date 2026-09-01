// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: an invariant over every element of an array
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The first loop writes 0 to every element in range; the second reads them
//   back. So the assertion holds for every element and every array length.
//
//   The length is nondeterministic, so no bounded unrolling establishes this:
//   a BMC can only check as many iterations as it unrolls. Proving it needs a
//   universally quantified invariant over the array -- exactly the reasoning
//   the `algorithms` category is full of, and the reason CHC declines every
//   task there today (its LIA encoding has no heap sort at all).
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    if (n < 0 || n > 1000) return;
    int[] a = new int[n];
    for (int i = 0; i < n; i++) {
      a[i] = 0;
    }
    for (int i = 0; i < n; i++) {
      assert a[i] == 0;
    }
  }
}
