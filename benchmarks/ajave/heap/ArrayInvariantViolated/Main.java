// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: the same shape, genuinely violated
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   The loop writes 1, the assertion demands 0, so any array with at least one
//   element violates it. Paired with ArrayInvariantHoldsForAllElements so that
//   an engine claiming to reason about arrays must separate them -- one that
//   simply says TRUE for anything with an array would pass the first and fail
//   this one.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    if (n < 1 || n > 1000) return;
    int[] a = new int[n];
    for (int i = 0; i < n; i++) {
      a[i] = 1;
    }
    for (int i = 0; i < n; i++) {
      assert a[i] == 0;
    }
  }
}
