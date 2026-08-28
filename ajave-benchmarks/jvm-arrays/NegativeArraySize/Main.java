// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NegativeArraySize
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    int n = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    org.sosy_lab.sv_benchmarks.Verifier.assume(n < 0);
    int[] a = new int[n];
    assert a.length >= 0;
  }
}
