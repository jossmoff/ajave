// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: FactorialPositive
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  static int fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }
  public static void main(String[] args) {
    int n = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    org.sosy_lab.sv_benchmarks.Verifier.assume(n >= 0 && n <= 6);
    assert fact(n) >= 1;
  }
}
