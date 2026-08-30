// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: MutualRecursionParity
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  static boolean isEven(int n) { return n == 0 ? true : isOdd(n - 1); }
  static boolean isOdd(int n) { return n == 0 ? false : isEven(n - 1); }
  public static void main(String[] args) {
    int n = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    org.sosy_lab.sv_benchmarks.Verifier.assume(n >= 0 && n <= 10);
    assert isEven(n) != isOdd(n);
  }
}
