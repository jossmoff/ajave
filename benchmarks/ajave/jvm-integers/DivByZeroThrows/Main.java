// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: DivByZeroThrows
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    // ArithmeticException is a RuntimeException: NRE must be violated.
    int d = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    org.sosy_lab.sv_benchmarks.Verifier.assume(d == 0);
    int y = 10 / d;
    assert y != 0;
  }
}
