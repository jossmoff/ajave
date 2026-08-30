// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: IntervalNarrowingProvesAssert
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Provable by the interval domain alone, no solver needed.
    int x = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    org.sosy_lab.sv_benchmarks.Verifier.assume(x > 5);
    assert x > 3;
  }
}
