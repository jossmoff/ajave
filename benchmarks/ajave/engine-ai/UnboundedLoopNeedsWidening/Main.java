// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: UnboundedLoopNeedsWidening
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // The trip count is not statically known, so the analysis only converges
    // if widening is applied at the loop header.
    int n = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    org.sosy_lab.sv_benchmarks.Verifier.assume(n > 0);
    int i = 0;
    while (i < n) { i++; }
    assert i >= 0;
  }
}
