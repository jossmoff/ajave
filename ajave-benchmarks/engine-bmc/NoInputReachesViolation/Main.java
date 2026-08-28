// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NoInputReachesViolation
// Expected: valid-assert=true, no-runtime-exception=n/a

public class Main {

  public static void main(String[] args) {
    // The guard is unsatisfiable, so the assertion is unreachable.
    int x = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    if (x > 10 && x < 5) {
      assert false;
    }
  }
}
