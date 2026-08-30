// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: DeepPathToViolation
// Expected: valid-assert=false, no-runtime-exception=n/a

public class Main {

  public static void main(String[] args) {
    // A specific input is needed; reachable only by solving, not by probing.
    int x = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    if (x > 1000 && x < 1010 && x % 7 == 3) {
      assert false;
    }
  }
}
