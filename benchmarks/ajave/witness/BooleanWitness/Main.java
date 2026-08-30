// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: BooleanWitness
// Expected: valid-assert=false, no-runtime-exception=n/a

public class Main {

  public static void main(String[] args) {
    boolean p = org.sosy_lab.sv_benchmarks.Verifier.nondetBoolean();
    boolean q = org.sosy_lab.sv_benchmarks.Verifier.nondetBoolean();
    if (p && !q) {
      assert false;
    }
  }
}
