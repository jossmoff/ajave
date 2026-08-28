// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: SingleIntWitness
// Expected: valid-assert=false, no-runtime-exception=n/a

public class Main {

  public static void main(String[] args) {
    // A FALSE verdict here must come with a replayable witness value.
    int x = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    if (x == 42) {
      assert false;
    }
  }
}
