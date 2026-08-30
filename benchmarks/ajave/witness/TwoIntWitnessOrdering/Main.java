// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: TwoIntWitnessOrdering
// Expected: valid-assert=false, no-runtime-exception=n/a

public class Main {

  public static void main(String[] args) {
    // Two nondet reads: the witness must preserve their order.
    int a = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    int b = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    if (a == 1 && b == 2) {
      assert false;
    }
  }
}
