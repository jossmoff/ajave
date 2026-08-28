// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: BitwiseAndOfComparisons
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // javac lowers && over comparisons into a bitwise & of 0/1 values.
    int i = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    org.sosy_lab.sv_benchmarks.Verifier.assume(i >= 0 && i < 10);
    assert i >= 0 & i < 10;
  }
}
