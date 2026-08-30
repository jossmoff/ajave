// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NullGuardedByBranch
// Expected: valid-assert=n/a, no-runtime-exception=true

public class Main {

  static class Node { int value; }
  public static void main(String[] args) {
    Node n = org.sosy_lab.sv_benchmarks.Verifier.nondetBoolean() ? new Node() : null;
    if (n != null) {
      int v = n.value;
      assert v == 0;
    }
  }
}
