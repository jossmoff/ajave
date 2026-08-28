// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NullFieldDeref
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  static class Node { int value; }
  public static void main(String[] args) {
    Node n = null;
    int v = n.value;
    assert v == 0;
  }
}
