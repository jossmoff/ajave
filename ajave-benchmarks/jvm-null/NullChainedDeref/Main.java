// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NullChainedDeref
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  static class Node { int value; }
  static class Holder { Node inner; }
  public static void main(String[] args) {
    // The outer object is non-null but its field is not.
    Holder h = new Holder();
    int v = h.inner.value;
    assert v == 0;
  }
}
