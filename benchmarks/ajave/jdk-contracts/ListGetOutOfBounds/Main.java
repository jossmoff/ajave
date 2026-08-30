// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ListGetOutOfBounds
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    java.util.List<String> l = new java.util.ArrayList<String>();
    String s = l.get(0);
    assert s != null;
  }
}
