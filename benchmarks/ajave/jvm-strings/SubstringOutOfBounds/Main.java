// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: SubstringOutOfBounds
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    String s = "abc";
    String t = s.substring(4);
    assert t != null;
  }
}
