// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: CharAtOutOfBounds
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    String s = "abc";
    char c = s.charAt(5);
    assert c == 'a';
  }
}
