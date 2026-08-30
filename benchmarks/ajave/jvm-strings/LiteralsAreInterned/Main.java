// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: LiteralsAreInterned
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    String a = "hello", b = "hello";
    assert a == b;
  }
}
