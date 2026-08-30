// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NarrowingCastTruncates
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    int big = 300;
    byte b = (byte) big;
    assert b == 44;
    char c = (char) -1;
    assert c == 65535;
  }
}
