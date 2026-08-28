// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: RemainderSignFollowsDividend
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Java's % takes the sign of the dividend, unlike floorMod.
    assert (-7 % 3) == -1;
    assert (7 % -3) == 1;
  }
}
