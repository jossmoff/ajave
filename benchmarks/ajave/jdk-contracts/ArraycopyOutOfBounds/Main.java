// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ArraycopyOutOfBounds
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    int[] src = new int[1], dst = new int[1];
    System.arraycopy(src, 0, dst, 0, 5);
    assert dst[0] == 0;
  }
}
