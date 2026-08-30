// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: UnsignedShiftDiffersFromSigned
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    int x = -1;
    assert (x >> 1) == -1;
    assert (x >>> 1) == Integer.MAX_VALUE;
  }
}
