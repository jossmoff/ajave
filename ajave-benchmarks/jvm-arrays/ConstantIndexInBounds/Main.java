// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ConstantIndexInBounds
// Expected: valid-assert=n/a, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Length is a constant, indices are constants: provable without solving.
    int[] a = new int[3];
    a[0] = 1; a[1] = 2; a[2] = 3;
    assert a.length == 3;
  }
}
