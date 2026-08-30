// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ConstantIndexOutOfBounds
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    int[] a = new int[3];
    a[3] = 1;
    assert a[0] == 0;
  }
}
