// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: OffByOneInLoop
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    int[] a = new int[10];
    for (int i = 0; i <= a.length; i++) {
      a[i] = i;
    }
    assert a[0] == 0;
  }
}
