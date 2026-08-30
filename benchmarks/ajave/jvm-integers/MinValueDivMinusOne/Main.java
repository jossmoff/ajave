// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: MinValueDivMinusOne
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Integer.MIN_VALUE / -1 overflows and wraps back to MIN_VALUE.
    // It does NOT throw, unlike division by zero.
    int x = Integer.MIN_VALUE;
    int y = x / -1;
    assert y == Integer.MIN_VALUE;
  }
}
