// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: FloatDivByZeroIsInfinity
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Floating-point division by zero yields Infinity, not an exception.
    double d = 1.0 / 0.0;
    assert Double.isInfinite(d);
  }
}
