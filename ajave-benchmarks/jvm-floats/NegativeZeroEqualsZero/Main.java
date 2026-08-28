// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NegativeZeroEqualsZero
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // -0.0 == 0.0 is true, but they differ under Double.compare.
    double negZero = -0.0;
    assert negZero == 0.0;
    assert Double.compare(negZero, 0.0) < 0;
  }
}
