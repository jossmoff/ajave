// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NaNNotEqualItself
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    double nan = 0.0 / 0.0;
    assert nan != nan;
    assert Double.isNaN(nan);
  }
}
