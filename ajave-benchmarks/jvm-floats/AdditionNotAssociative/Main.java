// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: AdditionNotAssociative
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    double a = 1e16, b = -1e16, c = 1.0;
    assert ((a + b) + c) == 1.0;
    assert (a + (b + c)) == 0.0;
  }
}
