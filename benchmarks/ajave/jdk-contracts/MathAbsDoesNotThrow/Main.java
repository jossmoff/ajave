// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: MathAbsDoesNotThrow
// Expected: valid-assert=n/a, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Math.abs(MIN_VALUE) returns MIN_VALUE rather than throwing.
    int x = Math.abs(Integer.MIN_VALUE);
    assert x == Integer.MIN_VALUE;
  }
}
