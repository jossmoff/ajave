// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: MathAddExactOverflows
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    int x = Math.addExact(Integer.MAX_VALUE, 1);
    assert x != 0;
  }
}
