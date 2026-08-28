// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: IntOverflowWrapsViolated
// Expected: valid-assert=false, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Same wraparound, asserted incorrectly: overflow does not saturate.
    int x = Integer.MAX_VALUE;
    int y = x + 1;
    assert y == Integer.MAX_VALUE;
  }
}
