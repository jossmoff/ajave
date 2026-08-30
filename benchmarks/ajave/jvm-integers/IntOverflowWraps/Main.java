// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: IntOverflowWraps
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // JVM int arithmetic wraps on overflow rather than throwing.
    int x = Integer.MAX_VALUE;
    int y = x + 1;
    assert y == Integer.MIN_VALUE;
  }
}
