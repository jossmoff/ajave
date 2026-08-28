// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: AssertionInCatchBlock
// Expected: valid-assert=false, no-runtime-exception=n/a

public class Main {

  static void thrower() { throw new IllegalStateException("boom"); }
  public static void main(String[] args) {
    // The assertion is reachable only via the exception edge out of a call.
    try {
      thrower();
      assert true;
    } catch (RuntimeException e) {
      assert false;
    }
  }
}
