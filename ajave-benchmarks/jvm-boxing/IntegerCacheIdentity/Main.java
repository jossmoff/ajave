// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: IntegerCacheIdentity
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Values in [-128, 127] are cached, so == compares equal by identity.
    Integer a = 127, b = 127;
    assert a == b;
  }
}
