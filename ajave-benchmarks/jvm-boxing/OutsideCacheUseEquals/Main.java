// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: OutsideCacheUseEquals
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Outside the cache range identity is not guaranteed, but equals holds.
    Integer a = 1000, b = 1000;
    assert a.equals(b);
  }
}
