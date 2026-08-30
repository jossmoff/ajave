// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: StaticInitRunsBeforeAccess
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  static class Config {
    static final int LIMIT;
    static { LIMIT = 42; }
  }
  public static void main(String[] args) {
    assert Config.LIMIT == 42;
  }
}
