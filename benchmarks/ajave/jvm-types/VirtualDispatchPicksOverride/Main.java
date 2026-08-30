// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: VirtualDispatchPicksOverride
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  static class Base { int value() { return 1; } }
  static class Derived extends Base { int value() { return 2; } }
  public static void main(String[] args) {
    Base b = new Derived();
    assert b.value() == 2;
  }
}
