// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: FieldClobberedByCall
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  static class Counter { int n; }
  static void bump(Counter c) { c.n = c.n + 1; }
  public static void main(String[] args) {
    // The callee does write the field, so the analysis must not assume 5.
    Counter c = new Counter();
    c.n = 5;
    bump(c);
    assert c.n == 6;
  }
}
