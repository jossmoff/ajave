// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: FieldValueSurvivesCall
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  static class Counter { int n; }
  static void pureCall() { }
  public static void main(String[] args) {
    // Requires knowing that pureCall() does not write the field.
    Counter c = new Counter();
    c.n = 5;
    pureCall();
    assert c.n == 5;
  }
}
