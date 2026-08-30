// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: InstanceOfGuardsCast
// Expected: valid-assert=n/a, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    Object o = "a string";
    if (o instanceof Integer) {
      Integer i = (Integer) o;
      assert i != null;
    }
  }
}
