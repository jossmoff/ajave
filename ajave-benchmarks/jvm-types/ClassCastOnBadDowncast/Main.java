// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ClassCastOnBadDowncast
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    Object o = "a string";
    Integer i = (Integer) o;
    assert i != null;
  }
}
