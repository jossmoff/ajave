// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: IntegerValueOfIntIsTotal
// Expected: valid-assert=n/a, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    Integer i = Integer.valueOf(Integer.MIN_VALUE);
    assert i.intValue() == Integer.MIN_VALUE;
  }
}
