// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: UnboxingNullThrows
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    Integer boxed = null;
    int raw = boxed;
    assert raw == 0;
  }
}
