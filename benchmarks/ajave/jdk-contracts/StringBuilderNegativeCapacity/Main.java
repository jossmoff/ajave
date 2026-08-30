// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: StringBuilderNegativeCapacity
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    StringBuilder sb = new StringBuilder(-1);
    assert sb != null;
  }
}
