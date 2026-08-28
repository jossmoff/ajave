// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: CaughtExceptionNotPropagated
// Expected: valid-assert=n/a, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // The NPE is caught, so no RuntimeException escapes main.
    try {
      String s = null;
      s.length();
    } catch (NullPointerException e) {
      // handled
    }
  }
}
