// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: CheckedHandlerDoesNotCatchRuntime
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  static void maybeIo() throws java.io.IOException { }
  public static void main(String[] args) {
    // Catching a checked exception must not mask the NPE.
    try {
      maybeIo();
      String s = null;
      s.length();
    } catch (java.io.IOException e) {
      // does not catch NullPointerException
    }
  }
}
