// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: FinallyRunsOnException
// Expected: valid-assert=true, no-runtime-exception=n/a

public class Main {

  public static void main(String[] args) {
    int[] state = new int[1];
    try {
      throw new IllegalStateException();
    } catch (RuntimeException e) {
      state[0] = 1;
    } finally {
      state[0] = state[0] + 10;
    }
    assert state[0] == 11;
  }
}
