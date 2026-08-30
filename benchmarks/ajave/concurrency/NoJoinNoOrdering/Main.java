// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NoJoinNoOrdering
// Expected: valid-assert=n/a, no-runtime-exception=true
//
// Ground truth (by construction, NOT by observation):
//   Without join() the main thread may read `value` before or after the write,
//   so both 0 and 42 are legal outcomes. The program asserts nothing about
//   which, and no read here can throw — so it is NRE-safe while being
//   genuinely nondeterministic. A verifier that reports a violation is wrong;
//   one that reports TRUE for valid-assert without reasoning about the
//   interleaving is guessing.

public class Main {

  static class Setter implements Runnable {
    int value = 0;
    public void run() { value = 42; }
  }
  public static void main(String[] args) throws Exception {
    Setter s = new Setter();
    new Thread(s).start();
    int observed = s.value;
    assert observed == 0 || observed == 42;
  }
}
