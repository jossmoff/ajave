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

//
// DRF-SC BOUNDARY -- this now reports UNKNOWN, and that is correct.
//
// The program has a data race, and the explorer only considers sequentially
// consistent executions. JLS 17.4.5 gives the SC guarantee to data-race-free
// programs only, so on a racy program an exhaustive SC search proves nothing
// about a real JVM and the engine declines to discharge. The verdict below is
// still the JVM's ground truth; we simply cannot establish it this way.
//
// Losing this TRUE is the point of the gate: the alternative is claiming a
// proof that a real JVM is not obliged to honour.

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
