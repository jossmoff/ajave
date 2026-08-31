// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: NonVolatileNoGuarantee
// Expected: valid-assert=n/a, no-runtime-exception=true
//
// Ground truth (by construction, NOT by observation):
//   Without volatile there is no happens-before edge, so the main thread may
//   never observe the write at all — a legal outcome under the JMM, not a bug.
//   Included to check we do not report a violation for a program that is
//   merely nondeterministic. Nothing here can throw.

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

  static class Flag {
    int ready = 0;
  }
  static class Setter implements Runnable {
    final Flag f;
    Setter(Flag f) { this.f = f; }
    public void run() { f.ready = 1; }
  }
  public static void main(String[] args) throws Exception {
    Flag f = new Flag();
    Thread t = new Thread(new Setter(f));
    t.start();
    int seen = f.ready;
    try { t.join(); } catch (InterruptedException e) { }
    assert seen == 0 || seen == 1;
  }
}
