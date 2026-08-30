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
