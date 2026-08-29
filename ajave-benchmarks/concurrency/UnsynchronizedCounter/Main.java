// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: UnsynchronizedCounter
// Expected: valid-assert=false, no-runtime-exception=n/a
//
// Ground truth (by construction, NOT by observation):
//   The increments are not atomic: both threads can read 0, both write 1, and
//   the total is 1 rather than 2. That interleaving is permitted, so the
//   assertion is violable. NOTE the asymmetry — this is expected FALSE, but a
//   single execution will usually print 2, so running it is not evidence
//   either way.

public class Main {

  static class Counter {
    int n = 0;
    void inc() { n = n + 1; }
  }
  static class Inc implements Runnable {
    final Counter c;
    Inc(Counter c) { this.c = c; }
    public void run() { c.inc(); }
  }
  public static void main(String[] args) throws Exception {
    Counter c = new Counter();
    Thread t = new Thread(new Inc(c));
    t.start();
    c.inc();
    try { t.join(); } catch (InterruptedException e) { }
    assert c.n == 2;
  }
}
