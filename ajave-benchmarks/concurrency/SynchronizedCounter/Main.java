// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: SynchronizedCounter
// Expected: valid-assert=true, no-runtime-exception=true
//
// Ground truth (by construction, NOT by observation):
//   Both increments hold the same monitor, so the read-modify-write is atomic
//   and the two increments are ordered by the monitor's synchronizes-with
//   edge. The total is 2 under every schedule.

public class Main {

  static class Counter {
    int n = 0;
    synchronized void inc() { n = n + 1; }
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
