// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: AtomicCounterIsRaceFree
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Both threads increment via AtomicInteger.incrementAndGet, which is a single
//   atomic read-modify-write. No interleaving can lose an update, so after both
//   joins the counter is exactly 2 and the assertion holds.
//
//   The contrast with UnsynchronizedCounter is the point: identical structure,
//   but a plain `n++` is three separate steps and does lose updates.

import java.util.concurrent.atomic.AtomicInteger;
public class Main {
  static class Inc implements Runnable {
    final AtomicInteger c;
    Inc(AtomicInteger c) { this.c = c; }
    public void run() { c.incrementAndGet(); }
  }
  public static void main(String[] args) throws Exception {
    AtomicInteger c = new AtomicInteger(0);
    Thread t = new Thread(new Inc(c));
    t.start();
    c.incrementAndGet();
    try { t.join(); } catch (InterruptedException e) { }
    assert c.get() == 2;
  }
}
