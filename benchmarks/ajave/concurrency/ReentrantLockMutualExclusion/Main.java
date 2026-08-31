// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ReentrantLockMutualExclusion
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Both increments are inside lock/unlock on the same ReentrantLock, so they
//   cannot interleave. After both joins the counter is exactly 2.

import java.util.concurrent.locks.ReentrantLock;
public class Main {
  static class Box { int n = 0; }
  static class Inc implements Runnable {
    final ReentrantLock l; final Box b;
    Inc(ReentrantLock l, Box b) { this.l = l; this.b = b; }
    public void run() { l.lock(); try { b.n++; } finally { l.unlock(); } }
  }
  public static void main(String[] args) throws Exception {
    ReentrantLock l = new ReentrantLock();
    Box b = new Box();
    Thread t = new Thread(new Inc(l, b));
    t.start();
    l.lock(); try { b.n++; } finally { l.unlock(); }
    try { t.join(); } catch (InterruptedException e) { }
    assert b.n == 2;
  }
}
