// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: Condition.await/signal with a state guard
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   The waiter tests `ready` inside the lock and only awaits while it is
//   false, so a signal delivered before the waiter arrives is not lost -- the
//   waiter simply never awaits. This is the reason the canonical form of a
//   condition wait is `while (!cond) await();` rather than a bare `await()`.
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.Condition;
public class Main {
  static final ReentrantLock lock = new ReentrantLock();
  static final Condition cond = lock.newCondition();
  static boolean ready = false;
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() {
        lock.lock();
        try {
          while (!ready) { try { cond.await(); } catch (InterruptedException e) { return; } }
        } finally { lock.unlock(); }
      }
    });
    t.start();
    lock.lock();
    try { ready = true; cond.signal(); } finally { lock.unlock(); }
    t.join();
  }
}
