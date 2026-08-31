// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: Condition.await with no state guard
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   The waiter awaits unconditionally. In the schedule where main takes the
//   lock and signals first, there is no waiter yet, so the signal is lost --
//   a Condition remembers nothing. The worker then awaits forever and main
//   blocks in join(), leaving no runnable thread with threads still alive.
//   The other schedule completes, so this is a bug only some interleavings
//   expose, which is exactly what the explorer has to find.
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.Condition;
public class Main {
  static final ReentrantLock lock = new ReentrantLock();
  static final Condition cond = lock.newCondition();
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() {
        lock.lock();
        try { cond.await(); } catch (InterruptedException e) { }
        finally { lock.unlock(); }
      }
    });
    t.start();
    lock.lock();
    try { cond.signal(); } finally { lock.unlock(); }
    t.join();
  }
}
