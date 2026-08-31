// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ReentrantLockOrderInversion
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   AB/BA lock-order inversion, but over ReentrantLock rather than monitors.
//   An interleaving exists where each thread holds one lock and waits for the
//   other.
//
//   A single JVM run exits cleanly here, which is expected and proves nothing:
//   a race need not manifest. The argument is structural, not observational.

import java.util.concurrent.locks.ReentrantLock;
public class Main {
  static final ReentrantLock A = new ReentrantLock();
  static final ReentrantLock B = new ReentrantLock();
  static class BA implements Runnable {
    public void run() { B.lock(); A.lock(); A.unlock(); B.unlock(); }
  }
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new BA());
    t.start();
    A.lock(); B.lock(); B.unlock(); A.unlock();
    try { t.join(); } catch (InterruptedException e) { }
  }
}
