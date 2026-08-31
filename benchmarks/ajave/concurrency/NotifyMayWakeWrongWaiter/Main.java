// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: notify() wakes ONE waiter, chosen arbitrarily
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   Two threads wait on one monitor for different conditions. Main satisfies
//   only `a` and calls notify(), which wakes exactly one waiter and the JLS
//   does not say which.
//
//   Wake A: it proceeds, sets `b`, notifies, and B follows. Everything ends.
//   Wake B: its condition is still false so it waits again -- and the notify
//   is spent. A is never woken, and main blocks in join() forever.
//
//   So the deadlock exists for one of two arbitrary outcomes. This is the
//   textbook reason to prefer notifyAll, and an engine that always wakes the
//   same waiter reports the program safe or broken depending on which one it
//   happens to pick, rather than on the program.
public class Main {
  static final Object lock = new Object();
  static boolean a = false;
  static boolean b = false;
  public static void main(String[] args) throws Exception {
    Thread ta = new Thread(new Runnable() {
      public void run() {
        synchronized (lock) {
          while (!a) { try { lock.wait(); } catch (InterruptedException e) { return; } }
          b = true;
          lock.notify();
        }
      }
    });
    Thread tb = new Thread(new Runnable() {
      public void run() {
        synchronized (lock) {
          while (!b) { try { lock.wait(); } catch (InterruptedException e) { return; } }
        }
      }
    });
    ta.start();
    tb.start();
    synchronized (lock) { a = true; lock.notify(); }
    ta.join();
    tb.join();
  }
}
