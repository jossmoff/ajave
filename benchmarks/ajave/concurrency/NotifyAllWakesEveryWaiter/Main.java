// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: notifyAll removes the arbitrary choice
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   Identical to NotifyMayWakeWrongWaiter except every signal is notifyAll, so
//   which waiter the runtime would have picked stops mattering. Both wake, B
//   re-tests and waits again while A proceeds and sets `b`, and A's notifyAll
//   then releases B. No arbitrary choice can strand either.
//
//   The pair isolates the choice as the cause: an engine modelling notify as
//   waking an arbitrary waiter must report this TRUE and its partner FALSE.
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
          lock.notifyAll();
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
    synchronized (lock) { a = true; lock.notifyAll(); }
    ta.join();
    tb.join();
  }
}
