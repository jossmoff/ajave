// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: interrupting a thread parked in wait()
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   Nothing ever notifies the lock, so the worker's wait() is released only by
//   the interrupt. Both orders terminate: if main interrupts first the flag is
//   already set and wait() throws immediately, and if the worker parks first
//   the interrupt wakes it. Either way it throws InterruptedException, catches
//   it, and exits, so main's join returns.
//
//   Without interrupt delivery this is a deadlock -- a thread parked forever on
//   a monitor nobody notifies. Modelling interrupt as "set a flag" would
//   therefore report a hang the program recovers from, which is why it was
//   refused rather than approximated.
public class Main {
  static final Object lock = new Object();
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() {
        synchronized (lock) {
          try { lock.wait(); } catch (InterruptedException e) { }
        }
      }
    });
    t.start();
    t.interrupt();
    t.join();
  }
}
