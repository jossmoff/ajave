// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: MissedSignalDeadlock
// Expected: no-deadlock=false
//
// Ground truth (by construction, and confirmed on a real JVM):
//   The signaller notifies before anyone is waiting, and a notify with no waiter
//   is simply lost -- it is not remembered. main then joins (so the notify has
//   definitely happened) and only then waits, so nothing will ever wake it: no
//   thread can proceed and not all have terminated. Verified: a real JVM hangs.
//
//   This is the classic missed-signal bug, and it is why waiting must always be
//   guarded by a loop on a condition rather than a bare wait().

public class Main {
  static class Holder { boolean ready = false; }
  static class Signaller implements Runnable {
    final Holder h;
    Signaller(Holder h) { this.h = h; }
    // Notifies, but nobody is waiting yet: the signal is lost.
    public void run() { synchronized (h) { h.notifyAll(); } }
  }
  public static void main(String[] args) throws Exception {
    Holder h = new Holder();
    Thread t = new Thread(new Signaller(h));
    t.start();
    try { t.join(); } catch (InterruptedException e) { }
    // The notify already happened, so this wait is never satisfied.
    synchronized (h) { h.wait(); }
  }
}
