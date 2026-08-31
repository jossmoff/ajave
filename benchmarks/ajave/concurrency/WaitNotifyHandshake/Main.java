// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: WaitNotifyHandshake
// Expected: no-deadlock=true
//
// Ground truth (by construction, and confirmed on a real JVM):
//   The waiter loops on a condition and waits; the signaller sets the flag and
//   notifies while holding the same monitor. The wait is satisfied, both
//   threads run to completion, and the program terminates. Verified: a real JVM
//   exits cleanly.

public class Main {
  static class Holder { boolean ready = false; }
  static class Signaller implements Runnable {
    final Holder h;
    Signaller(Holder h) { this.h = h; }
    public void run() {
      synchronized (h) { h.ready = true; h.notifyAll(); }
    }
  }
  public static void main(String[] args) throws Exception {
    Holder h = new Holder();
    Thread t = new Thread(new Signaller(h));
    t.start();
    synchronized (h) {
      while (!h.ready) { h.wait(); }
    }
    try { t.join(); } catch (InterruptedException e) { }
  }
}
