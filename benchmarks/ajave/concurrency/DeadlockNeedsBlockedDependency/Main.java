// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: DeadlockNeedsBlockedDependency
// Expected: no-deadlock=false
//
// Regression for a partial-order reduction that was unsound for deadlock
// (found 2026-08-31).
//
// Ground truth (by construction, NOT by observation):
//   Two threads take the same two monitors in opposite orders. An interleaving
//   exists where each holds one and waits for the other, so no thread can
//   proceed and neither has terminated. That is a deadlock.
//
// Why this is the shape that broke DPOR:
//   DPOR justifies its reduction by reasoning over *enabled* transitions -- two
//   independent enabled transitions commute, so one order stands for both. A
//   deadlock is the absence of enabled transitions, and the interleaving that
//   produces it is reached by threads *blocking* on each other. A blocking
//   transition carried no accesses, so no dependency was seen, so the backtrack
//   point that would have tried the other acquire order was never created.
//   DPOR explored 236 states here and reported no deadlock: a wrong TRUE.
//
//   Fixed by having a blocked acquire record the monitor it contended for, so
//   it is dependent with whoever holds or acquires the same monitor.
//
//   Minimal on purpose: two monitors, two threads, no shared data, no
//   assertions. Anything less cannot deadlock at all.
//
// Note on shape: the monitors are instance fields of a holder passed to the
// Runnable, not `static final` fields. The explorer returns UNKNOWN for the
// static form -- an unrelated gap in thread/monitor discovery, worth its own
// benchmark and fix.

public class Main {

  /** Holder for the two monitors, so both threads lock the same objects. */
  static class Locks {
    final Object a = new Object();
    final Object b = new Object();
  }

  /** Takes b then a -- the opposite order to main. */
  static class BA implements Runnable {
    final Locks l;
    BA(Locks l) { this.l = l; }
    public void run() {
      synchronized (l.b) {
        synchronized (l.a) { }
      }
    }
  }

  public static void main(String[] args) throws Exception {
    Locks l = new Locks();
    Thread t = new Thread(new BA(l));
    t.start();
    synchronized (l.a) {
      synchronized (l.b) { }
    }
    try { t.join(); } catch (InterruptedException e) { }
  }
}
