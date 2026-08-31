// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: StaticMonitorLockOrder
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   The same AB/BA lock-order inversion as LockOrderInversion, but the monitors
//   are `static final` fields rather than instance fields of a holder. An
//   interleaving exists where each thread holds one lock and waits for the
//   other, so this deadlocks.
//
// Why this shape needed its own fix:
//   The explorer identifies objects by allocation site and traces a monitor
//   operand back to a `new`. A static load traced to neither an allocation nor
//   an instance field, so every program locking a static was refused outright --
//   and `static final Object LOCK = new Object()` is the commonest lock idiom
//   in Java.
//
//   Resolving the trace alone then produced a *wrong TRUE*: `<clinit>` is not
//   executed by the explorer, so an uninitialised static reference reads as
//   null, both locks denoted the same object, and the deadlock became
//   unrepresentable. Statics initialised from a visible `new` in `<clinit>` are
//   now seeded with distinct identities.

public class Main {

  static final Object A = new Object();
  static final Object B = new Object();

  /** Takes B then A -- the opposite order to main. */
  static class BA implements Runnable {
    public void run() {
      synchronized (B) {
        synchronized (A) { }
      }
    }
  }

  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new BA());
    t.start();
    synchronized (A) {
      synchronized (B) { }
    }
    try { t.join(); } catch (InterruptedException e) { }
  }
}
