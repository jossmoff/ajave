// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: LockOrderInversion
// Expected: valid-assert=n/a, no-runtime-exception=n/a
//
// Ground truth (by construction, NOT by observation):
//   Classic AB/BA deadlock: main takes a then b, the other thread takes b then
//   a. An interleaving exists where each holds one and waits for the other.
//   Neither valid-assert nor no-runtime-exception is violated by a deadlock —
//   the program hangs rather than failing — so both properties are omitted and
//   this benchmark exists for the no-deadlock property, which SV-COMP defines
//   but no Java category uses.

public class Main {

  static class Locks {
    final Object a = new Object();
    final Object b = new Object();
  }
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
