// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ConsistentLockOrder
// Expected: valid-assert=true, no-runtime-exception=n/a
//
// Ground truth (by construction, NOT by observation):
//   Both threads acquire a before b, so no cycle in the wait-for graph is
//   possible and the program terminates. The assertion is on a value written
//   under the lock and read after join.

public class Main {

  static class Locks {
    final Object a = new Object();
    final Object b = new Object();
    int n = 0;
  }
  static class AB implements Runnable {
    final Locks l;
    AB(Locks l) { this.l = l; }
    public void run() {
      synchronized (l.a) {
        synchronized (l.b) { l.n++; }
      }
    }
  }
  public static void main(String[] args) throws Exception {
    Locks l = new Locks();
    Thread t = new Thread(new AB(l));
    t.start();
    synchronized (l.a) {
      synchronized (l.b) { l.n++; }
    }
    try { t.join(); } catch (InterruptedException e) { }
    assert l.n == 2;
  }
}
