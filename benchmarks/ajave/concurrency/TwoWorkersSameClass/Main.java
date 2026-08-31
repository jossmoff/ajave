// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: two threads running the same Runnable class
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Each worker writes its own field, so there is no shared write and no race.
//   Both workers are joined before the assertion, so both writes are visible
//   and a+b is exactly 2 under every interleaving.
//
//   The point is multiplicity: the two threads run the *same* run() method.
//   An analysis that identifies threads by the method they run rather than by
//   the start() that spawned them sees one thread here, and then a+b is 1 and
//   the assertion appears to fail -- a wrong FALSE for a program with no bug.
public class Main {
  static int a = 0;
  static int b = 0;
  static class W implements Runnable {
    final boolean first;
    W(boolean f) { first = f; }
    public void run() { if (first) a = 1; else b = 1; }
  }
  public static void main(String[] args) throws Exception {
    Thread t1 = new Thread(new W(true));
    Thread t2 = new Thread(new W(false));
    t1.start(); t2.start();
    t1.join(); t2.join();
    assert a + b == 2;
  }
}
