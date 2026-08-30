// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: VolatileVisibility
// Expected: valid-assert=n/a, no-runtime-exception=true
//
// Ground truth (by construction, NOT by observation):
//   A volatile write happens-before every subsequent volatile read of the same
//   field (JLS 17.4.4), so the reader either sees 0 or 1 and never a torn
//   value. No read here can throw regardless.

public class Main {

  static class Flag {
    volatile int ready = 0;
  }
  static class Setter implements Runnable {
    final Flag f;
    Setter(Flag f) { this.f = f; }
    public void run() { f.ready = 1; }
  }
  public static void main(String[] args) throws Exception {
    Flag f = new Flag();
    Thread t = new Thread(new Setter(f));
    t.start();
    int seen = f.ready;
    try { t.join(); } catch (InterruptedException e) { }
    assert seen == 0 || seen == 1;
  }
}
