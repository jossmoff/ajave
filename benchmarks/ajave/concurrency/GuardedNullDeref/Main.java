// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: GuardedNullDeref
// Expected: valid-assert=n/a, no-runtime-exception=true
//
// Ground truth (by construction, NOT by observation):
//   Same shape, but the check and the use are both inside a synchronized block
//   on the same monitor the writer uses, so no interleaving can place the
//   write between them.

public class Main {

  static class Holder {
    String s = "abc";
  }
  static class Clear implements Runnable {
    final Holder h;
    Clear(Holder h) { this.h = h; }
    public void run() { synchronized (h) { h.s = null; } }
  }
  public static void main(String[] args) throws Exception {
    Holder h = new Holder();
    Thread t = new Thread(new Clear(h));
    t.start();
    synchronized (h) {
      if (h.s != null) {
        h.s.length();
      }
    }
    try { t.join(); } catch (InterruptedException e) { }
  }
}
