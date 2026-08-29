// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: RacyNullDeref
// Expected: valid-assert=n/a, no-runtime-exception=false
//
// Ground truth (by construction, NOT by observation):
//   The worker clears the reference while main dereferences it. An
//   interleaving exists where the write lands between main's null check and
//   its use, so NullPointerException is reachable. This is the shape a
//   concurrency engine must find and a sequential one cannot.

public class Main {

  static class Holder {
    String s = "abc";
  }
  static class Clear implements Runnable {
    final Holder h;
    Clear(Holder h) { this.h = h; }
    public void run() { h.s = null; }
  }
  public static void main(String[] args) throws Exception {
    Holder h = new Holder();
    Thread t = new Thread(new Clear(h));
    t.start();
    if (h.s != null) {
      h.s.length();
    }
    try { t.join(); } catch (InterruptedException e) { }
  }
}
