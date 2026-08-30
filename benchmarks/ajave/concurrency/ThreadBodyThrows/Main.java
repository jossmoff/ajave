// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ThreadBodyThrows
// Expected: valid-assert=n/a, no-runtime-exception=false
//
// Ground truth (by construction, NOT by observation):
//   The Runnable dereferences null unconditionally. Whatever the schedule,
//   run() executes and raises NullPointerException. This is the defect that
//   motivated the whole plan: `Thread` was in PURE_OWNERS, so start() was
//   erased and the body never analysed, giving a wrong TRUE.

public class Main {

  static class Boom implements Runnable {
    public void run() {
      String s = null;
      s.length();
    }
  }
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Boom());
    t.start();
    try { t.join(); } catch (InterruptedException e) { }
  }
}
