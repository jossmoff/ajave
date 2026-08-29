// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ThreadBodySafe
// Expected: valid-assert=n/a, no-runtime-exception=true
//
// Ground truth (by construction, NOT by observation):
//   run() performs only local arithmetic on a local variable. No shared state,
//   no partial function, no schedule can make it throw.

public class Main {

  static class Quiet implements Runnable {
    public void run() {
      int x = 0;
      for (int i = 0; i < 3; i++) x += i;
    }
  }
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Quiet());
    t.start();
    try { t.join(); } catch (InterruptedException e) { }
  }
}
