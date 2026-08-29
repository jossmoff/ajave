// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: MutualExclusionHolds
// Expected: valid-assert=true, no-runtime-exception=n/a
//
// Ground truth (by construction, NOT by observation):
//   Both threads increment under the same lock, so at most one is inside the
//   critical section. The invariant `flag == 0` on entry cannot be observed
//   broken.

public class Main {

  static class Guard {
    int flag = 0;
    int violations = 0;
    synchronized void enter() {
      if (flag != 0) violations++;
      flag = 1;
      flag = 0;
    }
  }
  static class Enter implements Runnable {
    final Guard g;
    Enter(Guard g) { this.g = g; }
    public void run() { g.enter(); }
  }
  public static void main(String[] args) throws Exception {
    Guard g = new Guard();
    Thread t = new Thread(new Enter(g));
    t.start();
    g.enter();
    try { t.join(); } catch (InterruptedException e) { }
    assert g.violations == 0;
  }
}
