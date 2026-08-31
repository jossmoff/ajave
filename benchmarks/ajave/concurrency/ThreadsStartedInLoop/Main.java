// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: threads constructed inside a loop
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Each iteration starts a worker and joins it before the next begins, so the
//   two increments are strictly ordered and total is 2.
//
//   One construction *site* produces two threads at run time. An analysis that
//   allocates one thread identity per site has state for only the first, and
//   the second start() has nowhere to go.
public class Main {
  static int total = 0;
  static class W implements Runnable {
    public void run() { total = total + 1; }
  }
  public static void main(String[] args) throws Exception {
    for (int i = 0; i < 2; i++) {
      Thread t = new Thread(new W());
      t.start();
      t.join();
    }
    assert total == 2;
  }
}
