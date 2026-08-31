// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a Thread returned from another method
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The worker sets n=5 and is joined before the read.
//
//   The construction happens in `make()`, so in `main` the thread traces to a
//   call result rather than to an allocation. Resolving the body from the
//   object at start() makes where it was built irrelevant.
public class Main {
  static int n = 0;
  static class W implements Runnable {
    public void run() { n = 5; }
  }
  static Thread make() { return new Thread(new W()); }
  public static void main(String[] args) throws Exception {
    Thread t = make();
    t.start();
    t.join();
    assert n == 5;
  }
}
