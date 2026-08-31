// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: CompletableFuture.get as a happens-before edge
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   get() returns only once the future has been completed, and everything the
//   completing thread did beforehand is visible to the thread that retrieves
//   the result. So the read of `x` after get() must see 9.
public class Main {
  static int x = 0;
  static final java.util.concurrent.CompletableFuture<Object> f =
      new java.util.concurrent.CompletableFuture<Object>();
  static final Object DONE = new Object();
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() { x = 9; f.complete(DONE); }
    });
    t.start();
    f.get();
    assert x == 9;
    t.join();
  }
}
