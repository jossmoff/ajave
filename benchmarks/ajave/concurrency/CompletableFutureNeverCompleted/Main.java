// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: get() on a future nobody completes
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   Nothing ever calls complete(), so get() blocks forever while the worker
//   terminates. No thread is runnable and not all have finished: a deadlock,
//   and one that occurs under every schedule.
public class Main {
  static final java.util.concurrent.CompletableFuture<Object> f =
      new java.util.concurrent.CompletableFuture<Object>();
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() { public void run() { int q = 1; } });
    t.start();
    f.get();
  }
}
