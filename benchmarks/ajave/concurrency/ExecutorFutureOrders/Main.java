// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: Future.get as a happens-before edge
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Future.get() returns only after the task has completed, and the
//   java.util.concurrent memory-consistency guarantees make everything the
//   task did visible to the thread that retrieves its result. So the read of
//   `x` after get() must see 42. Only one task exists, so nothing races.
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
public class Main {
  static int x = 0;
  static class Task implements Runnable {
    public void run() { x = 42; }
  }
  public static void main(String[] args) throws Exception {
    ExecutorService pool = Executors.newFixedThreadPool(1);
    Future<?> f = pool.submit(new Task());
    f.get();
    assert x == 42;
    pool.shutdown();
  }
}
