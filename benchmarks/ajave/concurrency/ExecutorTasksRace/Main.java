// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: tasks submitted to a thread pool race like any threads
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   The pool has two workers and two tasks, so both can run at once. `n++` is
//   a read, an add and a write, and the interleaving where both tasks read 0
//   before either writes leaves n at 1. The assertion demands 2.
//
//   Submitting to an executor hides the start() but changes nothing about the
//   race, which is the point: an analysis that only recognises Thread.start()
//   sees no threads here and calls the program sequential.
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
public class Main {
  static int n = 0;
  static class Task implements Runnable {
    public void run() { n++; }
  }
  public static void main(String[] args) throws Exception {
    ExecutorService pool = Executors.newFixedThreadPool(2);
    pool.execute(new Task());
    pool.execute(new Task());
    pool.shutdown();
    pool.awaitTermination(1, java.util.concurrent.TimeUnit.SECONDS);
    assert n == 2;
  }
}
