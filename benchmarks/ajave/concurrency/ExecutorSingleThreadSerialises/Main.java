// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a pool with fewer workers than tasks
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   A single-threaded executor runs its tasks one after another on one worker,
//   so the two increments cannot interleave and n is exactly 2.
//
// KNOWN GAP -- this is expected to report UNKNOWN today, and that is the
// point of keeping it. The engine models a submitted task as its own thread
// and refuses when a pool has fewer workers than tasks, because pretending
// queued tasks run concurrently would invent the interleaving where both read
// 0 and report a race that cannot happen: a wrong FALSE, -32.
//
// So this benchmark guards the refusal. Unproven is the correct outcome until
// the work queue is modelled; a FALSE here means someone made the pool
// unsoundly concurrent, and the suite will say so.
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
public class Main {
  static int n = 0;
  static class Task implements Runnable {
    public void run() { n++; }
  }
  public static void main(String[] args) throws Exception {
    ExecutorService pool = Executors.newSingleThreadExecutor();
    pool.execute(new Task());
    pool.execute(new Task());
    pool.shutdown();
    pool.awaitTermination(1, java.util.concurrent.TimeUnit.SECONDS);
    assert n == 2;
  }
}
