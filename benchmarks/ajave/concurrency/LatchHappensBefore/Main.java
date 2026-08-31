// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: LatchHappensBefore
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The worker writes b.n=7 and then counts the latch down; main only reads
//   b.n after await() returns. CountDownLatch establishes happens-before
//   between the countDown and the return from await (JLS 17.4.5 via the
//   java.util.concurrent memory-consistency guarantees), so the read cannot
//   see the initial 0.
import java.util.concurrent.CountDownLatch;
public class Main {
  static class Box { int n = 0; }
  public static void main(String[] args) throws Exception {
    final CountDownLatch latch = new CountDownLatch(1);
    final Box b = new Box();
    Thread t = new Thread(new Runnable() {
      public void run() { b.n = 7; latch.countDown(); }
    });
    t.start();
    latch.await();
    assert b.n == 7;
  }
}
