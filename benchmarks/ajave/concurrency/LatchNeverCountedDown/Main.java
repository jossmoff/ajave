// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: LatchNeverCountedDown
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   The latch is created with count 1 and nobody ever calls countDown(), so
//   main blocks in await() forever while the worker terminates. No thread is
//   runnable and not all threads have finished: that is a deadlock.
import java.util.concurrent.CountDownLatch;
public class Main {
  public static void main(String[] args) throws Exception {
    final CountDownLatch latch = new CountDownLatch(1);
    Thread t = new Thread(new Runnable() {
      public void run() { int x = 1; }   // deliberately never counts down
    });
    t.start();
    latch.await();
  }
}
