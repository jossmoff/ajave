// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a timed await that may expire
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   `await(long, TimeUnit)` returns false if the latch did not reach zero
//   before the timeout. Nothing here counts the latch down, so the call must
//   return false and the assertion fails.
//
//   The interesting half is that expiry is a *choice*, not a computation: the
//   JVM may return either outcome depending on timing, so an analysis that
//   cannot branch on it has to refuse. This benchmark is deliberately rigged so
//   only one outcome is possible, making the expected verdict unambiguous while
//   still requiring the branch to exist.
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
public class Main {
  public static void main(String[] args) throws Exception {
    final CountDownLatch latch = new CountDownLatch(1);
    Thread t = new Thread(new Runnable() {
      public void run() { int x = 1; }   // never counts down
    });
    t.start();
    boolean ok = latch.await(1, TimeUnit.SECONDS);
    t.join();
    assert ok;
  }
}
