// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a timed await whose latch is already at zero
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The latch is counted down before await is reached -- main does it itself,
//   so no interleaving can change the order. `await` on a latch already at zero
//   returns true immediately without consulting the clock, so the assertion
//   holds under every schedule.
//
//   Paired with TimedAwaitCanExpire: together they pin that the timeout branch
//   is taken when it can be and not when it cannot. Modelling a timed await as
//   always succeeding passes this one and fails its partner; always expiring
//   does the reverse.
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
public class Main {
  public static void main(String[] args) throws Exception {
    final CountDownLatch latch = new CountDownLatch(1);
    Thread t = new Thread(new Runnable() {
      public void run() { int x = 1; }
    });
    t.start();
    latch.countDown();
    boolean ok = latch.await(1, TimeUnit.SECONDS);
    t.join();
    assert ok;
  }
}
