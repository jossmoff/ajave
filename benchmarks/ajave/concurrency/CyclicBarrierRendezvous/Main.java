// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: CyclicBarrierRendezvous
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The worker writes b.n=5 before its await(); main reads b.n only after its
//   own await() returns. A barrier orders everything before a party's await
//   before everything after the barrier trips, so the read must see 5.
import java.util.concurrent.CyclicBarrier;
public class Main {
  static class Box { int n = 0; }
  public static void main(String[] args) throws Exception {
    final CyclicBarrier barrier = new CyclicBarrier(2);
    final Box b = new Box();
    Thread t = new Thread(new Runnable() {
      public void run() {
        b.n = 5;
        try { barrier.await(); } catch (Exception e) { }
      }
    });
    t.start();
    barrier.await();
    assert b.n == 5;
  }
}
