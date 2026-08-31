// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: CyclicBarrierMissingParty
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   The barrier is built for three parties but only two ever arrive, so both
//   block permanently waiting for a third that does not exist.
import java.util.concurrent.CyclicBarrier;
public class Main {
  public static void main(String[] args) throws Exception {
    final CyclicBarrier barrier = new CyclicBarrier(3);
    Thread t = new Thread(new Runnable() {
      public void run() { try { barrier.await(); } catch (Exception e) { } }
    });
    t.start();
    barrier.await();
  }
}
