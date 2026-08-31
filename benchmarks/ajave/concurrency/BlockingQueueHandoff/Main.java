// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ArrayBlockingQueue put/take handoff
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   One item is put and one is taken. If the consumer reaches take() first it
//   blocks on an empty queue, and the producer's put() then releases it; if the
//   producer goes first the item is already there. Neither order can stall,
//   because in every state where one party is blocked the other still has its
//   operation left to perform.
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
public class Main {
  public static void main(String[] args) throws Exception {
    final BlockingQueue<Object> q = new ArrayBlockingQueue<Object>(1);
    final Object item = new Object();
    Thread producer = new Thread(new Runnable() {
      public void run() {
        try { q.put(item); } catch (InterruptedException e) { }
      }
    });
    producer.start();
    q.take();
    producer.join();
  }
}
