// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: take() on a queue nobody fills
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   Nothing is ever put into the queue, so take() blocks forever while the
//   worker terminates. No thread is runnable and not every thread has
//   finished: a deadlock. Unlike the handoff, this one stalls under every
//   schedule, so a real JVM hangs too.
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
public class Main {
  public static void main(String[] args) throws Exception {
    final BlockingQueue<Object> q = new ArrayBlockingQueue<Object>(1);
    Thread t = new Thread(new Runnable() {
      public void run() { int x = 1; }   // deliberately never produces
    });
    t.start();
    q.take();
  }
}
