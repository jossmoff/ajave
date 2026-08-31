// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: semaphore-bounded resource pool
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The semaphore issues one permit, so at most one thread is inside the pool
//   at a time and `inUse` is never above 1. The assertion states that bound.
//   A pool that leaked a permit, or released without acquiring, would break it.
import java.util.concurrent.Semaphore;
public class Main {
  static final Semaphore permits = new Semaphore(1);
  static int inUse = 0;
  static int maxSeen = 0;
  static class Client implements Runnable {
    public void run() {
      try { permits.acquire(); } catch (InterruptedException e) { return; }
      inUse++;
      if (inUse > maxSeen) maxSeen = inUse;
      inUse--;
      permits.release();
    }
  }
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Client());
    t.start();
    new Client().run();
    t.join();
    assert maxSeen <= 1;
  }
}
