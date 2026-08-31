// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: SemaphorePermitDeadlock
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   One permit, two acquires by the same thread and no release in between.
//   The second acquire blocks on a permit that only this thread could return,
//   so it blocks forever.
import java.util.concurrent.Semaphore;
public class Main {
  public static void main(String[] args) throws Exception {
    Semaphore s = new Semaphore(1);
    Thread t = new Thread(new Runnable() { public void run() { int x = 1; } });
    t.start();
    s.acquire();
    s.acquire();   // no permits left, and nobody will release one
    s.release();
  }
}
