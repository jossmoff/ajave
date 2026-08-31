// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: SemaphoreMutualExclusion
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   A binary semaphore serialises both increments, so they cannot interleave
//   and the counter is exactly 2 after both joins.
import java.util.concurrent.Semaphore;
public class Main {
  static class Box { int n = 0; }
  static class Inc implements Runnable {
    final Semaphore s; final Box b;
    Inc(Semaphore s, Box b) { this.s = s; this.b = b; }
    public void run() {
      try { s.acquire(); } catch (InterruptedException e) { return; }
      b.n++;
      s.release();
    }
  }
  public static void main(String[] args) throws Exception {
    Semaphore s = new Semaphore(1);
    Box b = new Box();
    Thread t = new Thread(new Inc(s, b));
    t.start();
    s.acquire(); b.n++; s.release();
    t.join();
    assert b.n == 2;
  }
}
