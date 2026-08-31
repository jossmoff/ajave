// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: Thread.isAlive after join, and Thread.yield as a no-op
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   join() returns only once the thread has terminated, so isAlive() is false
//   afterwards and the worker's write is visible. yield() only offers the
//   scheduler a switch and changes no value, so it cannot affect either.
public class Main {
  static int n = 0;
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() { Thread.yield(); n = 1; }
    });
    t.start();
    t.join();
    assert !t.isAlive() && n == 1;
  }
}
