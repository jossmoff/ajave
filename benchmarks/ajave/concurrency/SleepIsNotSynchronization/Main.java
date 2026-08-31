// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: Thread.sleep does not order anything
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   Sleeping establishes no happens-before edge with anything. The JLS gives
//   sleep no memory-model meaning at all: it is a hint to the scheduler about
//   when this thread wishes to run again. So the schedule where the worker has
//   not yet run when main wakes is permitted, and the assertion fails.
//
//   A real JVM almost always makes this pass, which is exactly what makes it
//   dangerous -- "add a sleep until it works" is a bug, not a fix. The verdict
//   here is structural, not observed: an engine that treated sleep as an
//   ordering edge would call this program safe.
public class Main {
  static boolean flag = false;
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() { flag = true; }
    });
    t.start();
    Thread.sleep(50);
    assert flag;
  }
}
