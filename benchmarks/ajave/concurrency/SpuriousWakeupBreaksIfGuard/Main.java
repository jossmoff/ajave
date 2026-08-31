// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: spurious wakeup from Object.wait
// Expected: valid-assert=false
//
// Ground truth (by construction, from the JLS, NOT by observation):
//   JLS 17.2.1 permits wait() to return without any notify, interrupt or
//   timeout -- a *spurious wakeup*. This consumer guards its wait with `if`
//   rather than `while`, so a spurious return sends it past the guard with
//   count still 0. It then decrements to -1 and the assertion fails.
//
//   This is why the specification says a wait must always be inside a loop
//   that re-tests its condition. A real JVM will almost never show it, so the
//   verdict here is a property of the language, not of a run: an analysis that
//   models wait as "returns only when notified" reports this program safe.
public class Main {
  static final Object lock = new Object();
  static int count = 0;
  public static void main(String[] args) throws Exception {
    Thread producer = new Thread(new Runnable() {
      public void run() { synchronized (lock) { count++; lock.notifyAll(); } }
    });
    producer.start();
    synchronized (lock) {
      if (count == 0) {                     // `if`, not `while` -- the bug
        try { lock.wait(); } catch (InterruptedException e) { return; }
      }
      count--;
      assert count >= 0;
    }
    producer.join();
  }
}
