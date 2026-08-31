// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: breaking the circular wait by reversing one thread
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   Identical to DiningPhilosophers except the last philosopher takes its
//   forks in the opposite order, so every thread acquires in a single global
//   order f0 < f1 < f2. Dijkstra's asymmetry fix: one right-handed
//   philosopher removes the cycle, and without a cycle there is no deadlock.
public class Main {
  static final Object f0 = new Object();
  static final Object f1 = new Object();
  static final Object f2 = new Object();
  static class Phil implements Runnable {
    final Object left, right;
    Phil(Object l, Object r) { left = l; right = r; }
    public void run() {
      synchronized (left) { synchronized (right) { } }
    }
  }
  public static void main(String[] args) throws Exception {
    Thread p0 = new Thread(new Phil(f0, f1));
    Thread p1 = new Thread(new Phil(f1, f2));
    p0.start(); p1.start();
    synchronized (f0) { synchronized (f2) { } }   // reversed: breaks the cycle
    p0.join(); p1.join();
  }
}
