// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: circular wait among three threads
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   Three philosophers, three forks, each taking its left fork then its right.
//   In the interleaving where all three take their left fork first, each holds
//   one fork and waits on one held by a neighbour: a three-node cycle in the
//   wait-for graph. Unlike the two-thread AB/BA case this needs a cycle longer
//   than two to be found, so it exercises the search rather than a pairwise
//   check.
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
    synchronized (f2) { synchronized (f0) { } }
    p0.join(); p1.join();
  }
}
