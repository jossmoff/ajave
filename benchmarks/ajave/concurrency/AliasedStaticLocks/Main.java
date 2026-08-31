// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: two static lock fields that alias the same object
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   B is assigned from A, so A == B: there is exactly one lock object. The two
//   threads take it in opposite "orders", but a second acquisition of a lock
//   you already hold is reentrant, so neither can block. An AB/BA cycle needs
//   two distinct locks and there are not two here.
//
//   This is the shape that catches an aliasing bug in the other direction from
//   the usual one. Treating two names for one object as two objects invents a
//   deadlock the JVM cannot have -- a wrong FALSE, the most expensive verdict
//   in the scoring.
public class Main {
  static final Object A = new Object();
  static final Object B = A;
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() {
        synchronized (B) { synchronized (A) { } }
      }
    });
    t.start();
    synchronized (A) { synchronized (B) { } }
    t.join();
  }
}
