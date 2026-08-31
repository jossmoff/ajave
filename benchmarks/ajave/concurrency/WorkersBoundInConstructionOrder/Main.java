// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: thread identity when construction order differs from
// the alphabetical order of the run() methods
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Zebra sets z=1, Alpha sets p=2, both are joined, so z+p is 3.
//
//   Zebra is constructed first but sorts last. An analysis that assigns thread
//   identities in construction order while listing thread bodies in sorted
//   order pairs each thread with the other one's body, so the two writes land
//   in the wrong variables. The values differ (1 and 2) precisely so that
//   swapping them is observable rather than silently harmless.
public class Main {
  static int z = 0;
  static int p = 0;
  static class Zebra implements Runnable { public void run() { z = 1; } }
  static class Alpha implements Runnable { public void run() { p = 2; } }
  public static void main(String[] args) throws Exception {
    Thread t1 = new Thread(new Zebra());
    Thread t2 = new Thread(new Alpha());
    t1.start(); t2.start();
    t1.join(); t2.join();
    assert z + p == 3;
  }
}
