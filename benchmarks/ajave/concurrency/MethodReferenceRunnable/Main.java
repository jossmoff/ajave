// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a thread body written as a method reference
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   `Main::work` sets n=3, and the thread is joined before the read.
//
//   A method reference is the same invokedynamic mechanism as a lambda, with
//   the implementation being an existing method rather than a synthesised one.
public class Main {
  static int n = 0;
  static void work() { n = 3; }
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(Main::work);
    t.start();
    t.join();
    assert n == 3;
  }
}
