// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a thread body written as a lambda
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The worker sets n=1 and is joined before the read, so n is 1. Identical in
//   substance to ThreadSubclassRuns; the only difference is how the Runnable is
//   written.
//
//   That difference was total. `new Thread(() -> ...)` compiles to an
//   invokedynamic, and the lifter havoced its result, so the Runnable was a
//   reference with no class and the thread's body could not be resolved. Every
//   benchmark in this suite used an anonymous inner class, which is exactly why
//   the gap went unnoticed -- this is how the code under test is actually
//   written today.
public class Main {
  static int n = 0;
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(() -> { n = 1; });
    t.start();
    t.join();
    assert n == 1;
  }
}
