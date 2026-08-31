// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: input nondeterminism deciding lock order
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   The worker takes A then B; main takes them in an order the input chooses.
//   When the input selects B-then-A the two orders are opposed and the
//   interleaving where each holds its first lock deadlocks. When it selects
//   A-then-B both agree and nothing can block.
//
//   So the deadlock exists for one input value under one interleaving. Fixing
//   the input hides it, and fixing the schedule hides it; only their product
//   finds it.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  static final Object A = new Object();
  static final Object B = new Object();
  static class W implements Runnable {
    public void run() { synchronized (A) { synchronized (B) { } } }
  }
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new W());
    t.start();
    if (Verifier.nondetBoolean()) {
      synchronized (B) { synchronized (A) { } }   // opposed order
    } else {
      synchronized (A) { synchronized (B) { } }   // same order
    }
    t.join();
  }
}
