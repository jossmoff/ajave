// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: an input that varies the path but preserves lock order
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   Both branches take A before B, as the worker does. A cycle in the wait-for
//   graph needs two threads acquiring in opposite orders, and no input value
//   produces one. Proving it requires visiting both branches.
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
      synchronized (A) { synchronized (B) { int x = 1; } }
    } else {
      synchronized (A) { synchronized (B) { int y = 2; } }
    }
    t.join();
  }
}
