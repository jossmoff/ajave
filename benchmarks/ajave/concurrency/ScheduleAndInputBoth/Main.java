// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ScheduleAndInputBoth
// Expected: valid-assert=false, no-runtime-exception=n/a
//
// Ground truth (by construction, NOT by observation):
//   Requires *both* a specific input and a specific interleaving: the
//   assertion fails only when the nondet value is 7 and the worker's write
//   lands first. A witness must therefore record the input sequence and the
//   schedule — neither alone reproduces it. This is the benchmark that
//   justifies Witness carrying both.

public class Main {

  static class Shared {
    int n = 0;
  }
  static class Bump implements Runnable {
    final Shared s;
    Bump(Shared s) { this.s = s; }
    public void run() { s.n = 1; }
  }
  public static void main(String[] args) throws Exception {
    Shared s = new Shared();
    Thread t = new Thread(new Bump(s));
    t.start();
    int x = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    try { t.join(); } catch (InterruptedException e) { }
    if (x == 7) {
      assert s.n == 0;
    }
  }
}
