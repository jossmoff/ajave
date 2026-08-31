// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: input nondeterminism deciding whether a race exists
// Expected: valid-assert=false, no-data-race=false
//
// Ground truth (by construction, NOT by observation):
//   A boolean has exactly two values, and they lead to different programs. On
//   the guarded branch the increment is inside the monitor and the total is 2.
//   On the unguarded branch both threads read before either writes and the
//   total can be 1, so the assertion is violable and the accesses race.
//
//   Neither the schedule nor the input alone exposes this: the analysis has to
//   consider both values of the input *and* the interleavings each admits.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  static final Object lock = new Object();
  static int n = 0;
  static boolean guard;
  static class W implements Runnable {
    public void run() {
      if (guard) { synchronized (lock) { n = n + 1; } } else { n = n + 1; }
    }
  }
  public static void main(String[] args) throws Exception {
    guard = Verifier.nondetBoolean();
    Thread t = new Thread(new W());
    t.start();
    new W().run();
    t.join();
    assert n == 2;
  }
}
