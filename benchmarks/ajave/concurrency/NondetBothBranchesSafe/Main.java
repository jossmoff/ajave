// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: an input that varies the code but not its safety
// Expected: valid-assert=true, no-data-race=true
//
// Ground truth (by construction, NOT by observation):
//   Both branches increment inside the same monitor, so the total is 2
//   whichever value the input takes and no access is unsynchronised.
//
//   The companion to NondetPicksRacingBranch, and the one that needs
//   *completeness*: proving this requires visiting both values of the input.
//   An analysis that explored only one would report TRUE having checked half
//   the program, which is right here by luck and wrong on its partner.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  static final Object lock = new Object();
  static int n = 0;
  static boolean which;
  static class W implements Runnable {
    public void run() {
      if (which) { synchronized (lock) { n = n + 1; } }
      else { synchronized (lock) { n = n + 1; } }
    }
  }
  public static void main(String[] args) throws Exception {
    which = Verifier.nondetBoolean();
    Thread t = new Thread(new W());
    t.start();
    new W().run();
    t.join();
    assert n == 2;
  }
}
