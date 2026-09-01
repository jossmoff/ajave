// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a loop invariant that no bounded unrolling establishes
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   `x` starts at 0 and the loop adds 2 each time, so x is even at every
//   point where the assertion is evaluated. Evenness is preserved by the
//   loop body (even + 2 is even) and holds initially, which is an induction
//   proof -- the invariant is inductive as written, needing no strengthening.
//
//   The bound is nondeterministic and unconstrained above, so no finite
//   unrolling covers every execution. A BMC can only report `Bounded { k }`.
//   Discharging this requires the step case to actually be a step case.
//
// Paired with LoopFailsOnSecondIteration so that the two cannot be passed by
// the same wrong mechanism: a 1-unrolling proves this one for the wrong
// reason and its partner not at all, while a real inductive step separates
// them.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    if (n < 0) return;
    int x = 0;
    for (int i = 0; i < n; i++) {
      x = x + 2;
      assert x % 2 == 0;
    }
  }
}
