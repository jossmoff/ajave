// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: k-induction must NOT prove a property that fails
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   x counts up without a guard, so the eleventh iteration evaluates
//   `assert 11 <= 10` and fails. The witness is any execution that takes the
//   loop at least eleven times.
//
//   This is the partner to the TRUE cases here, and it exists so that they
//   cannot all be passed by the same wrong mechanism. An engine that reported
//   TRUE by encoding a step case that does not actually generalise would
//   prove this one too; a real induction cannot, because the base case is
//   genuinely satisfiable at k = 11.
//
//   Note the base case must be checked to at least k = 11 to see it. That is
//   the BMC's job, not k-induction's -- the point here is that k-induction
//   stays silent rather than discharging.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int x = 0;
    while (Verifier.nondetBoolean()) {
      x = x + 1;
      assert x <= 10;
    }
  }
}
