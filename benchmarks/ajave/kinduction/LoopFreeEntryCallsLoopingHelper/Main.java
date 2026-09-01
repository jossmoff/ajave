// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a loop-free entry method whose callee loops
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   `count(n)` returns n for n >= 0, so the assertion `count(n) < 10` fails
//   for every n in [10, 20], and `n` is an unconstrained input restricted to
//   [0, 20]. A violating execution therefore exists -- run it with n = 10.
//
// Why this benchmark exists (issue #76):
//   k-induction discharges an obligation when the BMC published
//   `Status::Bounded { k }` for it and the method is loop-free, reasoning that
//   the bounded search was then exhaustive. That test used to inspect only the
//   *entry* body. Here `main` is loop-free and the loop is one frame down in
//   `count`, where the BMC stops after MAX_LOOP_UNROLL = 5 iterations -- so
//   `Bounded` would be published precisely because the search was NOT
//   exhaustive, and treated as though it were.
//
//   Measured behaviour before the fix was UNKNOWN, not a wrong TRUE, and the
//   reason is worth recording because it is not a safeguard. The BMC cuts the
//   loop off and reports a *spurious* violation (witness n = 6, which does not
//   actually fail); JVM replay refutes it; but `Bounded` is only published
//   when a run finds no violation anywhere, so the spurious one suppresses it
//   and starves k-induction. The unsound discharge is guarded by an accident
//   of another engine's imprecision.
//
//   The fix makes loop-freeness transitive over the reachable call graph, so
//   this shape is declined on its own merits rather than by that accident.
//   The bound is what the benchmark is calibrated against: the assertion first
//   fails at ten iterations, comfortably past five.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  static int count(int n) {
    int x = 0;
    for (int i = 0; i < n; i++) {
      x = x + 1;
    }
    return x;
  }
  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    if (n < 0 || n > 20) return;
    assert count(n) < 10;
  }
}
