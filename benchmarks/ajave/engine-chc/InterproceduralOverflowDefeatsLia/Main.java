// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: CHC's inter-procedural encoding and 32-bit overflow
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   `inc(n)` is `n + 1` in Java's 32-bit wrapping arithmetic, so at
//   n = Integer.MAX_VALUE it is Integer.MIN_VALUE, which is not greater than n.
//   The assertion therefore fails for that one input, and `n` is an
//   unconstrained input, so a violating execution exists. Confirmed on a real
//   JVM with n = 2147483647.
//
// Why this benchmark exists (issue #77):
//   `x + 1 > x` is valid in linear integer arithmetic and false in Java.
//   `encode_chc_interproc` encodes method bodies in LIA over unbounded `Int`,
//   so it proves this assertion and would discharge it.
//
//   The engine's own comments state the argument that would make LIA sound
//   here -- route any operation leaving the 32-bit range to `error`, so that
//   proving `error` unreachable proves no-overflow and the property together.
//   `INT_MIN` and `INT_MAX` are declared for it. Neither constant is read
//   anywhere, and no such guard is emitted.
//
//   The call to `inc` is what selects the unsound path: `encode_chc_single`
//   encodes in bitvectors and gets this right, and it is used only when the
//   program has no resolvable calls. `prog_has_resolvable_calls` sends
//   anything inter-procedural to the LIA encoder instead.
//
//   This currently answers FALSE via the BMC, which finds the overflow easily.
//   CHC never sees the obligation because `bb.open()` only offers it what
//   earlier engines left open -- the gating is the only reason the wrong answer
//   is not emitted, which is the point of #77. As a canary: a TRUE here means
//   CHC has been unstarved without its encoding being fixed.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  static int inc(int x) {
    return x + 1;
  }
  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    assert inc(n) > n;
  }
}
