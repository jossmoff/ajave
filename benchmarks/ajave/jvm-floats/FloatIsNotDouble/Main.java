// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: FloatIsNotDouble
// Expected: valid-assert=false, no-runtime-exception=true
//
// A `float` operation is not a `double` operation. The interval AI models both
// in `f64` — `interval.rs` routes `Ty::Float | Ty::Double` into one
// `FloatInterval` over `f64`, and contains no `as f32` anywhere — so its
// arithmetic is *more precise* than the JVM's, and a more precise model of a
// value can exclude the value the JVM actually produces.
//
// Ground truth (by construction, from IEEE-754 and the JVMS, NOT by
// observation):
//
//   `float` has a 24-bit significand, so the spacing of representable values
//   just above 1.0f is 2^-23 ≈ 1.1920929e-7. The JVMS specifies `fadd` as
//   IEEE-754 binary32 addition with round-to-nearest-even. 1.0e-8f is far
//   below half that spacing, so
//
//       fadd(1.0f, 1.0e-8f) == 1.0f          exactly
//
//   and therefore `sum > 1.0f` is FALSE and the assertion fires.
//
//   In binary64 the spacing above 1.0 is 2^-52 ≈ 2.2e-16, so 1.0e-8 is
//   comfortably representable as an increment:
//
//       dadd(1.0, 1.0e-8) == 1.00000001      > 1.0
//
//   An analysis that evaluates the `float` add in `f64` therefore computes the
//   point interval [1.00000001, 1.00000001], concludes `sum > 1.0f` holds, and
//   discharges the assertion — a wrong TRUE. The JVM violates it.
//
// Why this matters beyond the arithmetic: `ai.rs` publishes `Discharged`
// through `Blackboard::publish`, which hardcodes `Approximations::EXACT`. So
// the one mechanism that would hand this obligation back to a more faithful
// engine — `open_for(FLOAT_ARITH)`, consumed by the BMC's FPA pass — is told
// there is nothing to reconsider.
//
// `value` is read from the Verifier rather than written as a literal so that
// constant folding in javac or in ajave's own IR optimiser cannot evaluate the
// expression at compile time and sidestep the question.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    float one = Verifier.nondetFloat();
    // Pin `one` to exactly 1.0f without writing the sum as a constant.
    if (one != 1.0f) {
      return;
    }

    float tiny = 1.0e-8f;
    float sum = one + tiny;

    // False on any real JVM: the increment is below half the gap between
    // consecutive floats at 1.0f, so `sum` is bit-identical to `one`.
    assert sum > 1.0f;
  }
}
