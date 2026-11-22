// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ADoubleComparisonIsNotAnIntegerComparisonOfBitPatterns
// Expected: valid-assert=false, no-runtime-exception=true
//
// Ground truth (by construction, from IEEE-754 and the JVMS, NOT by
// observation):
//
//   -2.0 < -1.0, so the assertion is reached and valid-assert is FALSE.
//
//   The interesting part is the encoding that gets this wrong. IEEE-754 lays
//   out a double's sign in the top bit, so for two *negative* doubles the one
//   with the larger magnitude has the larger bit pattern read as unsigned --
//   and read as a signed 64-bit integer the order flips:
//
//     bits(-2.0) = 0xC000000000000000 = -4611686018427387904
//     bits(-1.0) = 0xBFF0000000000000 = -4616189618054758400
//
//   so bits(-2.0) > bits(-1.0) while -2.0 < -1.0.
//
//   `smt_text`'s `Encoder::rvalue` used to encode `Rvalue::Cmp` with
//   `encode_cmp` unconditionally, i.e. `(ite (< l r) -1 ...)` over whatever
//   integers the operands happened to be -- and a double-typed variable in the
//   LIA encoding *is* its bit pattern. On that encoding `a < b` is false, the
//   `assert false` looks unreachable, and an over-approximating engine
//   (`imc`, `cegar`, or `houdini`'s preservation check) could publish a
//   **wrong TRUE** on a program that really fails: -32 points.
//
//   `CmpKind` distinguishes `lcmp` (`Long`) from `fcmpl`/`fcmpg`/`dcmpl`/
//   `dcmpg` (`FloatL`/`FloatG`), so the fix reads the kind the lifter already
//   recorded and havocs the result. See docs/proposals/lia-faithfulness.md
//   §2.2, and Monniaux, "The pitfalls of verifying floating-point
//   computations", TOPLAS 2008.
//
// Status: this task is **already correct on c5d78d8**, the commit before this
// work, so it is a canary and not a demonstration of a gain. Measured, not
// assumed: both verdicts were run on a base-commit build before this header
// was written.
//
// The reason is the one CLAUDE.md records under "unsoundness masked by an
// unrelated conservative gate". The defect above is in the **LIA** encoder,
// and the engines that actually answer this task are not its consumers: the
// bitvector BMC decides it directly, and the interval domain carries a real
// float domain (`FloatInterval`) rather than a bit pattern. Of the LIA
// consumers, `imc` does not run at all without `AJAVE_SMTINTERPOL_JAR` (z3
// removed interpolation upstream; changes.md:7255), which leaves `cegar`,
// `invariant_check` and `houdini`. Ablating the answering engines leaves this
// UNKNOWN on both builds rather than wrong on the base one.
//
// So the value here is the canary's: "removing a gate does not create these;
// it reveals them". If the BMC is ever starved on a body like this, or an LIA
// engine is unstarved onto one, a wrong answer appears -- and it appears here
// first, with the mechanism written down.
//
// `a` and `b` are non-final locals, so `a < b` is not a constant expression
// and javac emits `dcmpg; ifge` rather than folding it away. That is the point
// of the benchmark: the comparison has to reach an engine.

public class Main {

  public static void main(String[] args) {
    double a = -2.0;
    double b = -1.0;
    // True in IEEE-754. False if the two bit patterns are compared as signed
    // integers, which is how this used to be encoded.
    if (a < b) {
      assert false;
    }
  }
}
