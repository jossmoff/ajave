// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ACastFromDoubleTruncatesTowardZero
// Expected: valid-assert=false, no-runtime-exception=true
//
// Ground truth (by construction, from JLS 5.1.3 and the JVMS, NOT by
// observation):
//
//   `d2i` rounds toward zero, so `(int) 3.7` is 3. The assertion is reached
//   and valid-assert is FALSE.
//
//   The encoding that gets this wrong is a width test. `lia_width(Ty::Float)`
//   is 32, so `LiaTheory::models_cast(Int, Float)` was `32 >= 32` -- "this is
//   a widening" -- and `encode_cast` returns a widening operand unchanged. The
//   LIA encoder therefore modelled `(int) d` as `i = d`, where `d` is a
//   double-typed variable holding a *bit pattern*. On that encoding `i == 3`
//   is false, the `assert false` looks unreachable, and an over-approximating
//   engine could publish a **wrong TRUE**: -32 points.
//
//   Casting between a float type and an integer type is not a width question
//   at all, and the fix says so: `models_cast` declines any cast touching a
//   float in either direction, and `Encoder::rvalue` havocs it before the
//   theory is consulted. See docs/proposals/lia-faithfulness.md §2.2.
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
// `d` is a non-final local, so `(int) d` is not a constant expression and
// javac emits `dload; d2i` rather than folding it to `iconst_3`. Without that
// the cast would never reach an engine.

public class Main {

  public static void main(String[] args) {
    double d = 3.7;
    int i = (int) d;
    // 3.7 truncates to 3, so this is reachable.
    if (i == 3) {
      assert false;
    }
  }
}
