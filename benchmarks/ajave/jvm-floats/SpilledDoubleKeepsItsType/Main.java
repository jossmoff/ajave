// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: SpilledDoubleKeepsItsType
// Expected: valid-assert=true, no-runtime-exception=true
//
// A double that reaches `dmul` from a different basic block must still be
// multiplied as a double.
//
// Ground truth (by construction, NOT by observation):
//   Both conditional expressions yield the same value on either arm, so the
//   product is 2.0 * 3.0 whatever `c` is. JLS 15.17.1 defines `*` on doubles
//   as IEEE-754 multiplication; 2.0, 3.0 and 6.0 are all exactly representable
//   and the product is exact, so `p == 6.0` holds. Confirmed on a real JVM for
//   both arms.
//
// What ajave did (found 2026-09-04, while triaging float-nonlinear-calculation):
//   The lifter models the operand stack with one `VarId` per stack depth,
//   allocated by `Lifter::stack_slot` — which hardcodes `Ty::Int` — and
//   `spill()` materialises the stack across a block boundary through temps
//   also hardcoded to `Ty::Int`. So a double that crosses a block boundary on
//   the stack is recorded in `body.vars` as an int.
//
//   Every consumer that asks the IR for an operand's type then gets the wrong
//   answer. `concrete::is_float_operand` consults it to choose between real
//   float arithmetic and the integer path, so `v * v` multiplied the two
//   *bit patterns* as i64 and reinterpreted the wrapped result as a double.
//   `smt_bmc::fp_width_of_operand` consults it to decide whether to emit an
//   `fp.mul`, so the BMC encoded the same multiply as a bitvector multiply.
//
//   Here that turns a true assertion into a proposed counterexample: the
//   verdict was never wrong, because JVM replay refuses the witness, but the
//   task is lost to UNKNOWN. The ternaries are the smallest way to force the
//   spill; in the corpus the same thing happens whenever both operands of an
//   arithmetic operation are results of calls, as in `Math.sin(y) *
//   Math.asin(x)`, because a call ends a block.
//
//   `smt_bmc` already carries a `var_widths` side table introduced for the
//   adjacent symptom (a 64-bit value in a slot declared 32-bit). That fixes
//   the width and cannot fix the type, since a bitvector width does not
//   distinguish a double from a long.
//
//   Typing the stack is necessary but not sufficient. The BMC's first pass
//   encodes float arithmetic as bitvector arithmetic by default
//   (AJAVE_FP_ARITH=0), so `2.0 * 3.0` is still a bitvector multiply of the
//   two bit patterns; it is the *taint* machinery that then knows the result
//   is meaningless, and taint only fires once `operand_is_float` can see that
//   the operands are doubles. So this task moves from "confidently wrong" to
//   "correctly refuses to answer" with the lifter fix alone, and needs the
//   FPA encoding to become TRUE.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    int c = Verifier.nondetInt();
    // The first operand stays on the operand stack while the second
    // conditional is evaluated, so it is spilled across a block boundary.
    double p = (c > 0 ? 2.0 : 2.0) * (c > 0 ? 3.0 : 3.0);
    assert p == 6.0;
  }
}
