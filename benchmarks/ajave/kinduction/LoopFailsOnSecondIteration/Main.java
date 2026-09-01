// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a looped property that survives one unrolling
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   `x` is 1 on the first iteration and 2 on the second. The assertion demands
//   x < 2, so it holds on iteration 1 and fails on iteration 2. The loop runs
//   three times unconditionally, so the failure is reachable on every
//   execution -- there is no input for which this program passes.
//
// Why this benchmark exists (issue #76):
//   `smt_encode::encode_body` walks blocks in ID order and processes each one
//   once, so a back-edge merges into a header that has already been visited
//   and is silently dropped. The resulting formula describes exactly ONE pass
//   through the loop. On that single pass x == 1 and the assertion holds, so
//   the violation term is UNSAT.
//
//   k-induction's `try_step_case` reported that UNSAT as a proof. It is not
//   one: it is a 1-unrolling. This program is the smallest thing that tells
//   the two apart -- any engine answering TRUE here is reporting a bounded
//   check as an inductive argument.
//
//   The bug is latent in the shipped configuration because `Status::Bounded`
//   is published only when a run finds no violations anywhere, so k-induction
//   is starved of base cases and never runs on programs like this one. The
//   Rust test `step_case_rejects_property_that_fails_after_one_unrolling` in
//   `kinduction.rs` exercises the same shape directly, without depending on
//   that gating.
public class Main {
  public static void main(String[] args) {
    int x = 0;
    for (int i = 0; i < 3; i++) {
      x = x + 1;
      assert x < 2;
    }
  }
}
