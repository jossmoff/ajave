// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ALowerBoundSurvivesOnlyIfTheIncrementIsBounded
// Expected: valid-assert=true, no-runtime-exception=true
//
// Ground truth (by construction, from JLS 15.18.2, NOT by observation):
//
//   `i` starts at 0 and is incremented only while `i < n`, so `i <= n` always
//   and `i + 1 <= n <= Integer.MAX_VALUE`: the increment never overflows and
//   `0 <= i` holds throughout. The assertion holds.
//
// What this pins -- a *boundary*, not only a capability:
//
//   `0 <= i` is a true invariant whose inductiveness depends on a **relation**
//   between two variables. Proving it needs `i < n` at the loop body, because
//   without it `i = Integer.MAX_VALUE` satisfies `0 <= i`, `i++` wraps
//   negative, and `{header: 0 <= i}` is not an inductive map of the *Java*
//   program -- only of its unbounded-integer shadow.
//
//   Before guarded preservation the LIA encoder accepted exactly that shadow:
//   `0 <= sum` was "preserved" by `sum = sum + 2`, which is how
//   `algorithms/BellmanFord-FunUnsat01` became a wrong TRUE on a program that
//   throws. `LiaEncoding::preservation_query` now carries the block's overflow
//   condition as a second disjunct of the transition, with an unconstrained
//   post-state -- overflow modelled as the exceptional edge it is.
//
//   The cost lands here. Houdini finds only *conjunctions* of candidates, and
//   a conjunction of unary bounds cannot say "the increment is bounded", so
//   this task is provable only when `i < n` is itself in the candidate pool.
//   An implication candidate (`i < n => i + 1 <= n`, after Lahiri & Qadeer's
//   clausal predicate abstraction) expresses it directly, and that is the next
//   widening rather than a bigger pool. See
//   docs/proposals/lia-faithfulness.md §7.
//
//   So an UNKNOWN here is honest and a TRUE is a real gain -- the shape
//   CLAUDE.md asks a boundary canary to have.
//
// Status: **already TRUE on c5d78d8**, the commit before this work. Measured,
// not assumed. The BMC unrolls and the interval domain widens, so neither
// needs the invariant this task is named for; the boundary being pinned is
// Houdini's, which cannot express "the increment is bounded" as a conjunction
// of unary candidates. The canary's job is therefore to *stay* TRUE while
// guarded preservation makes the synthesis path stricter -- a regression here
// would mean the guard had leaked out of the LIA path into an engine that was
// answering correctly without it.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    Verifier.assume(n >= 0);

    int i = 0;
    while (i < n) {
      i++;
    }
    // i == n >= 0 on exit, and the increment never wrapped getting here.
    assert i >= 0;
  }
}
