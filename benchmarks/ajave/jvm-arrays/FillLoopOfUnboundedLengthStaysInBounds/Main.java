// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: relating a loop index to an array length
// Expected: no-runtime-exception=true, valid-assert=true
//
// Six lines, and ajave cannot prove it. The smallest program that isolates
// what blocks the `ArrayBounds` obligations — 195 of them, 48% of all open
// obligations alongside `NullDeref`.
//
// Ground truth (by construction):
//   `a` is created with length `n`, and the loop guard is `i < n`. So at the
//   store, 0 <= i < n = a.length. Every access is in bounds on every
//   execution, for every n > 0. No runtime exception is possible.
//
// What ajave does, and why it is not a budget problem:
//   UNKNOWN. The BMC truncates at `handle_goto` — the unroll bound — which is
//   correct: `n` is unconstrained above, so no constant number of unrollings
//   covers the loop. Constrain it (`n < 4`) and the BMC unrolls and answers
//   TRUE, which proves the program is provable and the shape is not at fault.
//
//   Measured 2026-10-30: raising the unroll bound to 20, the fork/visit/solver
//   budget 8x, the path-length bound to 4000, and the engine's clock share to
//   0.9 each convert nothing on this population. No tunable bound reaches an
//   unbounded loop.
//
//   So an over-approximating engine must discharge it, and the one that should
//   is the interval AI. It cannot, for a structural reason: `IState` is
//   `BTreeMap<VarId, Interval>` — one interval per variable, independently.
//   That domain is **non-relational**. It can say `i >= 0` and
//   `a.length >= 1`, and it has no way to express `i < a.length`, which is
//   the entire content of the proof.
//
//   The fix is a weakly relational domain — Pentagons (intervals plus symbolic
//   strict upper bounds, Logozzo & Fähndrich) is the classic answer and was
//   designed for exactly this check. Note this is *not* the array-content
//   problem: nothing here needs a fact about the elements, only about the
//   index. See gh #115, where array segmentation was the proposed direction
//   until this probe showed the gap is one level simpler.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    Verifier.assume(n > 0);
    int[] a = new int[n];
    // 0 <= i < n = a.length at every store, by the guard alone.
    for (int i = 0; i < n; i++) {
      a[i] = i;
    }
  }
}
