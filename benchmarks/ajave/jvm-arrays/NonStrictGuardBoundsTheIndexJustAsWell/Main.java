// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a non-strict loop guard, composed into a strict bound
// Expected: no-runtime-exception=true, valid-assert=true
//
// The third of the relational-bounds trio. `i <= n - 1` is the same bound as
// `i < n` written differently, and it is the guard shape in **24% of the
// 135-task `budget` population** — so a domain carrying only strict relations
// leaves a quarter of its target population untouched.
//
// Ground truth (by construction):
//   `a` has length `n`, and the guard admits `i` up to `n - 1`, so every
//   access is in bounds for every n in (0, 1000). Confirmed on a real JVM.
//
// Why it needs two facts rather than one:
//   `i <= n - 1` alone does **not** discharge a bounds check. `ArrayBounds`
//   requires `i < len`, and `i <= len` is false exactly at `i == len` — the
//   off-by-one that would be a wrong TRUE. The proof composes two relations:
//
//       i <= t      from the guard, where javac materialises t = n - 1
//       t < n       from `t = n - 1` with the interval showing no wrap
//       ------------
//       i < n       one hop, which is what `strict_via_le` performs
//
//   So the non-strict relation is never consulted on its own for a strict
//   question; it is only ever a step towards one. That separation is why `le`
//   is a second map rather than a flag on `lt` — folding them together loses
//   the distinction precisely where it matters.
//
//   The `t = n - 1` half carries its own guard: the relation `t < n` holds
//   only if the subtraction did not wrap, and the interval already computed
//   for `n` is what establishes that. On an unconstrained `int` it would not,
//   and the fact is simply not recorded.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    Verifier.assume(n > 0 && n < 1000);
    int[] a = new int[n];
    for (int i = 0; i <= n - 1; i++) {
      a[i] = i;
    }
  }
}
