// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: RecursiveFieldWriteIsNotForgotten
// Expected: valid-assert=false, no-runtime-exception=true
//
// **A confirmed soundness defect, reduced.** With `AJAVE_CHC_HEAP_SUMMARY=1`
// (C1) and every under-approximating engine disabled, CHC answers **TRUE** on
// this program — it proves a false assertion. See issue #106.
//
// Ground truth (by construction, NOT by observation):
//   `bump` increments `b.v` once per level and is called with n = 3, so `b.v`
//   is 3 at the assertion and `assert b.v == 0` FAILS. A real JVM throws
//   AssertionError on every run — there is no nondeterminism here, which is
//   the point: the corpus instance of this bug (`algorithms/Tsp-FunSat01`) has
//   a contested expected verdict and oracles that cannot conclude, so it
//   cannot settle the question. This program can.
//
// What makes it reachable: C1 threads field arrays through summary relations
// instead of clobbering them at the call site. The clobber was *masking* this
// defect — exactly the pattern CLAUDE.md records as "unsoundness masked by an
// unrelated conservative gate; removing a gate does not create these, it
// reveals them". So this is very likely a pre-existing CHC heap-encoding bug
// rather than one C1 introduced.
//
// Ruled out by reading the generated Horn query (all five checked, none is the
// cause):
//   * the pre/post collapse fixed on 2026-10-28 — entry-heap binders (`_e`)
//     are present and distinct from the post-heap in every conclusion
//   * the summary arity cap — 4 arguments, far under MAX_SUMMARY_FIELDS
//   * a missing `store` — `(store fld_Main_Box_v v5 _f0)` is present
//   * a lost receiver identity through the lifter's copy chain
//     (`v6 = v2; v5 = v6`) — the transition binds `w5 := v2` correctly
//   * the entry fact failing to tie `fld_e` to `fld` at the entry block
//
// The root cause is **not yet known**. Do not enable C1 until it is.

public class Main {
  static class Box {
    int v;
  }

  static void bump(Box b, int n) {
    if (n <= 0) {
      return;
    }
    b.v = b.v + 1;
    bump(b, n - 1);
  }

  public static void main(String[] args) {
    Box b = new Box();
    b.v = 0;
    bump(b, 3);
    assert b.v == 0;
  }
}
