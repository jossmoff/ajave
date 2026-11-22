// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: the flattened-matrix index lemma, i*s + j < m*s
// Expected: no-runtime-exception=true, valid-assert=true
//
// A 2D array held as a single flat allocation and addressed `a[i * s + j]` is
// the standard Java idiom for a matrix, and its bounds proof is beyond every
// weakly relational domain. This is the fourth of the relational-bounds set
// and the only one that needs an arithmetic lemma rather than a relation.
//
// Ground truth (by construction):
//   `v` is in (0, 46341), so `v*v` fits in `int`. The guards give `i < v` and
//   `j < v`, hence
//
//       i*v + j  <=  (v-1)*v + (v-1)  =  v*v - 1  <  v*v  =  d.length
//
//   and all of `i`, `j`, `v` are non-negative, so the index is in bounds on
//   every execution. Confirmed on a real JVM.
//
// Why no relational domain reaches it:
//   `i*v + j < v*v` is **non-linear** — a product of two program variables.
//   Pentagons states `x < y`, difference bounds `x - y <= c`, Octagons
//   `±x ±y <= c` with unit coefficients. None can express it. Intervals lose
//   the identity of `v`: `i*v` bounds at ~2.147e9 while `v*v` bounds below at
//   1, and nothing records that both mention the same `v`.
//
// What makes the rule legitimate rather than pattern matching:
//   `i < m and j < s implies i*s + j < m*s` is a theorem of arithmetic, true
//   for all i, j, m, s satisfying the premises. The domain contributes only
//   the *syntactic recognition* of which variables play those roles, read from
//   `mul_of` and `add_of` provenance, and every premise is checked rather than
//   assumed — including that `m*s` fits in `int`, without which the lemma
//   holds of mathematical integers and not of Java's.
//
// The half that is easy to miss:
//   An `ArrayBounds` obligation is `idx >= 0 & idx < len`, and the *lower*
//   half fails first. `i*v` bounds at ~2.147e9 and adding `j` leaves `int`, so
//   the abstract interval for the index is Top and even `idx >= 0` is
//   unprovable. The lemma therefore supplies both halves; with only the upper
//   one the comparison proved and the obligation still did not discharge.
//
// Known boundary — `algorithms/BellmanFord-*` is this idiom and is still
// UNKNOWN. There the array is allocated `new int[V*V]` in `main` and passed to
// `runBellmanFord(int N, int D[], int src)`, so inside the callee the needed
// fact `D.length == N*N` is a *precondition* that holds at the call site and is
// never stated. That is an interprocedural gap, not a gap in this lemma.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    int v = Verifier.nondetInt();
    Verifier.assume(v > 0 && v < 46341); // v*v < Integer.MAX_VALUE
    int[] d = new int[v * v];
    for (int i = 0; i < v; i++) {
      for (int j = 0; j < v; j++) {
        d[i * v + j] = 1;
      }
    }
  }
}
