// The flattened-matrix lemma, with the allocation and the indexing in
// different methods — the shape BellmanFord and the other graph benchmarks
// actually have.
//
// Ground truth, by construction: `main` assumes 0 < v < 46341 and allocates
// `v*v` ints, so `d.length == v*v` exactly and `v*v` cannot overflow (46340^2
// = 2147395600 < 2^31-1). `fill` is called with `n == v`, and its loops keep
// 0 <= i < n and 0 <= j < n, so `i*n + j <= (n-1)*n + (n-1) = n*n - 1`, which
// is `d.length - 1`. Every access is in bounds, so the verdict is TRUE.
// Confirmed on a real JVM by running the loop with concrete in-range `n`.
//
// What makes this interesting is that it needed two independent facts, and
// probing for one while the other was missing gave a misleading answer:
//
//   1. `d.length == n*n` must cross the call. `fill` on its own knows nothing
//      about `d`, so the AI derives this as an array-length *precondition*
//      when every call site agrees on it (see `analyze_array_len_preconditions`).
//
//   2. `n`'s upper bound must cross the call. The caller established
//      `v < 46341`, which is what makes `n*n` provably fit in an int. Only
//      `v > 0` currently propagates, so the lemma still declines here on the
//      overflow premise, and this task is UNKNOWN.
//
// There was a third, which is fixed: the outer counter reached the obligation
// as Top, because the inner loop's header widened it to `[0, MAX]` and `i + 1`
// on that interval wraps. See
// `jvm-arrays/OuterCounterKeepsItsLowerBoundAcrossAnInnerLoop`.
//
// So this file is a *deliberately unproven* case, kept because it names the
// one remaining fact. `AJAVE_TRACE_FLAT=1` prints which premise declines.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  static void fill(int n, int[] d) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        d[i * n + j] = 1;
      }
    }
  }

  public static void main(String[] args) {
    int v = Verifier.nondetInt();
    Verifier.assume(v > 0 && v < 46341);
    int[] d = new int[v * v];
    fill(v, d);
  }
}
