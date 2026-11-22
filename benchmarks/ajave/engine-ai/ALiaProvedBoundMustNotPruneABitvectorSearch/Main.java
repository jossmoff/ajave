// An invariant proved over unbounded integers must not prune a search that
// reasons in bitvectors.
//
// Ground truth, by construction from the JLS. `sum` starts at
// Integer.MAX_VALUE - 1 and the loop adds 2, so on the second iteration it
// overflows and wraps to a negative value (JLS 15.18.2: integer addition is
// performed modulo 2^32). `a[sum]` with a negative `sum` throws
// ArrayIndexOutOfBoundsException, so the expected verdict for
// no-runtime-exception is FALSE. The assertion is never reached, so
// valid-assert is TRUE.
//
// Confirmed on a real JVM: it throws ArrayIndexOutOfBoundsException.
//
// What this pins. Candidate-elimination synthesis (`houdini`) checks
// preservation with the LIA encoder, where integers are unbounded. In that
// arithmetic `0 <= sum` IS preserved by `sum = sum + 2`, so the candidate
// survives and the map is inductive -- over LIA. On a JVM it is false the
// moment the addition wraps.
//
// `smt_text::lia_overflow_cond` states the same fact in the tree already:
// "Java's arithmetic wraps; linear integer arithmetic does not, so `x + 1 > x`
// is valid in an unbounded encoding and false on a JVM."
//
// The damage is not the claim, it is the consumer. The BMC reasons in
// bitvectors and uses a published bound to *prune* branches, so a bound that
// only holds without wrapping makes it skip the throwing path while still
// reporting `all_paths_complete` -- a wrong TRUE, scored -32. That is what
// happened on `sv-comp/algorithms/BellmanFord-FunUnsat01`
// [no-runtime-exception], which is now a smoke canary.
//
// The fix was to stop maps feeding the hint path and to declare
// `Approximations::INT_WRAPPING` on them instead of the `EXACT` that
// `publish` defaults to. Reinstating the consumer needs overflow-guarded
// preservation -- carry `lia_overflow_cond` through the preservation query so
// a surviving candidate is one that holds *and* cannot overflow. That is gh
// #77's problem in a new place.
//
// To see the mechanism rather than the verdict:
//   AJAVE_HOUDINI=1 RUST_LOG=ajave_engines::houdini=debug
public class Main {
  public static void main(String[] args) {
    int[] a = new int[10];
    int sum = Integer.MAX_VALUE - 1;
    int i = 0;
    while (i < 2) {
      sum = sum + 2;
      i = i + 1;
    }
    // Reached with sum < 0 on a JVM, and with sum > 0 in unbounded arithmetic.
    a[sum] = 1;
    assert a[0] == 0;
  }
}
