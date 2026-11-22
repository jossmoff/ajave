// The outer counter's lower bound must survive the inner loop's widening.
//
// JLS 14.14.1: `i` is initialised to 0 and only ever incremented, so `i >= 0`
// holds at every point in the loop body. A real JVM never reaches the assert
// with a negative `i`, so the expected verdict is TRUE by construction.
//
// What ajave did before the reduction step, and why it is interesting:
// the inner loop's header is a program point reached once per *outer*
// iteration with a different value of `i` each time, so the interval for `i`
// widens there to [0, Integer.MAX_VALUE]. The increment `i + 1` on a value
// that may be MAX_VALUE genuinely wraps in Java, so the interval transfer
// must return the whole range — and that discards the *lower* bound too.
// Nothing on a later branch restores it: narrowing `i < n` only bounds `i`
// from above. So `i` reached the assert as Top and `i >= 0` was unprovable,
// even though the loop guard `i < n` was recorded relationally the whole time.
//
// The fix is the reduction step of the reduced product: refine `i`'s interval
// with `i < n` before evaluating the increment, so it is computed against the
// guard's bound and never looks like an overflow. Note how little is needed:
// `n` is only known to be at least 1, so refining gives `i <= MAX_VALUE - 1`,
// and that single unit of slack is enough for `i + 1` not to wrap.
//
// `n` must NOT be bounded above here. An upper bound on `n` lets plain
// narrowing cap `i` at the loop guard and the overflow never arises, so the
// first version of this benchmark (`assume(n > 0 && n < 1000)`) proved under
// intervals alone and demonstrated nothing.
//
// The portfolio answers this task either way — the BMC unrolls it. The
// mechanism is visible only with the other engines removed:
//   AJAVE_DISABLE=smt-bmc,smt-bmc-fpa,concolic,kinduction,chc,imc,cegar,concrete,nra,presolve,exhaustive
// Under that, valid-assert is UNKNOWN without the reduction step and TRUE with
// it. (no-runtime-exception is TRUE either way: nothing in it needs the bound.)
// Note the engine ids are hyphenated and AJAVE_DISABLE matches them exactly --
// `smt_bmc` with an underscore silently disables nothing, which made a first
// version of this note describe a run that still had the BMC in it.
// The guard that
// actually holds the mechanism is therefore the domain law test
// `refinement_lets_a_widened_counter_be_incremented_without_overflow`; this
// file is here so the next reader can see the shape that provokes it.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    Verifier.assume(n > 0);
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        // The inner loop exists only to put a widening point between the
        // outer counter's definition and its use.
      }
      assert i >= 0;
    }
  }
}
