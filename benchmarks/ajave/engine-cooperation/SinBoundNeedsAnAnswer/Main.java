// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: two engines answering one question between them.
// Expected: valid-assert=true, no-runtime-exception=true
//
// This is the smallest program no single engine in the portfolio can decide,
// and that the portfolio *as a portfolio* can.
//
// Ground truth (by construction, NOT by observation):
//   java.lang.Math.sin(double) is specified to return a value in [-1, 1] for
//   every finite argument, and NaN for NaN or an infinity. `Verifier.nondetInt`
//   is bounded by the guard below, so the argument is finite, so the result is
//   in [-1, 1]. 2.0 is outside that range, therefore `s > 2.0` is false on
//   every execution and the assertion is unreachable. The property holds.
//
// Why no one engine gets it:
//   * smt-bmc cannot encode `sin`. SMT-LIB's FloatingPoint theory has no
//     `fp.sin`, so the call becomes an unconstrained value and the solver is
//     free to claim `s == 5000`. It reports a violation on a path that does
//     not exist. (The verdict is not *wrong* — JVM replay refuses the witness
//     — but the obligation is closed and the task scores nothing.)
//   * interval-ai has a sound interval for `sin`, but the assertion sits
//     behind float arithmetic it does not track precisely enough to discharge.
//   * chc, k-induction, imc and cegar all decline a body containing float
//     arithmetic outright.
//   * ranges knows the answer — the Javadoc pins it — and could not verify a
//     program if its life depended on it. It publishes no statuses at all.
//
// How the portfolio gets it:
//   smt-bmc posts `Query { about: s, given: [s == Math.sin(x)], want: Bounds }`
//   rather than giving up. `ranges` answers with a `Lemma` guarded on NaN.
//   smt-bmc is woken by `Interest::LEMMA`, assumes the bound, and the error
//   path is now unsatisfiable.
//
//   That round trip is the whole point of the blackboard, and until the round
//   loop and cursor deltas existed the scheduler could not run it: the BMC
//   re-entered on a fixed latch whether or not anybody had answered, which is
//   why the mechanism measured as a cost and was left behind AJAVE_ASK=1.
//
// NaN cannot arise here: `sin` returns NaN only for a NaN or infinite
// argument, and neither is reachable from an int. So the property rests on the
// range alone, which is the thing under test. `dcmpl` would in any case send a
// NaN comparison to -1 and skip the assertion, and a benchmark that can pass
// for two reasons tests neither.

public class Main {

  public static void main(String[] args) {
    // An int widened to double is always finite, so the specified range
    // applies unconditionally and no guard is needed. Keeping one would put a
    // second branch in the path condition and make the trace harder to read
    // than the property.
    double s = Math.sin(org.sosy_lab.sv_benchmarks.Verifier.nondetInt());
    // Unreachable: sin is in [-1, 1] for every finite argument.
    if (s > 2.0) {
      assert false;
    }
  }
}
