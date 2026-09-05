// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a TRUE property that is not k-inductive at ANY k
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   x starts at 0 and only ever gains 3, so it walks 0, 3, 6, 9, 12. From 9
//   the guard (9 < 11) still holds and x becomes 12; from 12 the guard fails
//   and x is fixed. So the reachable set is exactly {0,3,6,9,12} and the
//   assertion `x <= 12` holds on every execution.
//
//   But `x <= 12` is NOT inductive, and no larger k rescues it. Take x = 10:
//   it satisfies the invariant, satisfies the guard, and steps to 13, which
//   does not. k-induction assumes the property at k consecutive states and
//   may start from any of them, so it can always pick the chain
//       10-3(k-1), ..., 4, 7, 10  ->  13
//   whose first k states all satisfy `x <= 12` and whose successor does not.
//   The states are unreachable, but k-induction has no way to say so.
//
//   The missing fact is a congruence: x is always a multiple of 3. The bound
//   12 is tight only because 10 is not on that grid -- 11 was chosen as the
//   guard precisely so that guard-1 is not a multiple of the stride.
//
//   This is the integer analogue of the float_unboundedloop category, where
//   `0 <= x <= 8` fails to be inductive because x walks a 0.5 grid and x = 8.0
//   steps to 8.5. Same shape, no floating point involved, ten lines instead of
//   forty.
//
//   The step case was checked with z3 at k = 1, 2, 3 and 5: sat every time,
//   so the property really is not k-inductive at any depth.
//
//   ajave nonetheless answers TRUE, and correctly -- but not by induction.
//   k-induction never sees the obligation, because an exhaustive engine closes
//   it first: x saturates at 12 after four iterations and the state stops
//   changing, so the reachable set is finite and exploration completes.
//   Exhaustion is a sound proof and needs no congruence at all.
//
//   That is the lesson worth keeping, and it is why the float version is still
//   open. There the reachable set is finite too -- x takes 17 values -- but
//   they are floats, and exploration does not converge on them. So the missing
//   capability is a fixpoint that terminates over float states, not a
//   congruence domain. An earlier draft of this comment predicted UNKNOWN here
//   and called a TRUE unsound; both were wrong, and the benchmark is kept
//   partly as the record of that.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int x = 0;
    while (Verifier.nondetBoolean()) {
      if (x < 11) {
        x = x + 3;
      }
      assert x <= 12;
    }
  }
}
