// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Expected: valid-assert=true, no-runtime-exception=true
//
// Feature under test: a nullness fact travelling between engines as a Query
// and a Lemma. The counterpart to SinBoundNeedsAnAnswer, for `Want::NonNull`
// rather than `Want::Bounds`.
//
// Ground truth (by construction, from the Collections contract):
//   `Collections.unmodifiableList(l)` returns an unmodifiable *view* of its
//   argument. It is specified to return a list, never null — it throws
//   NullPointerException if the argument is null, which cannot happen here
//   because `new ArrayList<>()` is non-null by JLS 15.9.4. So `view.size()`
//   cannot raise a NullPointerException. Confirmed on a real JVM.
//
// Why no single engine gets it:
//   * smt-bmc cannot model `unmodifiableList`, so the call is havoced and the
//     result is an unconstrained reference — which the solver is free to make
//     null, producing a NullDeref obligation it cannot discharge.
//   * The contract database knows the answer (`returns_nonnull` lists
//     `Collections.unmodifiableList`) and is not an engine: it publishes
//     nothing and reasons about no program.
//   * interval-ai tracks nullness but not through an unmodelled call's return.
//
// How the portfolio gets it:
//   smt-bmc posts `Query { about: view, want: NonNull }` instead of assuming
//   the worst. `ranges` answers from the contract — keyed on the full
//   (class, name, desc) signature, as every statement about an external method
//   must be. smt-bmc is woken by `Interest::LEMMA`, assumes `view != null`,
//   and the null branch is gone.
//
// Why the answer is a path constraint and not a discharge:
//   smt-bmc is an Under engine and may never conclude safety. It may *assume* a
//   fact an Over answerer established, which prunes a spurious path so the real
//   ones get explored. The discharge, if any, comes from an Over engine.

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class Main {

  public static void main(String[] args) {
    List<Integer> backing = new ArrayList<>();
    backing.add(1);
    List<Integer> view = Collections.unmodifiableList(backing);
    // No NPE: unmodifiableList is specified never to return null.
    int n = view.size();
    assert n >= 0;
  }
}
