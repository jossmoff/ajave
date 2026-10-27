// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: IntervalHintAtAJoinMustHoldOnBothPaths
// Expected: valid-assert=false, no-runtime-exception=true
//
// A fault in the seam between `interval-ai` and `smt-bmc`, not inside either.
//
// `interval-ai` publishes an `Artifact::Invariant` per (block, variable),
// which `smt-bmc` asserts into its path formula as a fact true at that block
// on every path. `IState` stores intervals sparsely — a variable absent from
// the map *is* Top, and `IState::set` removes an entry rather than storing
// Top, by design. `join_block_intervals` then iterated `state.vars`, so a
// state in which the variable was Top contributed **nothing** to the join
// instead of widening it to Top.
//
// At the join below there are two abstract states. The then-branch narrowed
// `n` to [0,0]; the else-branch knows nothing about `n`, so `n` is absent from
// its map. The published hint was therefore `n ∈ [0,0]` at the join — a claim
// that is false on half the paths reaching it.
//
// Ground truth (by construction, NOT by observation):
//   `n` is `Verifier.nondetInt()` and unconstrained at the assertion, so the
//   assertion fails for every non-zero input. A real JVM fires it.
//
// What this cost: the BMC asserted `n = 0` into its path condition, found the
// violating path infeasible, reported `all_paths_complete`, and **discharged**
// the obligation. That is a wrong TRUE (−16). Here it is visible only because
// `concolic` independently found the violation and JVM replay confirmed it,
// which is what `Blackboard::contested()` reports — on a task where no
// under-approximating engine reaches the violation, nothing would have caught
// it.
//
// The `if` writes a static on both arms so javac cannot fold the branch away;
// the branch, not the write, is what the benchmark is about.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  static int sink;

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    if (n == 0) {
      sink = 10;
    } else {
      sink = 20;
    }
    assert n == 0;
  }
}
