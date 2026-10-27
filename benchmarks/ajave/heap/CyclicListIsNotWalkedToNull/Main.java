// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: CyclicListIsNotWalkedToNull
// Expected: valid-assert=false, no-runtime-exception=true
//
// **The soundness case for E1.** A ghost depth is only a proof of acyclicity
// if a cycle makes it unsatisfiable rather than merely unknown.
//
// `o.next = o` would require `depth(o) = depth(o) + 1`, which has no integer
// solution — so the encoding must report the state infeasible, *not* satisfy
// it by letting depth drift. An implementation that maintained depth only on
// the first write, or that treated a self-assignment as a no-op, would make
// this program look acyclic and prove the assertion below.
//
// Ground truth (by construction, NOT by observation):
//   `o.next = o`, so following `next` never reaches null and the loop exits on
//   the step counter with `p == o`. `assert p == null` is FALSE and a real JVM
//   fires it.
//
// What a wrong answer here looks like: TRUE. That is the −16 this benchmark
// exists to make impossible, and it is why E1 cannot ship on the strength of
// AcyclicListIsWalkedToNull alone.

public class Main {
  static class Node {
    Node next;
  }

  public static void main(String[] args) {
    Node o = new Node();
    o.next = o;

    Node p = o;
    int steps = 0;
    while (p != null && steps < 10) {
      p = p.next;
      steps++;
    }
    assert p == null;
  }
}
