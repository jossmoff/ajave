// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: TwoNodeCycleIsNotWalkedToNull
// Expected: valid-assert=false, no-runtime-exception=true
//
// The program that shows why ghost depth is **not** a proof of acyclicity, and
// the reason E1 of `docs/proposals/heap-full-implementation.md` is sequenced
// wrongly.
//
// That plan says acyclicity is "`depth` being well-founded, which the existing
// integer machinery proves", maintained as `new` gives depth 0 and `o.f = p`
// gives `depth(o) = depth(p) + 1`. Encoded Burstall-style that is
//
//     d' = store(d, o, V)      V = ite(p = 0, 0, select(d', p) + 1)
//
// For a **self**-loop `o.f = o` this is unsatisfiable: `V = V + 1`. That is the
// case the plan's own soundness benchmark covers, and it is the only case the
// mechanism covers. Checked directly in z3:
//
//     o.next = o            unsat   (cycle detected)
//     a.next = b; b.next = a  sat   (cycle NOT detected)
//
// For the two-node cycle the second store recomputes `depth(b)` from the
// *current* `depth(a)` and nothing re-establishes `depth(a)` from the new
// `depth(b)`. Each individual store is consistent; only the global invariant
//
//     ∀x. x.f ≠ null → depth(x) > depth(x.f)
//
// rules the cycle out, and maintaining that across arbitrary field writes is a
// quantified invariant — which is checkpoint D1, placed *after* E1 in the plan.
//
// Ground truth (by construction, NOT by observation):
//   `a.next = b` and `b.next = a`, so following `next` never reaches null; the
//   loop exits on the step counter. `assert p == null` is FALSE and a real JVM
//   fires it.
//
// A tool that claimed to prove acyclicity by well-founded depth, and was tested
// only on a self-loop, would answer TRUE here. That is a −16, and it is what
// this benchmark exists to make impossible.

public class Main {
  static class Node {
    Node next;
  }

  public static void main(String[] args) {
    Node a = new Node();
    Node b = new Node();
    a.next = b;
    b.next = a;

    Node p = a;
    int steps = 0;
    while (p != null && steps < 10) {
      p = p.next;
      steps++;
    }
    assert p == null;
  }
}
