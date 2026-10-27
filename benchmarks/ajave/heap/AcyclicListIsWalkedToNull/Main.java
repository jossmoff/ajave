// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: AcyclicListIsWalkedToNull
// Expected: valid-assert=true, no-runtime-exception=true
//
// The capability E1 exists for: the cheapest shape property worth having, and
// one that needs no new theory.
//
// A ghost `depth` per reference, maintained like the ghost array lengths the
// CHC encoder already keeps: `new` sets depth 0, and `o.next = p` sets
// `depth(o) = depth(p) + 1` when `p` is non-null. Acyclicity is then `depth`
// being well-founded, which the existing integer machinery proves — no
// separation logic, no reachability relation.
//
// Ground truth (by construction, from the JLS, NOT by observation):
//   The list is built tail-first from three fresh nodes, so `a.next.next.next`
//   is null and the walk below reaches null in exactly three steps. Both
//   assertions hold.
//
// The walk is written as a bounded loop rather than three dereferences so that
// the property genuinely depends on the chain's depth rather than on constant
// folding.

public class Main {
  static class Node {
    Node next;
  }

  public static void main(String[] args) {
    Node c = new Node();
    Node b = new Node();
    b.next = c;
    Node a = new Node();
    a.next = b;

    Node p = a;
    int steps = 0;
    while (p != null && steps < 10) {
      p = p.next;
      steps++;
    }
    assert p == null;
    assert steps == 3;
  }
}
