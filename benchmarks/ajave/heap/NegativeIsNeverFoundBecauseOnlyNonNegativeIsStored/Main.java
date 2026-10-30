// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a quantified invariant over *field contents* of a linked
// structure, maintained across calls
// Expected: valid-assert=true
//
// `algorithms/BinaryTreeSearch-FunSat01` reduced from 120 lines to this. That
// task is the clearest member of the heap-shaped population the heap work was
// aimed at, and this is the property it actually needs -- argued below from
// what the CHC query does, not from what the engine happens to answer.
//
// Ground truth (by construction):
//   `insert` returns early for a negative argument, so every node reachable
//   from `head` has `value >= 0`. `search` returns true only on finding a node
//   whose value equals its argument. `v` is constrained negative. A negative
//   value therefore matches no node and `search(v)` is false on every
//   execution. Confirmed on a real JVM under -ea.
//
//   The proof obligation is `forall n reachable from head . value[n] >= 0`.
//   That is a statement about the *contents* of a field map, universally
//   quantified over references, and it must survive a call boundary: `insert`
//   establishes it and `search` consumes it.
//
// What ajave does, and why this is the honest boundary of the heap work:
//   UNKNOWN. The CHC encoding is not at fault and this was checked rather
//   than assumed. Dumping the Horn query for BinaryTreeSearch and deleting
//   the assertion's error rule leaves z3 answering `sat` -- safe -- in
//   milliseconds, so every other part of the encoding, including the Burstall
//   field arrays and C1's threaded summaries, is strong enough to be proven.
//   Restore that one rule and z3 answers `unsat` in 0.05s: the abstraction
//   admits a trace in which the assertion fails, and no amount of solver time
//   changes that, because the query is decided rather than timing out.
//
//   So the missing capability is not a heap *model*. It is inference of a
//   quantified invariant over heap contents. `AJAVE_CHC_QGEN` (Spacer's
//   quantified generalisation) is exactly the mechanism for this and it is on
//   by default; it finds the analogous invariant for
//   `EveryElementNonNullAfterAFillLoop`, where the quantified fact is
//   established by a loop over an array in one method. It does not find this
//   one, where the fact is established by a *guard* in one method and consumed
//   by a *traversal* in another.
//
//   That contrast is the point of keeping both benchmarks: they bracket what
//   qgen can currently do.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  static class Node {
    int value;
    Node next;
  }

  static Node head;

  // The guard that establishes the invariant.
  static void insert(int x) {
    if (x < 0) {
      return;
    }
    Node n = new Node();
    n.value = x;
    n.next = head;
    head = n;
  }

  // The traversal that consumes it.
  static boolean search(int x) {
    for (Node p = head; p != null; p = p.next) {
      if (p.value == x) {
        return true;
      }
    }
    return false;
  }

  public static void main(String[] args) {
    insert(Verifier.nondetInt());
    insert(Verifier.nondetInt());
    insert(Verifier.nondetInt());

    int v = Verifier.nondetInt();
    Verifier.assume(v < 0);
    // Holds because every stored value is non-negative.
    assert !search(v);
  }
}
