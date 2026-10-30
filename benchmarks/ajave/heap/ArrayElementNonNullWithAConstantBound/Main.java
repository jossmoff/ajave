// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ArrayElementNonNullWithAConstantBound
// Expected: valid-assert=true, no-runtime-exception=true
//
// The program that showed the CHC encoders read arrays they never write, and
// that the heap work's real gate was never expressibility.
//
// `docs/proposals/heap-full-implementation.md` places this shape under Part D,
// "quantified invariants", as needing `∀j. 0 ≤ j < size → a[j] ≠ null`. With a
// **constant** bound no quantified invariant is needed at all — three
// unrollings suffice — and the CHC encoding still reported the assertion
// reachable. The encoding of this program contained twenty uses of the array
// havoc destination and **zero** `store`s.
//
// The cause is in neither the array theory nor the solver. `array_sites_of`
// answers one allocation site per variable for the whole body, and marks a
// variable ambiguous as soon as it is assigned from anything that is not a
// known array. javac reuses local slots, so the lifted body assigns one slot
// the array, then an *element* of it, then an `AssertionError` — the store's
// receiver is therefore ambiguous and the store havocs every array, while the
// reads happen to go through a different, non-reused variable and resolve
// fine. The encoder read an array it never wrote, so every element was
// unconstrained, including null.
//
// Ground truth (by construction, from the JVMS, NOT by observation):
//   `newarray` zero-fills and the loop assigns a fresh `A` to every index in
//   `0..3`, and `new` never yields null (JLS 15.9.4), so every element is
//   non-null at the read. The assertion holds.
//
// Kept as a benchmark distinct from EveryElementNonNullAfterAFillLoop because
// the two separate the two causes: this one needs only the store to be
// encoded, that one needs the store *and* a quantified invariant. Before the
// fix both failed, which is why the quantified one looked like evidence for a
// solver-side gate it was not.

public class Main {
  static class A {
    int x;
  }

  public static void main(String[] args) {
    A[] a = new A[3];
    for (int i = 0; i < 3; i++) {
      a[i] = new A();
    }
    for (int i = 0; i < 3; i++) {
      assert a[i] != null;
    }
  }
}
