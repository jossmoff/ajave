// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: TwoInstancesOneAllocationSite
// Expected: valid-assert=false, no-runtime-exception=true
//
// A guard for the flat field abstraction's soundness argument, and for
// whatever replaces it (H3 of docs/proposals/heap-theory.md).
//
// `interval.rs` keeps ONE cell per `(class, name, desc)` with the receiver
// ignored. A `PutField` may replace that cell outright — a *strong* update —
// only when `FieldPrec::may_update_strongly` says so, which for an instance
// field means the class is in `singleton_classes`: exactly one `New` site, and
// that site not inside a looping method.
//
// This program satisfies both conditions and still has two live instances,
// because `mk` is *called* twice. One site, no loop, two objects.
//
// Ground truth (by construction, from the JLS, NOT by observation):
//   `x` and `y` are distinct objects, so `x.v` is 1 and `y.v` is 2. The
//   assertion `x.v == 2` is therefore false and must fire. Confirmed on a real
//   JVM: AssertionError at the assert.
//
// Why ajave is nonetheless right today (verified 2026-10-27): the flat cell is
// saved by *call clobbering*. `FieldPrec::writes` records that `mk` writes
// `Box.v`, so each call to it invalidates that cell, and an invalidated cell
// reads as Top. The engine cannot prove `x.v == 2` and does not try.
//
// So the singleton licence is not the hole it looks like — but it is one
// conservative mechanism away from being one, and the mechanism is in a
// different file from the licence. That is why this program exists rather than
// a comment.
//
// What H3 must not break: once field cells are keyed by allocation site, `x`
// and `y` share a site, so a site-indexed abstraction conflates them exactly
// as the flat one does and must still widen. An implementation that keyed on
// the *variable* instead would read `x.v` as 1 and prove the assertion safe —
// a wrong TRUE, and the one `Approximations::HEAP_ALIASING` was written for.

public class Main {
  static class Box { int v; }

  // One allocation site. No loop. Called twice, so two instances are live
  // simultaneously — which `singleton_classes` (one site, not in a loop)
  // would license a *strong* update for.
  static Box mk(int v) {
    Box b = new Box();
    b.v = v;
    return b;
  }

  public static void main(String[] args) {
    Box x = mk(1);
    Box y = mk(2);
    // FALSE on a real JVM: x.v is 1. A flat cell that took the last strong
    // write holds 2, and an engine reading it would prove this.
    assert x.v == 2;
    if (y.v != 2) {
      assert false;
    }
  }
}
