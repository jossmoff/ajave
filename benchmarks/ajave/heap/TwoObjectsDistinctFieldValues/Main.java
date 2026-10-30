// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: TwoObjectsDistinctFieldValues
// Expected: valid-assert=true, no-runtime-exception=true
//
// The capability B2 exists for, and the case the flat field abstraction cannot
// express.
//
// `interval.rs` keeps ONE cell per `(class, name, desc)` with the receiver
// ignored, so `a.v` and `b.v` share a cell. A weak update joins, so after both
// writes the cell holds [1,2] and neither assertion is provable. Keying cells
// by allocation site separates them.
//
// Ground truth (by construction, from the JLS, NOT by observation):
//   `a` and `b` are distinct objects (JLS 12.5 — each `new` yields a fresh
//   reference), so `a.v` is 1 and `b.v` is 2 and both assertions hold.
//
// What must NOT happen: a site-indexed abstraction that reads `a.v` as 1 while
// some *other* write could have targeted the same object. Here no such write
// exists — both receivers are known — so the precision is honest. The
// companion benchmark UnknownReceiverReadsTheMergedCell covers the case where
// it is not.

public class Main {
  static class Box { int v; }

  public static void main(String[] args) {
    Box a = new Box();
    Box b = new Box();
    a.v = 1;
    b.v = 2;
    assert a.v == 1;
    assert b.v == 2;
  }
}
