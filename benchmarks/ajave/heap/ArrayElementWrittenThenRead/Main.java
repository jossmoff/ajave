// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ArrayElementWrittenThenRead
// Expected: valid-assert=true, no-runtime-exception=true
//
// The capability B3 exists for. `interval.rs` modelled array *lengths* and not
// element values — the comment at the `ArrayStore` arm said so — so every
// `aaload`/`iaload` read as Top and no claim about an element was provable.
//
// Ground truth (by construction, from the JVMS, NOT by observation):
//   `newarray` zero-fills, so `a[2]` is 0 before any store (JVMS 6.5
//   `newarray`: "each of the elements of the new array is initialized to the
//   default initial value for the element type"). The two stores set `a[0]` and
//   `a[1]`, leaving `a[2]` at its default. All three assertions hold.
//
// The third assertion is the one that matters: it is provable only if the
// zero-fill is modelled, not merely the stores. An implementation that tracked
// stores and left unwritten elements at Top would pass the first two and fail
// this one.

public class Main {
  public static void main(String[] args) {
    int[] a = new int[3];
    a[0] = 7;
    a[1] = 9;
    assert a[0] == 7;
    assert a[1] == 9;
    assert a[2] == 0;
  }
}
