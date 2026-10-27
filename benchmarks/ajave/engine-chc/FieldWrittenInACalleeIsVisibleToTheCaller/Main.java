// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: FieldWrittenInACalleeIsVisibleToTheCaller
// Expected: valid-assert=true, no-runtime-exception=true
//
// The capability C1 exists for, and the smallest program that needs it.
//
// CHC summary relations had arity `params + 1` — the parameters and the return
// value — so they could say nothing about a heap effect. A call to a method
// that may write a field therefore *clobbered* that field: the caller's
// knowledge of `b.v` was replaced by an unconstrained array after the call.
//
// `set` is void, so before C1 it had no summary at all. A void method exists
// entirely for its heap effect, which is exactly what a summary keyed on the
// return value cannot describe.
//
// Ground truth (by construction, from the JLS, NOT by observation):
//   `set` assigns `this.v = 5`, so `b.v` is 5 at the assertion and it holds.
//
// With the field threaded through `set`'s summary as a pre/post pair, the
// caller reads a *constrained* array after the call and the assertion is
// provable. Without it the read is unconstrained and nothing is provable.

public class Main {
  static class Box {
    int v;

    void set() {
      this.v = 5;
    }
  }

  public static void main(String[] args) {
    Box b = new Box();
    b.set();
    assert b.v == 5;
  }
}
