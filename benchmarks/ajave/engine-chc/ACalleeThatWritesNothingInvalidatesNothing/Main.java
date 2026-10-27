// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ACalleeThatWritesNothingInvalidatesNothing
// Expected: valid-assert=true, no-runtime-exception=true
//
// The converse of FieldWrittenInACalleeIsVisibleToTheCaller, and the case that
// keeps C1 honest in the other direction.
//
// A two-state summary can lose a fact as easily as carry one. `read` writes no
// field, so `b.v` must still be 5 at the assertion. If the summary relation
// failed to constrain the post-heap on a path that writes nothing — a missing
// frame condition — then `b.v` would become unconstrained after the call and
// the assertion would stop being provable.
//
// So this program fails as UNKNOWN rather than as a wrong answer, which is why
// it needs stating explicitly: a C1 that carries the write and drops the frame
// looks like a success on the companion benchmark and quietly costs points
// everywhere else.
//
// Ground truth (by construction, from the JLS, NOT by observation):
//   `read` returns `this.v` and assigns nothing, so `b.v` is 5 throughout and
//   both assertions hold.

public class Main {
  static class Box {
    int v;

    void set() {
      this.v = 5;
    }

    int read() {
      return this.v;
    }
  }

  public static void main(String[] args) {
    Box b = new Box();
    b.set();
    int seen = b.read();
    assert seen == 5;
    assert b.v == 5;
  }
}
