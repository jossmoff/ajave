// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: UnknownReceiverReadsTheMergedCell
// Expected: valid-assert=false, no-runtime-exception=true
//
// The soundness case for B2, and the one the whole design rests on.
//
// The flat field abstraction is safe *because* it merges: every write to
// `Box.v` lands in one cell, so a read cannot be narrower than the truth. A
// site-indexed abstraction is only safe if a write through a receiver whose
// site is unknown still reaches every cell that receiver might denote —
// otherwise the read is too narrow, and a too-narrow read is a wrong TRUE.
//
// Here `which` comes from the Verifier, so the engine cannot know whether `c`
// is `a` or `b`. The write `c.v = 7` may therefore target either object.
//
// Ground truth (by construction, NOT by observation):
//   `assert a.v == 1` is FALSE: if `which` is non-zero then `c` is `a` and
//   `a.v` is 7. A real JVM fires the assertion for that input.
//
// A site-indexed abstraction that recorded `a.v = 1` and left it untouched by
// the write through `c` would prove this assertion and be wrong. The merged
// cell is what prevents that, and this program is the test named after it.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  static class Box { int v; }

  public static void main(String[] args) {
    Box a = new Box();
    Box b = new Box();
    a.v = 1;
    b.v = 2;

    int which = Verifier.nondetInt();
    Box c = (which != 0) ? a : b;
    c.v = 7;

    assert a.v == 1;
  }
}
