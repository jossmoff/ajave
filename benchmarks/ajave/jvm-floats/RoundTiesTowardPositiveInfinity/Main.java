// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: which way Math.round breaks a tie
// Expected: valid-assert=true
//
// Ground truth (by construction, from the Javadoc, NOT by observation):
//   "the closest long to the argument, with ties rounding to positive
//   infinity". So round(2.5) is 3 and round(-2.5) is **-2**, not -3.
//   Confirmed on a real JVM.
//
// Why this benchmark exists:
//   Ties toward positive infinity is not ties-away-from-zero, and the two
//   differ on every negative half-integer. A model using `RNA` rounding, or
//   `Math.abs` plus a sign fix, gets -2.5 wrong.
//
//   It also pins a *known* imprecision rather than a bug. The engine models
//   the general case as |x - round(x)| <= 0.5, which at an exact tie admits
//   both neighbours: for -2.5 both -3 and -2 satisfy it. That is a deliberate
//   one-point over-approximation — sound, since an over-approximating result
//   can only cost precision, and JVM replay rejects a witness that lands on
//   the wrong neighbour.
//
//   So this benchmark is expected to be *unproven* rather than TRUE until the
//   tie direction is encoded. It is here to make that gap visible and to fail
//   loudly if a future model picks the wrong direction outright.
public class Main {
    public static void main(String[] args) {
        assert Math.round(2.5) == 3L;
        assert Math.round(-2.5) == -2L;
    }
}
