// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: Math.round's specified semantics, not the old formula
// Expected: valid-assert=true
//
// Ground truth (by construction, from the Javadoc, NOT by observation):
//   `Math.round(double)` returns "the closest long to the argument, with ties
//   rounding to positive infinity". For the largest double below one half,
//   0.49999999999999994, the closest long is 0. Likewise `Math.round(float)`
//   on 0.49999997f is 0. Confirmed on a real JVM, which also shows the
//   contrast: `(long) Math.floor(d + 0.5)` is **1** for the same input.
//
// Why this benchmark exists (JDK-6430675):
//   `Math.round` used to be implemented as `floor(x + 0.5)`, and Java 7
//   changed it because that formula is wrong here: `d + 0.5` rounds up to
//   exactly 1.0 in double arithmetic, so the floor is 1 while the correct
//   answer is 0. The same happens in float for 0.49999997f.
//
//   `floor(x + 0.5)` is the obvious way to model rounding, it is what the
//   engine's model deliberately does *not* do, and nothing else in the suite
//   would notice if someone simplified it to that. The witness for such a
//   model is a value one greater than the truth, so it would show up as a
//   wrong FALSE on a program asserting the correct result — this one.
//
//   The engine models the general case relationally as
//   |x - round(x)| <= 0.5 rather than by any closed formula, precisely to
//   avoid committing to an arithmetic identity that does not hold.
public class Main {
    public static void main(String[] args) {
        double d = 0.49999999999999994;
        assert Math.round(d) == 0L;

        float f = 0.49999997f;
        assert Math.round(f) == 0;
    }
}
