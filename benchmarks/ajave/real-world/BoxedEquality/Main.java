// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Expected: valid-assert=true, no-runtime-exception=true
//
// Added 2026-09-10 from a held-out probe set written from the shape of
// ordinary Java rather than from anything in sv-benchmarks. Twelve probes,
// five of which ajave could not prove; this is one of them. Added BEFORE any
// fix, so it is demonstrated to reproduce.
//
// Feature under test: `equals` on a boxed primitive.
//
// Ground truth (by construction, from JLS 5.1.7 and Integer.equals):
//   `Integer x = 127` boxes via `Integer.valueOf`, which the JLS *requires* to
//   return a cached instance for values in [-128, 127]. `Integer.equals`
//   compares the wrapped `int` values, so `x.equals(y)` is true regardless of
//   caching. The assertion holds. Confirmed on a real JVM with -ea.
//
//   Note the assertion deliberately uses `equals` and not `==`. `x == y` is
//   also true here because of the cache, but only by an implementation detail
//   the JLS mandates over a narrow range — a benchmark resting on that would
//   be testing the cache, not the comparison.
//
// What ajave does, and why:
//   BLOCKER skipped_obligation, and the BMC withholds its own violation:
//   "tainted path with an empty witness cannot replay". `Integer.equals` is
//   unmodelled, so its result is unconstrained, the assertion is satisfiable,
//   and the resulting witness has no nondet values in it at all — there is no
//   input to blame. Suppressing it is right (it would fail replay), but the
//   obligation is then skipped and no over-approximating engine picks it up.
//
// The gap is a contract, not an engine: `Integer.equals(Object)` on two boxed
// ints has a specified result.

public class Main {
  public static void main(String[] a) {
    Integer x = 127, y = 127;      // inside the Integer cache
    assert x.equals(y);
  }
}
