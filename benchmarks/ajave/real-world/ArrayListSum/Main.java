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
// Feature under test: the contents of a collection read back through an
// index-bounded loop. Ordinary Java; ajave cannot prove it.
//
// Ground truth (by construction, from the JLS and the Collection contract):
//   Three `add` calls on a fresh `ArrayList` leave `size() == 3` and elements
//   1, 2, 3 at indices 0..2 (java.util.List is an ordered sequence and
//   `add(E)` appends). The loop therefore runs exactly three times and sums
//   1 + 2 + 3 = 6. Confirmed on a real JVM with -ea.
//
// What ajave does, and why:
//   BLOCKER all_paths_complete. `size()` is not modelled, so it returns an
//   unconstrained value; the loop bound is then unknown, exploration unrolls
//   to MAX_LOOP_UNROLL and truncates, and a truncated search may not
//   discharge. The failure is *not* in the arithmetic — it is that a loop
//   bounded by a collection's own size has no bound at all.
//
//   This is the single most common shape in real Java that the portfolio
//   cannot see through: `for (int i = 0; i < xs.size(); i++)`.
//
// Related: #95 (heap contents), and the `CollectionStore/Load` model, which
// tracks the last stored element rather than the sequence.

import java.util.*;
public class Main {
  public static void main(String[] a) {
    List<Integer> xs = new ArrayList<>();
    xs.add(1); xs.add(2); xs.add(3);
    int sum = 0;
    for (int i = 0; i < xs.size(); i++) sum += xs.get(i);
    assert sum == 6;
  }
}
