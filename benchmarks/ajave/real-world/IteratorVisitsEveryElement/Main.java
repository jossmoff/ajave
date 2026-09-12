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
// Feature under test: a for-each loop over a collection, and the relationship
// between the number of iterations and `size()`.
//
// Ground truth (by construction, from the Iterable contract):
//   `Arrays.asList(1,2,3,4)` is a fixed-size list of exactly four elements.
//   The enhanced for loop is defined (JLS 14.14.2) as iterating until
//   `hasNext()` is false, which for this list is exactly `size()` times. So
//   `n == xs.size()` holds. Confirmed on a real JVM with -ea.
//
// What ajave does, and why:
//   UNKNOWN on both properties. Same root as `ArrayListSum` but through the
//   iterator protocol rather than an index: `hasNext`/`next` are unmodelled,
//   so the loop has no bound and the assertion relates two values the engine
//   has no facts about.
//
// Kept separate from `ArrayListSum` deliberately. The index form could be
// fixed by modelling `size()` alone; this one additionally needs the iterator
// protocol tied to the same length, and a fix for one is not a fix for both.

import java.util.*;
public class Main {
  public static void main(String[] a) {
    List<Integer> xs = Arrays.asList(1, 2, 3, 4);
    int n = 0;
    for (Integer x : xs) n++;
    assert n == xs.size();
  }
}
