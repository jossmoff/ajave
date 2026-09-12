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
// Feature under test: an array of strings returned by a JDK method.
//
// Ground truth (by construction, from the String.split contract):
//   `"a,b,c".split(",")` returns an array of exactly three elements — the
//   receiver contains two separators and no trailing empty string, and split
//   with a zero limit discards trailing empties only. So `parts.length == 3`.
//   Confirmed on a real JVM with -ea.
//
// What ajave does, and why:
//   UNKNOWN on both properties. `split` is unmodelled, so the result is a
//   havoced reference with no length. This is issue #28 in its smallest form:
//   a string term is lost the moment it passes through an array, and the
//   length that would decide the property never exists.
//
// Worth having as a benchmark rather than only as an issue because it takes
// three lines to state and needs no taint chain to reproduce.

public class Main {
  public static void main(String[] a) {
    String[] parts = "a,b,c".split(",");
    assert parts.length == 3;
  }
}
