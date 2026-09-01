// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a library method contracted never to return null
// Expected: no-runtime-exception=true
//
// Ground truth (by construction, from the Javadoc, NOT by observation):
//   `Collections.singleton` returns an immutable set containing the argument
//   and `Collections.enumeration` returns an Enumeration over it. Neither can
//   return null, so the `hasMoreElements` call below cannot throw.
//
//   Nothing in the contract table can say that. A `Contract` states what a
//   method throws and what it writes, never what it *returns*, so the result of
//   an unmodelled call is an unconstrained reference and every dereference of
//   it stays unproven.
//
//   This is the exact shape that keeps securibench open: its mock servlet API
//   is real Java, and `getHeaderNames()` is literally
//   `Collections.enumeration(Collections.singleton(tainted))`. Both inner calls
//   havoc, so the Enumeration is unconstrained and the null check on it cannot
//   be discharged -- 65 open NullDeref obligations there and 57 in
//   jbmc-regression, from a missing thing to say rather than a missing analysis.
import java.util.Collections;
import java.util.Enumeration;
public class Main {
  public static void main(String[] args) {
    Enumeration<Object> e = Collections.enumeration(Collections.singleton("x"));
    boolean more = e.hasMoreElements();
  }
}
