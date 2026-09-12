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
// Feature under test: a virtual call through an interface with two
// implementations, which is what polymorphism looks like in real code.
//
// Ground truth (by construction, from JLS 15.12.4 on invokeinterface):
//   The receiver is either a `Sq(3)` or a `Re(2, 4)`, and dispatch selects the
//   implementation from the runtime class. So `area()` returns 9 or 8 and no
//   third value is possible. Confirmed on a real JVM with -ea.
//
// What ajave does, and why:
//   BLOCKER violated — the BMC *publishes a violation* here, and JVM replay
//   refutes it. With the call unresolved the result is unconstrained, so
//   `r == 9 || r == 8` is trivially falsifiable. CHC cannot take over:
//   `chc-imprecision: rvalue GetField` and `Nondet/Havoc` — it declines any
//   body that reads a field.
//
//   So this sits in the refuted-witness population: an engine finds a
//   violation that is not real, the obligation is closed, replay withdraws it,
//   and the task scores nothing. Two independent gaps have to close for it to
//   verify — devirtualisation over the two candidate types, and a CHC encoding
//   that does not decline on `GetField`.
//
// Related: #95 (heap contents), #18 (CHC declines heap ops).

interface Shape { int area(); }
class Sq implements Shape { int s; Sq(int s){this.s=s;} public int area(){ return s*s; } }
class Re implements Shape { int w,h; Re(int w,int h){this.w=w;this.h=h;} public int area(){ return w*h; } }
public class Main {
  public static void main(String[] a) {
    Shape s = (org.sosy_lab.sv_benchmarks.Verifier.nondetInt() > 0) ? new Sq(3) : new Re(2, 4);
    int r = s.area();
    assert r == 9 || r == 8;   // the only two possibilities
  }
}
