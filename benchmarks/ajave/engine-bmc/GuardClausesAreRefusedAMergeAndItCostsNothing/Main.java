// Twenty-four guard clauses, every one refused a merge, and it costs nothing.
//
// This benchmark exists to record a *counter*-measurement: it is the evidence
// for NOT building the next level of region encoding.
//
// Ground truth, by construction from the JLS. `f` returns -1 as soon as any of
// the low 24 bits of `bits` is set. If none is set, all 24 iterations fall
// through, so `x` is incremented 24 times from 0 and `y` decremented 24 times
// from 24 (JLS 15.26.2), and the return is `24 + 0 == 24`. So the result is
// always -1 or 24 and the expected verdict is TRUE.
//
// A note on how that was established, because the obvious check is wrong:
// `java -ea Main` passes three times in a row against the assertion
// `r == -1 || r == 0`, which is FALSE. `Verifier.nondetInt()` virtually never
// returns 0, so the all-zero path -- the only one that reaches the `return
// x + y` -- is never taken. The verdict has to come from the JLS and an
// explicit all-zero driver, not from a green JVM run.
//
// What it measures. `if (c) { return ...; }` gives the branch no immediate
// post-dominator inside the method: one arm leaves without reconverging. So
// `cfg.rs` refuses every one of these a merge and they all fork --
// `cfg: Main.f(I)I blocks=49 merged=0 exits_method=24 back_edge=0`. Java
// Ranger's veritesting levels 4 and 5 (regions with more than one exit, and
// `return` as an exit) exist precisely to merge this shape.
//
// And it would gain nothing. Measured on this program, valid-assert, one
// build:
//
//   AJAVE_LBE=0   54 solver calls, 57 block visits, 27 forks
//   AJAVE_LBE=1   54 solver calls, 57 block visits, 27 forks
//
// Bit-identical, because a fork whose arm returns immediately duplicates no
// continuation. 57 block visits over a 49-block method is one pass. Contrast
// `AChainOfOneArmedIfsMustNotForkPerBranch`, where the same count of refused
// branches costs 980 solver calls against 4.
//
// The lesson is the one the corpus keeps teaching: a high decline *count* is
// not a high decline *cost*. `budget` once counted 135 tasks and was really 1;
// `refuted-witness` counted 211 pairs and was really 1. Here 24 of 24 branches
// are refused and the refusal is free. Building L4/L5 off the count would have
// been effort spent for no measurable gain -- see gh #129.
//
// 24 forks against `MAX_FORKS=500` also answers the one residual worry, that
// cheap forks still consume the fork budget and so forfeit discharge via
// `mark_incomplete`: it would take roughly 440 guard clauses in a single
// method to exhaust it.
public class Main {
  static int f(int bits) {
    int x = 0;
    int y = 24;
    if ((bits & (1 << 0)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 1)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 2)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 3)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 4)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 5)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 6)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 7)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 8)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 9)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 10)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 11)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 12)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 13)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 14)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 15)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 16)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 17)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 18)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 19)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 20)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 21)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 22)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    if ((bits & (1 << 23)) != 0) { return -1; }
    x = x + 1; y = y - 1;
    return x + y;
  }
  public static void main(String[] a) {
    int bits = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    int r = f(bits);
    assert r == -1 || r == 24;
  }
}
