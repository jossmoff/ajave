// A chain of one-armed `if`s: 2^24 paths, and a property that needs all of them.
//
// Ground truth, by construction from the JLS. `x + y == 24` holds before the
// chain (0 + 24) and every statement in the chain either changes neither
// variable or increments `x` and decrements `y` together (JLS 15.26.2), so the
// sum is invariant. The assertion holds on all 16,777,216 executions and the
// expected verdict is TRUE. Confirmed on a real JVM with `-ea`.
//
// The property is deliberately **relational**. An interval domain learns
// `x in [0,24]` and `y in [0,24]`, hence `x + y in [0,48]`, and cannot
// discharge `x + y == 24`. So this is a question only a path-sensitive
// engine answers, which is what makes the verdict discriminate rather than
// just the counters.
//
// What it isolates: `if (c) { ... }` is the commonest branch shape in Java and
// javac compiles it to `ifeq join`, so the *else* target of the branch IS the
// join block. `find_join` used to intersect forward-reachable sets and decline
// whenever one arm's target was reachable from another's — exactly this shape,
// since the join is trivially reachable from the then block. Every one-armed
// if therefore took `handle_branch_fork`, which explores the entire remainder
// of the method once per arm. Twenty-four in sequence is 2^24 explorations of
// the tail: the search exhausts `MAX_FORKS` and reports
// `BLOCKER all_paths_complete` with its other budgets barely touched.
//
// Measured on this program, valid-assert, same build:
//
//   AJAVE_LBE=0   500 forks (the cap), 980 solver calls, 862 block visits
//   AJAVE_LBE=1     3 forks,             6 solver calls,  54 block visits
//
// The fix is to ask for the branch block's immediate post-dominator, which is
// what large-block encoding means (Beyer, Cimatti, Griggio, Keremoglu,
// Sebastiani, *Software Model Checking via Large-Block Encoding*, FMCAD 2009).
// Each branch then takes `handle_branch_diamond`: both arms are explored to
// the join, merged with one `ite` per differing variable, and the tail is
// explored **once**. Exploration becomes linear in the chain length.
//
// Why 24 and not three: the behaviour is a blowup, so the benchmark has to
// be past the point where the blowup bites. Three one-armed ifs fork eight
// ways and prove fine, which demonstrates nothing.
//
// The portfolio answers this task either way: there is no loop, so CHC's
// single-method bitvector encoding proves it in one query. The capability
// boundary is therefore visible only with the other over-approximating
// engines removed, and there it is exact:
//
//   AJAVE_DISABLE=chc,imc,cegar,concolic,kinduction AJAVE_LBE=0  -> UNKNOWN
//   AJAVE_DISABLE=chc,imc,cegar,concolic,kinduction AJAVE_LBE=1  -> TRUE
public class Main {
  public static void main(String[] args) {
    int bits = org.sosy_lab.sv_benchmarks.Verifier.nondetInt();
    int x = 0;
    int y = 24;
    if ((bits & (1 << 0)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 1)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 2)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 3)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 4)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 5)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 6)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 7)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 8)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 9)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 10)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 11)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 12)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 13)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 14)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 15)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 16)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 17)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 18)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 19)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 20)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 21)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 22)) != 0) { x = x + 1; y = y - 1; }
    if ((bits & (1 << 23)) != 0) { x = x + 1; y = y - 1; }
    assert x + y == 24;
  }
}
