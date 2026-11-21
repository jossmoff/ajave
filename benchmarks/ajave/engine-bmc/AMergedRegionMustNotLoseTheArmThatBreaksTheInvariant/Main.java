// The FALSE twin of AChainOfOneArmedIfsMustNotForkPerBranch: a merged region
// must not lose the arm that breaks the invariant.
//
// Ground truth, by construction from the JLS. Every statement in the chain
// keeps `x + y == 24` except the one at bit 11, which increments `x`
// without decrementing `y` (JLS 15.26.2). So any execution with bit 11
// set reaches the assertion with `x + y == 25`, and `bits` is
// unconstrained, so such an execution exists. The expected verdict is FALSE.
// Confirmed on a real JVM: `java -ea Main` throws AssertionError whenever bit
// 11 of the nondeterministic int is set.
//
// Why this benchmark exists rather than only its TRUE twin. Merging a branch
// is new discharge surface: `handle_branch_diamond` explores both arms to the
// join and combines them with `ite(c, then, else)`, and that is exact **only
// if both arms are actually explored and both end states are actually
// merged**. If `merge_states_ite` dropped a component of the state, or if one
// arm were skipped, the lost arm here is the one carrying the violation — and
// the result would be a wrong TRUE on a program that fails, scored -32.
//
// So this is the test `CLAUDE.md` asks for under "every engine publishing
// `Over` needs a test that would fail if its encoding were unsound": the TRUE
// twin cannot distinguish a correct merge from a merge that silently loses an
// arm, because losing an arm still leaves the invariant holding. This one can.
//
// The violation is reachable only through the merged region, so finding it
// also confirms the merge preserves enough of the state for the BMC to solve
// for `bits` and for JvmReplay to reproduce the failure.
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
    if ((bits & (1 << 11)) != 0) { x = x + 1; }
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
