// Integer.parseInt(s) is modelled as a fresh bitvector with no relation to `s`.
//
// JLS 5.1.3 / Integer.parseInt: the method either returns the integer the
// string denotes in the given radix, or throws NumberFormatException. So on
// any path that returns normally, the result is a *function of the string* --
// it is not free to take an arbitrary value.
//
// ajave's BMC models the call as `fresh_bv("parse", 32)` and adds no
// constraint tying it to the argument. The solver may therefore pick n == 7
// while leaving the string entirely unconstrained, so the witness it prints is
// whatever the string solver happened to produce -- typically "A", which the
// JVM rejects with NumberFormatException before ever reaching the assert.
//
// Expected verdict: FALSE. The assertion is genuinely reachable (s = "7"), so
// this is a precision loss, not a soundness bug: we publish a violation that
// JVM replay refutes, and the task scores zero rather than wrong.
//
// Why it is not simply fixed: constraining `fresh = str.to_int(s)` is correct
// but asks Z3 to *invert* str.to_int over a free string. Measured 2026-09-05:
// this six-line program went from 1.0s to >90s (timeout). See the experiment
// issue for the numbers. A viable fix needs a bounded-length digit encoding
// rather than str.to_int.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
    public static void main(String[] args) {
        String s = Verifier.nondetString();
        int n;
        try {
            n = Integer.parseInt(s);
        } catch (NumberFormatException e) {
            return;
        }
        if (n == 7) {
            assert false;
        }
    }
}
