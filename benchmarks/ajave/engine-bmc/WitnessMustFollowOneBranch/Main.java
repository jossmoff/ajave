// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: BMC witness extraction across an explored branch
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   `a` and `b` are unconstrained ints. On the execution where a = 1 and
//   b = 99, the guard `a > 0 && b == 99` holds and the assertion fails. That
//   execution is reachable because both values are unconstrained, so a
//   violating execution exists and the expected verdict is false. Confirmed on
//   a real JVM by supplying those values.
//
// Why this benchmark exists (issue #85):
//   The BMC appends the nondets of *both* arms of an explored branch to one
//   list, and `extract_witness` emits that whole list as the replay sequence.
//   The list is therefore what the exploration created, not what any single
//   execution consumes.
//
//   Here the engine records four values -- a, the then-branch x, the
//   else-branch x, and b -- while an execution with a > 0 consumes only three.
//   The JVM reads the else-branch's x where the engine meant b, so `b` gets the
//   wrong value, the assertion holds, and JVM replay refutes a violation that
//   is real. The task then scores UNKNOWN instead of FALSE.
//
//   Measured across a 214-task sample: 42 witnesses refuted, 39 of them with
//   the signature this program produces -- exit 0, no exception thrown, the
//   replayed run simply going somewhere else. 21 of the affected tasks expect
//   FALSE, so the violation was real every time.
//
//   Two nondets are needed, one per arm. With a nondet in only one arm the
//   sequence still lines up and nothing goes wrong, which is why this needs to
//   be written deliberately rather than found by accident.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
    public static void main(String[] args) {
        int a = Verifier.nondetInt();
        int x;
        if (a > 0) {
            x = Verifier.nondetInt();
        } else {
            x = Verifier.nondetInt();
        }
        int b = Verifier.nondetInt();
        assert !(a > 0 && b == 99) : "x was " + x;
    }
}
