// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: an input pinned only by a constraint BELOW the call
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   fib(6) = 8, and 8 != 3, so with x = 6 control reaches `assert false`.
//   Any x other than 6 returns early. So the assertion is violated, on
//   exactly one input, and the witness is x = 6.
//
// Why this shape defeats forward symbolic execution:
//   The only fact that pins x is `x != 6`, and it appears *after* the call.
//   A forward symbolic exploration therefore enters fibonacci(x) knowing
//   nothing about x, and a recursive callee over an unconstrained argument
//   forks until its budget is gone -- it never reaches the branch that would
//   have told it the answer. Measured 2026-09-06 on the equivalent SV-COMP
//   task: raising the fork budget eightfold changed nothing, while moving the
//   constraint above the call turned UNKNOWN into FALSE immediately.
//
//   Concolic execution inverts the roles. The concrete run computes fib(6)
//   with six additions rather than an exponential tree, and the solver only
//   sees the branch conditions along one concrete path -- here a single
//   `x != 6`. Flipping it yields x = 6 on the second iteration.
//
// The bound on x keeps this honest: without it the task would also be
// solvable by guessing small values, and would not distinguish an engine that
// reasons from one that enumerates.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
    static int fibonacci(int n) {
        if (n < 1) {
            return 0;
        } else if (n == 1) {
            return 1;
        } else {
            return fibonacci(n - 1) + fibonacci(n - 2);
        }
    }

    public static void main(String[] args) {
        int x = Verifier.nondetInt();
        // A *range* bound, so that executing this on a real JVM terminates --
        // fibonacci of an arbitrary int recurses until the stack runs out.
        // It deliberately does not pin x: the fact that selects the violating
        // input is still the `x != 6` below the call, which is the shape under
        // test. 21 candidate values is also far too many to stumble on by
        // probing, so an engine that guesses cannot pass this.
        if (x < 0 || x > 20) {
            return;
        }
        int result = fibonacci(x);
        if (x != 6 || result == 3) {
            return;
        } else {
            assert false;
        }
    }
}
