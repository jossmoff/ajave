// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a quantified heap invariant over unboundedly many cells
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Every element of `array` is assigned `new A()` before the second loop
//   reads it, and JLS 15.9.4 says a class instance creation expression never
//   produces null. So every element is non-null and the assertion holds.
//
//   The bound is nondeterministic, so no unrolling covers every execution --
//   a BMC can only report Bounded { k }. Proving it needs an invariant that
//   quantifies over all cells of the array: "every element written so far is
//   non-null". That is what CHC space invariants provide, by having the Horn
//   solver infer a predicate phi_arr(ref, idx, val) describing every cell at
//   once.
//
// Two facts must both be present, and this benchmark fails without either:
//   * the space invariant, or heap reads are unconstrained and the assertion
//     is unprovable;
//   * non-null allocation, or the invariant admits null and the assertion is
//     false under it.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
    static class A {
        int value = 0;
    }

    public static void main(String[] args) {
        int size = Verifier.nondetInt();
        if (size < 0 || size > 1000) {
            return;
        }
        A[] array = new A[size];
        for (int i = 0; i < size; i++) {
            array[i] = new A();
        }
        for (int i = 0; i < size; i++) {
            assert array[i] != null;
        }
    }
}
