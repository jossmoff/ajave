// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: TwoReadsOfOneArrayLengthAreTheSameNumber
// Expected: valid-assert=true, no-runtime-exception=true
//
// Ground truth (by construction, from JVMS 6.5 `newarray`/`arraylength`, NOT
// by observation):
//
//   An array's length is fixed when it is created and `arraylength` returns
//   it unchanged, so two reads of one array's length are the same number and
//   that number is the creation argument. Both assertions hold.
//
// What this pins:
//
//   `interpolation::encode_body_lia` had **no arm for `Rvalue::ArrayLength`**.
//   It fell through `Encoder::rvalue`'s `_ => self.fresh(false)`, which mints a
//   *fresh* unconstrained integer per read -- so `p != q` was satisfiable for
//   two reads of the same array, `new int[n]` did not relate the array to `n`,
//   and the JVMS guarantee `length >= 0` was absent entirely. On that encoding
//   neither assertion below is provable, and the second is not even statable:
//   `invariant_check::render` had to decline `Expr::Length`, which dropped
//   every one of the 1,486 length conjuncts the interval domain publishes.
//
//   The model is one SMT array indexed by the reference -- McCarthy's theory
//   of arrays applied the way Burstall applies it to fields, which is how this
//   encoder already handles fields and how Boogie, VCC, Why3 and Dafny all
//   encode lengths. See docs/proposals/lia-faithfulness.md §5.
//
// `n` is nondeterministic so the length is symbolic: a concrete probe cannot
// settle this, and the fact has to be carried by the encoding rather than
// evaluated.
//
// Status: **already TRUE on c5d78d8**, the commit before this work, so this is
// a canary rather than a gain. Measured, not assumed. The bitvector BMC models
// arrays properly and decides it; the LIA encoder's missing length arm never
// got the chance to fail here. What the canary is worth is the direction: if a
// length fact is ever published, certified or eliminated against the LIA
// relation and this task goes UNKNOWN, the ghost model has regressed.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    Verifier.assume(n >= 0 && n < 100);
    int[] a = new int[n];

    int p = a.length;
    int q = a.length;
    // Two reads of one array's length. Unprovable while each read was a fresh
    // unconstrained integer.
    assert p == q;

    // And the length is the creation argument.
    assert p == n;
  }
}
