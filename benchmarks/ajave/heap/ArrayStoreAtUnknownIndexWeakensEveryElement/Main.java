// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ArrayStoreAtUnknownIndexWeakensEveryElement
// Expected: valid-assert=false, no-runtime-exception=true
//
// The soundness case for B3, and the exact analogue of
// UnknownReceiverReadsTheMergedCell one level down.
//
// Per-index element cells are only safe if a store at an index the analysis
// cannot evaluate reaches *every* cell for that array. Otherwise the cell for
// `a[0]` still reads 7 after a store that may have targeted it, and a
// too-narrow read is a wrong TRUE.
//
// Ground truth (by construction, NOT by observation):
//   `i` is `Verifier.nondetInt()` masked to 0..2, so `a[i] = 99` may write
//   `a[0]`. `assert a[0] == 7` is therefore FALSE, and a real JVM fires it
//   whenever the masked value is 0. The mask is there so the store is in
//   bounds — this benchmark is about element values, and an
//   ArrayIndexOutOfBoundsException would make the assertion unreachable and
//   the task vacuously true.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int[] a = new int[3];
    a[0] = 7;
    a[1] = 9;

    int i = Verifier.nondetInt() & 3;
    if (i > 2) {
      i = 2;
    }
    a[i] = 99;

    assert a[0] == 7;
  }
}
