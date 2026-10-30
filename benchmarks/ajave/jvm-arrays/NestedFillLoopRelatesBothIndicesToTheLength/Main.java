// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: relational facts surviving javac's copy chains
// Expected: no-runtime-exception=true, valid-assert=true
//
// The sibling of `FillLoopOfUnboundedLengthStaysInBounds`, and the one that
// pins the part of Pentagons that is specific to *bytecode* rather than to the
// domain.
//
// Ground truth (by construction):
//   `a` has length `n`. The inner guard is `j < n`, so every access `a[j]` is
//   in bounds, for every n in (0, 1000). Confirmed on a real JVM.
//
// What made this harder than the single loop:
//   `a[j] = a[j] + 1` is a *compound* assignment, and javac compiles it
//   through a chain of copies — the lifted IR reads
//
//       v22 = v12[v15]      // load
//       v23 = v12   v25 = v15   v27 = v22
//       v10 = v23   v24 = v25   v26 = v27
//       v30 = v10.length
//       v32 = v24 < v30     // the obligation's condition
//
//   so the index at the *store* is `v24`, three copies removed from the `v15`
//   the loop guard constrained. A relational domain that does not transfer
//   facts across `x = y` learns `v15 < n` on the guard and has lost it before
//   the obligation, which is exactly what this program did until copies were
//   handled: the single-loop benchmark passed and this one did not.
//
//   The rule is that `x = y` makes the two equal, so every relation on either
//   side of `y` transfers to `x`. Sound because it is an equality, and
//   necessary because stack-to-local copies are everywhere in JVM bytecode.
//   The Pentagons paper (Logozzo and Fähndrich, SAC 2008) targets .NET IL,
//   where the same shape arises; nothing about the domain itself says this,
//   and it is the first thing to check if a relation goes missing.

import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    Verifier.assume(n > 0 && n < 1000);
    int[] a = new int[n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        // Compound assignment: a load, three copies, then a store.
        a[j] = a[j] + 1;
      }
    }
  }
}
