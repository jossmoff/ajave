// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a coupled invariant that survives integer overflow
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   `i == j` is inductive: assume it for an arbitrary pair, then both are
//   incremented by the same amount, so they remain equal.
//
//   The interesting part is that this holds *through* overflow. JLS 15.18.2
//   defines int addition as wrapping modulo 2^32, and wrapping is a function
//   of the value alone -- equal inputs wrap to equal outputs. The loop is
//   unbounded, so an execution really can drive both past Integer.MAX_VALUE.
//
//   This is therefore a test that the step case models `+` as the JVM does.
//   An encoding that treated int addition as unbounded mathematical integers
//   would also prove it, but one that mixed the two -- wrapping on one side
//   of the equality and not the other -- would not.
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int i = 0;
    int j = 0;
    while (Verifier.nondetBoolean()) {
      i = i + 1;
      j = j + 1;
      assert i == j;
    }
  }
}
