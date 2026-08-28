// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: PathExplosionBounded
// Expected: valid-assert=true, no-runtime-exception=n/a

public class Main {

  public static void main(String[] args) {
    // 2^8 paths: exercises merging rather than raw enumeration.
    int sum = 0;
    for (int i = 0; i < 8; i++) {
      if (org.sosy_lab.sv_benchmarks.Verifier.nondetBoolean()) { sum++; }
    }
    assert sum >= 0 && sum <= 8;
  }
}
