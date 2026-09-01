// Part of ajave's contract-monotonicity corpus.
//
// SPDX-License-Identifier: Apache-2.0
//
// Each program here rests its verdict on exactly one library contract: the
// call below is the only thing that could throw, so the TRUE holds precisely
// because that method is contracted total.
//
// That is what makes them usable for metamorphic testing. Perturbing the
// contract to OPAQUE must weaken this to UNKNOWN and must never change it to
// FALSE. Sampling ordinary benchmarks instead does not work -- their verdicts
// rarely depend on any single contract, so every perturbation is inert and the
// test passes while proving nothing.
public class Main {
  public static void main(String[] args) {
    boolean v = Double.isNaN(1.0);
    boolean w = !v;
  }
}
