// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ShiftDistanceIsMasked
// Expected: valid-assert=true, no-runtime-exception=true

public class Main {

  public static void main(String[] args) {
    // Shift distances are masked to 5 bits for int, 6 for long.
    int x = 1;
    assert (x << 32) == 1;
    long l = 1L;
    assert (l << 64) == 1L;
  }
}
