/*
 * Adding 1.0f to a float of magnitude ~2e7 moves it by 2.0f, not 1.0f -- but
 * only when the tie breaks upward.
 *
 * A float has a 24-bit significand, so at magnitude m the spacing between
 * representable values is ulp(m) = 2^(floor(log2 m) - 23). For m near 2e7,
 * floor(log2 m) = 24, so ulp = 2.0 and the exact sum m + 1 lands exactly
 * halfway between two representable floats. JLS 15.18.2 rounds it under
 * IEEE-754 round-to-nearest-*even*, so which way it goes depends on m:
 *
 *   m = 20000000  ->  m/2 = 10000000 is even  ->  rounds down, m + 1.0f == m
 *   m = 20000002  ->  m/2 = 10000001 is odd   ->  rounds up,   m + 1.0f == m + 2
 *
 * 20000002.0f is used here, so `Math.abs(big - (big + 1.0f))` is 2.0f and the
 * assertion is VIOLATED. Expected verdict: false, argued from IEEE-754 and
 * confirmed on a real JVM (which also rejected the first draft of this file,
 * written with 2.0e7f -- that value ties to even and the assertion holds).
 *
 * Why this exists. `sv-comp/argv-tasks/ReverseInterpolator_true` is labelled
 * expected_verdict: true and is in fact violable, for exactly this reason. Its
 * assertion compares `t*t*t*t*t*16.0f` against `0.5f*x*x*x*x*x + 1` where
 * x = t*2.0f. The two products are *bit-identical*: every factor pulled across
 * is an exact power of two, and scaling by a power of two commutes with
 * rounding. So the whole assertion reduces to |v - (v + 1.0f)| < 1.1f, and for
 * |t| up to the guard's 100.0f, v reaches ~1.6e11 where ulp is far above 1.1.
 *
 * ajave reports FALSE on that task with the witness t = 16.342388f, which
 * throws AssertionError on a real JVM. The benchmark's label is wrong and ours
 * is right -- and being right costs -32 under SV-COMP scoring.
 *
 * Reduced here so the mechanism is visible in three lines rather than behind a
 * quintic and a branch.
 */
public class Main {
  public static void main(String[] args) {
    float big = 20000002.0f;
    assert Math.abs(big - (big + 1.0f)) < 1.1f;
  }
}
