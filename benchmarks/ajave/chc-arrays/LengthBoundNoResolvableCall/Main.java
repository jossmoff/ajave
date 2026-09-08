/*
 * The same array-bounds proof as `BoundedByArrayLength`, in a program with no
 * resolvable calls. Expected verdict: true.
 *
 * That difference selects a different CHC encoder. `encode_chc_interproc` is
 * used when something with a body is called; otherwise `encode_chc_single`,
 * the single-method bitvector encoder, is. They are two separate encoders and
 * a capability added to one is simply absent from the other -- which is how
 * ghost array lengths came to work inter-procedurally while the small array
 * benchmarks, whose only calls are to `Verifier`, stayed unprovable.
 *
 * `Verifier.nondetInt()` is not resolvable, so nothing here is: this file is
 * the bitvector encoder's copy of the same obligation.
 */
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  static int sink;

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    if (n <= 0 || n > 1000) return;
    int[] v = new int[n];
    for (int i = 0; i < v.length; i++) v[i] = i;
    sink = v[0];
  }
}
