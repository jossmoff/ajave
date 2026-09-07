/*
 * A loop bounded by `array.length` stays in bounds. Expected verdict: true.
 *
 * The bound is *relational* -- it relates the index to the array's length --
 * and that is why an interval domain cannot prove it. `i` ranges over
 * [0, 999] and `v.length` over [1, 1000]; nothing in a product of intervals
 * says `i < v.length`. Only a relational engine can, which for ajave means
 * the CHC encoding.
 *
 * CHC could not either, until array length became ghost state. `ArrayLength`
 * was an unconstrained fresh value, so the obligation `i >= 0 && i < len`
 * held no information at all and the query returned `unsat` -- a spurious
 * counterexample, read for a long time as "the encoding is imprecise about
 * the heap".
 *
 * The length is now a shadow integer threaded alongside the reference,
 * written at `new int[n]` (JLS 10.7: `length` is the creation dimension, and
 * it is final) and carried across edges like any other variable. It is
 * deliberately *not* an uninterpreted predicate or function: both of those
 * are interpreted by the solver, which may choose one that falsifies the
 * read and makes the path vacuously safe.
 */
import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  static int sink;

  static void fill(int[] a) {
    for (int i = 0; i < a.length; i++) a[i] = i;
  }

  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    if (n <= 0 || n > 1000) return;
    int[] v = new int[n];
    fill(v);
    sink = v[0];
  }
}
