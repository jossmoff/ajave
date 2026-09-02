// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a store at one array index is not visible at another
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   `a[0]` is written and `a[1]` is never written, so `a[1]` is null and the
//   guarded body is unreachable. The assertion cannot fail for any input.
//
// Paired with StringSurvivesArrayRoundTrip so the two cannot be passed by the
// same wrong mechanism. A model that made every element carry the last stored
// string -- which is exactly what the `$$coll_last` collection lowering does --
// answers the first correctly and this one wrongly.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    String s = Verifier.nondetString();
    if (s == null) return;
    String[] a = new String[4];
    a[0] = s;
    String t = a[1];
    if (t != null && t.contains("<bad/>")) {
      assert false;
    }
  }
}
