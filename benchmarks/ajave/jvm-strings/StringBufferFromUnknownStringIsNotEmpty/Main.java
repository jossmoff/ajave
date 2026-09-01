// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: `new StringBuffer(s)` when `s`'s content is not tracked
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   `s` is an unconstrained input, so `s2` is any string ending in ";", and a
//   StringBuffer built from it holds exactly that. For s = "<bad/>" the guard
//   is true and the assertion fails, so a violating execution exists.
//
// Why this benchmark exists:
//   The BMC modelled `new StringBuffer(x)` as the **empty string** whenever it
//   could not resolve x's symbolic content:
//
//       args.get(1).and_then(|a| self.encode_str_operand(a))
//           .unwrap_or_else(|| self.solver.str_const(""))
//
//   An unknown argument is not an empty one. Asserting `buf == ""` is a claim
//   about content the program never made, and it is strong enough to prove the
//   guard false -- so the branch holding the assertion was pruned as
//   infeasible, the obligation was never checked, and it was discharged as
//   unreachable. That is a wrong TRUE, worth -16.
//
//   The concatenation matters and is not decoration. `s + ";"` compiles to its
//   own StringBuilder append chain, which is what leaves the result untracked
//   at the point the StringBuffer is constructed; with `new StringBuffer(s)`
//   directly, the argument resolves and ajave answers FALSE correctly. That is
//   the paired benchmark below.
//
//   Found via securibench/Basic15, which has the same shape behind two casts.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    String s = Verifier.nondetString();
    String s2 = s + ";";
    StringBuffer buf = new StringBuffer(s2);
    String t = buf.toString();
    if (t != null && t.contains("<bad/>")) {
      assert false;
    }
  }
}
