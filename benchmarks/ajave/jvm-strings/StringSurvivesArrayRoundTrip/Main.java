// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: string contents surviving a store into and load from an array
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   `a[0]` is assigned `s` and read straight back, so `t` is `s`. `s` is an
//   unconstrained input, so an execution with s = "<bad/>" reaches the
//   assertion. Confirmed by the JLS: an aastore followed by an aaload at the
//   same index yields the same reference, and String is immutable.
//
// Why this benchmark exists:
//   The BMC tracked string contents through *fields* -- `field_str_arrays`,
//   which the `$$coll_last` collection lowering uses -- and not through Java
//   arrays. `array_map` holds a 32-bit element per index, which models the
//   element *reference* and says nothing about the characters, so the round
//   trip lost the contents.
//
//   The cost was not imprecision but taint. `rvalue_tainted` taints any call
//   that is not a modelled string call, and `str_call_modelled` requires both
//   operands of `contains` to have tracked strings. With `t`'s contents gone
//   the call is unmodelled, the path is tainted, and `has_tainted_paths`
//   blocks discharge for the whole run. Measured as the reason 12 of 12
//   blocked securibench valid-assert tasks were stuck.
//
//   Note what finding the violation requires: the solver has to produce a
//   string satisfying `contains(t, "<bad/>")`. That is the string theory
//   deciding it, not a constant embedded in an engine -- the distinction that
//   sank the taint-engine experiment of 2026-08-24.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    String s = Verifier.nondetString();
    if (s == null) return;
    String[] a = new String[4];
    a[0] = s;
    String t = a[0];
    if (t.contains("<bad/>")) {
      assert false;
    }
  }
}
