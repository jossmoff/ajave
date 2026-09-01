// Part of ajave's own benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: `new StringBuilder(CharSequence)`
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   `StringBuilder(CharSequence)` is specified to contain the same characters
//   as the argument (JLS/Javadoc), so `t` is whatever `s` is. For
//   s = "<bad/>" the assertion fails.
//
// Why this benchmark exists:
//   The constructor model tested only for a `(Ljava/lang/String;)` descriptor
//   and treated **every other** constructor as producing an empty buffer. That
//   is right for `()` and for `(int)`, which really do start empty, and wrong
//   for `(CharSequence)`, which starts with the argument's characters.
//
//   Descriptor-blind defaults are the failure CLAUDE.md's modelling rules warn
//   about: keying on part of the signature and letting everything else fall
//   into one bucket. Here the bucket asserts emptiness, which is strong enough
//   to prove a guard false and discharge an obligation that is reachable.
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
  public static void main(String[] args) {
    String s = Verifier.nondetString();
    CharSequence cs = s;
    StringBuilder buf = new StringBuilder(cs);
    String t = buf.toString();
    if (t != null && t.contains("<bad/>")) {
      assert false;
    }
  }
}
