// A literal string's hash is a constant, and claiming otherwise manufactured
// a violation out of nothing.
//
// Ground truth, TRUE by specification with no inputs at all. The Javadoc
// defines `String.hashCode()` exactly:
//
//     s[0]*31^(n-1) + s[1]*31^(n-2) + ... + s[n-1]
//
// evaluated as `int` arithmetic. So "abc" hashes to
// 97*961 + 98*31 + 99 = 96354, on every conforming JVM, and both assertions
// below are constant-true. Confirmed on a real JVM.
//
// What ajave did, and why it is the interesting case for gh #88. The BMC's
// string encoder had:
//
//     "hashCode" => { let s = recv_str?; let _ = s;
//                     let h = self.solver.fresh_bv("hash", 32); ... }
//
// -- it discarded the receiver and returned an entirely *unconstrained*
// 32-bit value. Meanwhile `str_call_modelled` listed `hashCode` among the
// modelled calls, and the BMC derives taint from that classification. So the
// invented value was **untainted**, `handle_check`'s `!is_tainted` guard let
// it through, and `assert h != 0` was reported as violable: a violation
// claimed against a deterministic program, with a witness that necessarily
// carries nothing, because there is no input to blame.
//
// gh #88 described this mechanism for `Rvalue::Havoc` and proposed tainting
// the obligation's condition -- which the BMC already does. This instance
// escaped it from the other side: not a havoc, but a call *declared modelled*
// and encoded as a free variable. Being untainted, it also bypassed
// `skipped_obligations`, so the obligation was occupied by the claim rather
// than recorded as undecided, which blocks an over-approximating engine from
// proving it.
//
// The fix computes the hash for a literal receiver and declines otherwise, so
// this task does not merely stop being mis-claimed -- it is now *proved*.
// A symbolic receiver is declined, which taints the result and withholds the
// claim; declining can only remove violations, so it cannot create a wrong
// TRUE.
public class Main {
  public static void main(String[] args) {
    int h = "abc".hashCode();
    assert h != 0;
    assert h == 96354;
  }
}
