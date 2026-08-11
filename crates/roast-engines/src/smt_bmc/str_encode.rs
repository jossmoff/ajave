//! String method SMT encoding: String, StringBuilder, StringBuffer.
//!
//! Provides `str_call_modelled`, `encode_str_call`, and helper methods
//! for encoding Java string operations into SMT-LIB QF_S.

use roast_core::smt::Term;
use roast_ir::*;

use super::ExploreCtx;

impl<'a> ExploreCtx<'a> {
    /// Returns true if the given String/StringBuilder/StringBuffer method can be
    /// encoded precisely in SMT. Checks that required string operands are available.
    pub(super) fn str_call_modelled(&self, target: &MethodKey, args: &[Operand]) -> bool {
        let has_recv_str = args.first().map_or(false, |a| match a {
            Operand::Var(v) => self.str_vars.contains_key(v),
            Operand::Const(Const::Str(_)) => true,
            _ => false,
        });
        let has_arg1_str = args.get(1).map_or(false, |a| match a {
            Operand::Var(v) => self.str_vars.contains_key(v),
            Operand::Const(Const::Str(_)) => true,
            _ => false,
        });
        match target.name.as_str() {
            "length" | "isEmpty" | "toString" | "trim"
            | "toLowerCase" | "toUpperCase" => has_recv_str,
            "contains" | "equals" | "startsWith" | "endsWith" | "concat"
            | "equalsIgnoreCase" => {
                has_recv_str && has_arg1_str
            }
            "charAt" | "substring" | "hashCode" => has_recv_str,
            "indexOf" => {
                if target.desc.starts_with("(I") {
                    has_recv_str
                } else {
                    has_recv_str && has_arg1_str
                }
            }
            "lastIndexOf" => {
                if target.desc.starts_with("(I") {
                    has_recv_str
                } else {
                    has_recv_str && has_arg1_str
                }
            }
            "replace" if target.desc.starts_with("(CC)") => has_recv_str,
            "regionMatches" => {
                let other_idx = if target.desc.starts_with("(ZI") { 3 } else { 2 };
                let has_other_str = args.get(other_idx).map_or(false, |a| match a {
                    Operand::Var(v) => self.str_vars.contains_key(v),
                    Operand::Const(Const::Str(_)) => true,
                    _ => false,
                });
                has_recv_str && has_other_str
            }
            "valueOf" => {
                // Only model valueOf for primitive argument types (int, long, char, boolean).
                // valueOf(Object) calls toString() which we can't model.
                !target.desc.starts_with("(L") && !target.desc.starts_with("([")
            }
            // StringBuilder / StringBuffer methods
            "append" => has_recv_str,
            "setLength" | "deleteCharAt" | "reverse" => has_recv_str,
            "insert" => has_recv_str,
            "delete" => has_recv_str,
            _ => false,
        }
    }

    /// Encode a String/StringBuilder/StringBuffer method call.
    /// Returns `(bv_result, Option<str_term>)` or `None` if unhandled.
    pub(super) fn encode_str_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
    ) -> Option<(Term, Option<Term>)> {
        let recv_str = args.first().and_then(|a| self.encode_str_operand(a));
        let one = self.solver.bv_const(1, 32);
        let zero = self.solver.bv_const(0, 32);

        match target.name.as_str() {
            "length" => {
                let s = recv_str?;
                let len_int = self.solver.str_len(s);
                let len_bv = self.solver.int_to_bv32(len_int);
                Some((len_bv, None))
            }
            "isEmpty" => {
                let s = recv_str?;
                let len_int = self.solver.str_len(s);
                let zero_int = self.solver.int_const(0);
                let eq = self.solver.bveq(len_int, zero_int);
                let r = self.solver.ite(eq, one, zero);
                Some((r, None))
            }
            "contains" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_contains(s, t);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "equals" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_eq(s, t);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "startsWith" => {
                let s = recv_str?;
                let prefix = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                if let Some(off_op) = args.get(2) {
                    // startsWith(String prefix, int toffset)
                    let toff_bv = self.encode_operand(off_op);
                    let toff_int = self.solver.bv32_to_int(toff_bv);
                    let slen = self.solver.str_len(s);
                    let slen_bv = self.solver.int_to_bv32(slen);
                    let rem_bv = self.solver.bvsub(slen_bv, toff_bv);
                    let rem_int = self.solver.bv32_to_int(rem_bv);
                    let tail = self.solver.str_substr(s, toff_int, rem_int);
                    let b = self.solver.str_prefixof(prefix, tail);
                    let r = self.solver.ite(b, one, zero);
                    Some((r, None))
                } else {
                    let b = self.solver.str_prefixof(prefix, s);
                    let r = self.solver.ite(b, one, zero);
                    Some((r, None))
                }
            }
            "endsWith" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_suffixof(t, s);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "charAt" => {
                let s = recv_str?;
                let idx_bv = self.encode_operand(args.get(1)?);
                let idx_int = self.solver.bv32_to_int(idx_bv);
                let ch_str = self.solver.str_at(s, idx_int);
                let ch_int = self.solver.str_to_code(ch_str);
                let ch_bv = self.solver.int_to_bv32(ch_int);
                Some((ch_bv, None))
            }
            "indexOf" => {
                let s = recv_str?;
                if target.desc.starts_with("(I") {
                    let ch_bv = self.encode_operand(args.get(1)?);
                    let ch_int = self.solver.bv32_to_int(ch_bv);
                    let needle = self.solver.str_from_code(ch_int);
                    let start = if let Some(from_op) = args.get(2) {
                        let from_bv = self.encode_operand(from_op);
                        self.solver.bv32_to_int(from_bv)
                    } else {
                        self.solver.int_const(0)
                    };
                    let idx_int = self.solver.str_indexof(s, needle, start);
                    let idx_bv = self.solver.int_to_bv32(idx_int);
                    Some((idx_bv, None))
                } else {
                    let needle = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                    let start = if let Some(from_op) = args.get(2) {
                        let from_bv = self.encode_operand(from_op);
                        self.solver.bv32_to_int(from_bv)
                    } else {
                        self.solver.int_const(0)
                    };
                    let idx_int = self.solver.str_indexof(s, needle, start);
                    let idx_bv = self.solver.int_to_bv32(idx_int);
                    Some((idx_bv, None))
                }
            }
            "lastIndexOf" => {
                let s = recv_str?;
                if target.desc.starts_with("(I") {
                    let ch_bv = self.encode_operand(args.get(1)?);
                    let ch_int = self.solver.bv32_to_int(ch_bv);
                    let needle = self.solver.str_from_code(ch_int);
                    let max_from = if let Some(from_op) = args.get(2) {
                        let from_bv = self.encode_operand(from_op);
                        Some(self.solver.bv32_to_int(from_bv))
                    } else {
                        None
                    };
                    Some((self.encode_last_indexof(s, needle, max_from), None))
                } else {
                    let needle = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                    let max_from = if let Some(from_op) = args.get(2) {
                        let from_bv = self.encode_operand(from_op);
                        Some(self.solver.bv32_to_int(from_bv))
                    } else {
                        None
                    };
                    Some((self.encode_last_indexof(s, needle, max_from), None))
                }
            }
            "substring" => {
                let s = recv_str?;
                let start_bv = self.encode_operand(args.get(1)?);
                let start_int = self.solver.bv32_to_int(start_bv);
                let len_int = if let Some(end_op) = args.get(2) {
                    let end_bv = self.encode_operand(end_op);
                    let diff_bv = self.solver.bvsub(end_bv, start_bv);
                    self.solver.bv32_to_int(diff_bv)
                } else {
                    let total = self.solver.str_len(s);
                    let total_bv = self.solver.int_to_bv32(total);
                    let diff = self.solver.bvsub(total_bv, start_bv);
                    self.solver.bv32_to_int(diff)
                };
                let result = self.solver.str_substr(s, start_int, len_int);
                Some((one, Some(result)))
            }
            "concat" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let result = self.solver.str_concat(s, t);
                Some((one, Some(result)))
            }
            "toString" => {
                let s = recv_str?;
                Some((one, Some(s)))
            }
            "equalsIgnoreCase" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let s_low = self.str_to_lower(s);
                let t_low = self.str_to_lower(t);
                let b = self.solver.str_eq(s_low, t_low);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "regionMatches" => {
                let s = recv_str?;
                // regionMatches(int toffset, String other, int ooffset, int len)
                // regionMatches(boolean ignoreCase, int toffset, String other, int ooffset, int len)
                let (ignore_case, toff_idx, other_idx, ooff_idx, len_idx) =
                    if target.desc.starts_with("(ZI") {
                        (true, 2, 3, 4, 5)
                    } else {
                        (false, 1, 2, 3, 4)
                    };
                let other = args.get(other_idx).and_then(|a| self.encode_str_operand(a))?;
                let toff_bv = self.encode_operand(args.get(toff_idx)?);
                let ooff_bv = self.encode_operand(args.get(ooff_idx)?);
                let len_bv = self.encode_operand(args.get(len_idx)?);
                let toff_int = self.solver.bv32_to_int(toff_bv);
                let ooff_int = self.solver.bv32_to_int(ooff_bv);
                let len_int = self.solver.bv32_to_int(len_bv);
                // Bounds checks: Java returns false if offsets/len are out of range
                let slen = self.solver.str_len(s);
                let olen = self.solver.str_len(other);
                let slen_bv = self.solver.int_to_bv32(slen);
                let olen_bv = self.solver.int_to_bv32(olen);
                let t_end = self.solver.bvadd(toff_bv, len_bv);
                let t_ok = self.solver.bvsle(t_end, slen_bv);
                let o_end = self.solver.bvadd(ooff_bv, len_bv);
                let o_ok = self.solver.bvsle(o_end, olen_bv);
                let t_ge0 = self.solver.bvsle(zero, toff_bv);
                let o_ge0 = self.solver.bvsle(zero, ooff_bv);
                let l_ge0 = self.solver.bvsle(zero, len_bv);
                let bounds_ok = self.solver.and(t_ok, o_ok);
                let bounds_ok = self.solver.and(bounds_ok, t_ge0);
                let bounds_ok = self.solver.and(bounds_ok, o_ge0);
                let bounds_ok = self.solver.and(bounds_ok, l_ge0);

                let s_region = self.solver.str_substr(s, toff_int, len_int);
                let o_region = self.solver.str_substr(other, ooff_int, len_int);
                let eq = if ignore_case {
                    let ic_bv = self.encode_operand(args.get(1)?);
                    let ic_zero = self.solver.bveq(ic_bv, zero);
                    let ic_is_true = self.solver.not(ic_zero);
                    let s_low = self.str_to_lower(s_region);
                    let o_low = self.str_to_lower(o_region);
                    let eq_ci = self.solver.str_eq(s_low, o_low);
                    let eq_cs = self.solver.str_eq(s_region, o_region);
                    self.solver.ite(ic_is_true, eq_ci, eq_cs)
                } else {
                    self.solver.str_eq(s_region, o_region)
                };
                let b = self.solver.and(bounds_ok, eq);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "replace" if target.desc.starts_with("(CC)") => {
                let s = recv_str?;
                let old_bv = self.encode_operand(args.get(1)?);
                let new_bv = self.encode_operand(args.get(2)?);
                let old_int = self.solver.bv32_to_int(old_bv);
                let new_int = self.solver.bv32_to_int(new_bv);
                let old_str = self.solver.str_from_code(old_int);
                let new_str = self.solver.str_from_code(new_int);
                let result = self.solver.str_replace_all(s, old_str, new_str);
                Some((one, Some(result)))
            }
            "trim" => {
                let s = recv_str?;
                let result = self.solver.fresh_str("trimmed");
                let rlen = self.solver.str_len(result);
                let slen = self.solver.str_len(s);
                let rlen_bv = self.solver.int_to_bv32(rlen);
                let slen_bv = self.solver.int_to_bv32(slen);
                let le = self.solver.bvsle(rlen_bv, slen_bv);
                self.solver.assert(le);
                let cont = self.solver.str_contains(s, result);
                self.solver.assert(cont);
                Some((one, Some(result)))
            }
            "toLowerCase" => {
                let s = recv_str?;
                let result = self.str_to_lower(s);
                Some((one, Some(result)))
            }
            "toUpperCase" => {
                let s = recv_str?;
                let result = self.str_to_upper(s);
                Some((one, Some(result)))
            }
            "hashCode" => {
                let s = recv_str?;
                let _ = s;
                let h = self.solver.fresh_bv("hash", 32);
                Some((h, None))
            }
            "valueOf" if !target.desc.starts_with("(L") && !target.desc.starts_with("([") => {
                let arg_bv = self.encode_operand(args.first()?);
                if target.desc.starts_with("(Z)") {
                    let eq = self.solver.bveq(arg_bv, zero);
                    let is_nz = self.solver.not(eq);
                    let s_true = self.solver.str_const("true");
                    let s_false = self.solver.str_const("false");
                    let result = self.solver.ite(is_nz, s_true, s_false);
                    Some((one, Some(result)))
                } else if target.desc.starts_with("(C)") {
                    let ch_int = self.solver.bv32_to_int(arg_bv);
                    let result = self.solver.str_from_code(ch_int);
                    Some((one, Some(result)))
                } else {
                    let w = if target.desc.starts_with("(J)") { 64 } else { 32 };
                    let result = self.signed_bv_to_str(arg_bv, w);
                    Some((one, Some(result)))
                }
            }
            // StringBuilder / StringBuffer methods
            "append" => {
                let s = recv_str?;
                let arg = args.get(1)?;
                let arg_str = self.encode_str_operand(arg).unwrap_or_else(|| {
                    let bv = self.encode_operand(arg);
                    if target.desc.starts_with("(Z)") {
                        let zero_bv = self.solver.bv_const(0, 32);
                        let eq = self.solver.bveq(bv, zero_bv);
                        let is_nz = self.solver.not(eq);
                        let s_true = self.solver.str_const("true");
                        let s_false = self.solver.str_const("false");
                        self.solver.ite(is_nz, s_true, s_false)
                    } else if target.desc.starts_with("(C)") {
                        let ch_int = self.solver.bv32_to_int(bv);
                        self.solver.str_from_code(ch_int)
                    } else {
                        let w = if target.desc.starts_with("(J)") { 64 } else { 32 };
                        self.signed_bv_to_str(bv, w)
                    }
                });
                let result = self.solver.str_concat(s, arg_str);
                let recv_bv = self.encode_operand(args.first()?);
                Some((recv_bv, Some(result)))
            }
            "setLength" => {
                let s = recv_str?;
                let len_bv = self.encode_operand(args.get(1)?);
                let len_int = self.solver.bv32_to_int(len_bv);
                let zero_int = self.solver.int_const(0);
                let result = self.solver.str_substr(s, zero_int, len_int);
                let recv_bv = self.encode_operand(args.first()?);
                Some((recv_bv, Some(result)))
            }
            "deleteCharAt" => {
                let s = recv_str?;
                let idx_bv = self.encode_operand(args.get(1)?);
                let idx_int = self.solver.bv32_to_int(idx_bv);
                let zero_int = self.solver.int_const(0);
                let prefix = self.solver.str_substr(s, zero_int, idx_int);
                let slen = self.solver.str_len(s);
                let slen_bv = self.solver.int_to_bv32(slen);
                let one_bv = self.solver.bv_const(1, 32);
                let idx_plus1 = self.solver.bvadd(idx_bv, one_bv);
                let rem_bv = self.solver.bvsub(slen_bv, idx_plus1);
                let rem_int = self.solver.bv32_to_int(rem_bv);
                let after_int = self.solver.bv32_to_int(idx_plus1);
                let suffix = self.solver.str_substr(s, after_int, rem_int);
                let result = self.solver.str_concat(prefix, suffix);
                let recv_bv = self.encode_operand(args.first()?);
                Some((recv_bv, Some(result)))
            }
            "delete" => {
                let s = recv_str?;
                let start_bv = self.encode_operand(args.get(1)?);
                let end_bv = self.encode_operand(args.get(2)?);
                let start_int = self.solver.bv32_to_int(start_bv);
                let end_int = self.solver.bv32_to_int(end_bv);
                let zero_int = self.solver.int_const(0);
                let prefix = self.solver.str_substr(s, zero_int, start_int);
                let slen = self.solver.str_len(s);
                let slen_bv = self.solver.int_to_bv32(slen);
                let rem_bv = self.solver.bvsub(slen_bv, end_bv);
                let rem_int = self.solver.bv32_to_int(rem_bv);
                let suffix = self.solver.str_substr(s, end_int, rem_int);
                let result = self.solver.str_concat(prefix, suffix);
                let recv_bv = self.encode_operand(args.first()?);
                Some((recv_bv, Some(result)))
            }
            "insert" => {
                let s = recv_str?;
                let off_bv = self.encode_operand(args.get(1)?);
                let off_int = self.solver.bv32_to_int(off_bv);
                let zero_int = self.solver.int_const(0);
                let prefix = self.solver.str_substr(s, zero_int, off_int);
                let slen = self.solver.str_len(s);
                let slen_bv = self.solver.int_to_bv32(slen);
                let rem_bv = self.solver.bvsub(slen_bv, off_bv);
                let rem_int = self.solver.bv32_to_int(rem_bv);
                let suffix = self.solver.str_substr(s, off_int, rem_int);
                let ins_arg = args.get(2)?;
                let ins_str = self.encode_str_operand(ins_arg).unwrap_or_else(|| {
                    let bv = self.encode_operand(ins_arg);
                    self.signed_bv_to_str(bv, 32)
                });
                let tmp = self.solver.str_concat(prefix, ins_str);
                let result = self.solver.str_concat(tmp, suffix);
                let recv_bv = self.encode_operand(args.first()?);
                Some((recv_bv, Some(result)))
            }
            "reverse" => {
                let s = recv_str?;
                let result = self.solver.fresh_str("reversed");
                let rlen = self.solver.str_len(result);
                let slen = self.solver.str_len(s);
                let eq = self.solver.bveq(rlen, slen);
                self.solver.assert(eq);
                let recv_bv = self.encode_operand(args.first()?);
                Some((recv_bv, Some(result)))
            }
            _ => None,
        }
    }

    /// Encode lastIndexOf via iterative forward search (8 iterations).
    pub(super) fn encode_last_indexof(&mut self, s: Term, needle: Term, max_from: Option<Term>) -> Term {
        let zero_int = self.solver.int_const(0);
        let nlen = self.solver.str_len(needle);

        let search_s = if let Some(mf) = max_from {
            let mf_bv = self.solver.int_to_bv32(mf);
            let nlen_bv = self.solver.int_to_bv32(nlen);
            let bound_bv = self.solver.bvadd(mf_bv, nlen_bv);
            let bound_int = self.solver.bv32_to_int(bound_bv);
            self.solver.str_substr(s, zero_int, bound_int)
        } else {
            s
        };

        let start = self.solver.int_const(0);
        let mut cur = self.solver.str_indexof(search_s, needle, start);
        for _ in 0..8 {
            let cur_bv = self.solver.int_to_bv32(cur);
            let one_bv = self.solver.bv_const(1, 32);
            let next_start_bv = self.solver.bvadd(cur_bv, one_bv);
            let next_start = self.solver.bv32_to_int(next_start_bv);
            let next = self.solver.str_indexof(search_s, needle, next_start);
            let neg1_int = self.solver.int_const(-1);
            let eq_neg1 = self.solver.bveq(next, neg1_int);
            let found = self.solver.not(eq_neg1);
            cur = self.solver.ite(found, next, cur);
        }
        self.solver.int_to_bv32(cur)
    }

    /// Approximate toLowerCase: replace A-Z with a-z via str.replace_all.
    pub(super) fn str_to_lower(&mut self, s: Term) -> Term {
        let mut result = s;
        for (upper, lower) in (b'A'..=b'Z').zip(b'a'..=b'z') {
            let u = self.solver.str_const(&String::from(upper as char));
            let l = self.solver.str_const(&String::from(lower as char));
            result = self.solver.str_replace_all(result, u, l);
        }
        result
    }

    /// Approximate toUpperCase: replace a-z with A-Z via str.replace_all.
    pub(super) fn str_to_upper(&mut self, s: Term) -> Term {
        let mut result = s;
        for (lower, upper) in (b'a'..=b'z').zip(b'A'..=b'Z') {
            let l = self.solver.str_const(&String::from(lower as char));
            let u = self.solver.str_const(&String::from(upper as char));
            result = self.solver.str_replace_all(result, l, u);
        }
        result
    }

    /// Encode a signed bitvector to its decimal string representation.
    /// `width` must match the actual BV width of `val` (32 or 64).
    pub(super) fn signed_bv_to_str(&mut self, val: Term, width: u32) -> Term {
        let zero_bv = self.solver.bv_const(0, width);
        let is_neg = self.solver.bvslt(val, zero_bv);
        let neg_val = self.solver.bvneg(val);
        let abs_int = self.solver.bv32_to_int(neg_val);
        let pos_int = self.solver.bv32_to_int(val);
        let pos_str = self.solver.str_from_int(pos_int);
        let neg_str_tail = self.solver.str_from_int(abs_int);
        let minus = self.solver.str_const("-");
        let neg_str = self.solver.str_concat(minus, neg_str_tail);
        self.solver.ite(is_neg, neg_str, pos_str)
    }

    /// Encode an unsigned bitvector to its decimal string (toUnsignedString).
    pub(super) fn unsigned_bv_to_str(&mut self, val: Term, _width: u32) -> Term {
        let uint = self.solver.bv32_to_int(val);
        self.solver.str_from_int(uint)
    }

    /// Encode an unsigned bitvector to its hex string (toHexString).
    pub(super) fn unsigned_bv_to_hex_str(&mut self, val: Term, width: u32) -> Term {
        self.unsigned_bv_to_radix_str(val, width, 4, true)
    }

    /// Encode an unsigned bitvector to its octal string (toOctalString).
    pub(super) fn unsigned_bv_to_oct_str(&mut self, val: Term, width: u32) -> Term {
        self.unsigned_bv_to_radix_str(val, width, 3, false)
    }

    /// Encode an unsigned bitvector to its binary string (toBinaryString).
    pub(super) fn unsigned_bv_to_bin_str(&mut self, val: Term, width: u32) -> Term {
        self.unsigned_bv_to_radix_str(val, width, 1, false)
    }

    /// Generic radix conversion: extract groups of `bits_per_digit` bits,
    /// map each to a character code, strip leading zeros.
    /// If `hex` is true, digits 10-15 map to 'a'-'f'; otherwise digits map to '0'+digit.
    fn unsigned_bv_to_radix_str(
        &mut self,
        val: Term,
        width: u32,
        bits_per_digit: usize,
        hex: bool,
    ) -> Term {
        let num_digits = (width as usize + bits_per_digit - 1) / bits_per_digit;
        let digit_mask = ((1u64 << bits_per_digit) - 1) as i64;
        let mask = self.solver.bv_const(digit_mask, width);

        // Build a string character for each digit position (LSB first)
        let mut digit_strs = Vec::with_capacity(num_digits);
        for i in 0..num_digits {
            let shift_amt = (i * bits_per_digit) as i64;
            let shift = self.solver.bv_const(shift_amt, width);
            let shifted = self.solver.bvlshr(val, shift);
            let digit = self.solver.bvand(shifted, mask);
            // Map digit to character code
            let char_code = if hex {
                let ten = self.solver.bv_const(10, width);
                let is_digit = self.solver.bvult(digit, ten);
                let c48 = self.solver.bv_const(48, width);
                let d_code = self.solver.bvadd(digit, c48);
                let c87 = self.solver.bv_const(87, width);
                let a_code = self.solver.bvadd(digit, c87);
                self.solver.ite(is_digit, d_code, a_code)
            } else {
                let c48 = self.solver.bv_const(48, width);
                self.solver.bvadd(digit, c48)
            };
            let char_int = self.solver.bv32_to_int(char_code);
            let char_str = self.solver.str_from_code(char_int);
            digit_strs.push(char_str);
        }

        // Build cumulative strings: cumulative[0] = digit[0], cumulative[1] = digit[1]++digit[0], ...
        let mut cumulative = Vec::with_capacity(num_digits);
        cumulative.push(digit_strs[0]);
        for i in 1..num_digits {
            let prev = cumulative[i - 1];
            let cur = self.solver.str_concat(digit_strs[i], prev);
            cumulative.push(cur);
        }

        // Select by magnitude: use the shortest string that fits the value
        let zero_bv = self.solver.bv_const(0, width);
        let zero_str = self.solver.str_const("0");
        let mut result = cumulative[num_digits - 1]; // full-length string

        for i in (0..num_digits - 1).rev() {
            let threshold_shift = (i + 1) * bits_per_digit;
            if threshold_shift < 64 {
                let threshold = self.solver.bv_const((1u64 << threshold_shift) as i64, width);
                let cond = self.solver.bvult(val, threshold);
                result = self.solver.ite(cond, cumulative[i], result);
            }
        }

        let is_zero = self.solver.bveq(val, zero_bv);
        self.solver.ite(is_zero, zero_str, result)
    }

    // ── Wrapper toString encoding ───────────────────────────────────────

    /// Encode wrapper-type calls that produce strings.
    /// Returns (bv_ref, Some(str_term)) on success.
    pub(super) fn encode_wrapper_str_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
    ) -> Option<(Term, Option<Term>)> {
        let one = self.solver.bv_const(1, 32);
        match (target.class.as_str(), target.name.as_str()) {
            // Boolean.toString(boolean) / Boolean.toString()
            ("java/lang/Boolean", "toString") => {
                let val = if target.desc.starts_with("(Z)") {
                    self.encode_operand(args.first()?)
                } else if target.desc == "()Ljava/lang/String;" {
                    let recv = self.encode_operand(args.first()?);
                    let fk = (
                        "java/lang/Boolean".to_string(),
                        "$$value".to_string(),
                        "I".to_string(),
                    );
                    let arr = self.get_field_array(&fk, 32);
                    self.solver.array_select(arr, recv)
                } else {
                    return None;
                };
                let zero = self.solver.bv_const(0, 32);
                let eq = self.solver.bveq(val, zero);
                let is_nz = self.solver.not(eq);
                let s_true = self.solver.str_const("true");
                let s_false = self.solver.str_const("false");
                let result = self.solver.ite(is_nz, s_true, s_false);
                Some((one, Some(result)))
            }
            // Integer.toString(int) / Integer.toString()
            ("java/lang/Integer", "toString") => {
                let val = if target.desc.starts_with("(I)") {
                    self.encode_operand(args.first()?)
                } else if target.desc == "()Ljava/lang/String;" {
                    let recv = self.encode_operand(args.first()?);
                    let fk = (
                        "java/lang/Integer".to_string(),
                        "$$value".to_string(),
                        "I".to_string(),
                    );
                    let arr = self.get_field_array(&fk, 32);
                    self.solver.array_select(arr, recv)
                } else {
                    return None;
                };
                let result = self.signed_bv_to_str(val, 32);
                Some((one, Some(result)))
            }
            // Long.toString(long) / Long.toString()
            ("java/lang/Long", "toString") => {
                let val = if target.desc.starts_with("(J)") {
                    self.encode_operand(args.first()?)
                } else if target.desc == "()Ljava/lang/String;" {
                    let recv = self.encode_operand(args.first()?);
                    let fk = (
                        "java/lang/Long".to_string(),
                        "$$value".to_string(),
                        "J".to_string(),
                    );
                    let arr = self.get_field_array(&fk, 64);
                    self.solver.array_select(arr, recv)
                } else {
                    return None;
                };
                let result = self.signed_bv_to_str(val, 64);
                Some((one, Some(result)))
            }
            // Integer/Long.toHexString
            ("java/lang/Integer", "toHexString") => {
                let val = self.encode_operand(args.first()?);
                let result = self.unsigned_bv_to_hex_str(val, 32);
                Some((one, Some(result)))
            }
            ("java/lang/Long", "toHexString") => {
                let val = self.encode_operand(args.first()?);
                let result = self.unsigned_bv_to_hex_str(val, 64);
                Some((one, Some(result)))
            }
            // Integer/Long.toBinaryString
            ("java/lang/Integer", "toBinaryString") => {
                let val = self.encode_operand(args.first()?);
                let result = self.unsigned_bv_to_bin_str(val, 32);
                Some((one, Some(result)))
            }
            ("java/lang/Long", "toBinaryString") => {
                let val = self.encode_operand(args.first()?);
                let result = self.unsigned_bv_to_bin_str(val, 64);
                Some((one, Some(result)))
            }
            // Integer/Long.toOctalString
            ("java/lang/Integer", "toOctalString") => {
                let val = self.encode_operand(args.first()?);
                let result = self.unsigned_bv_to_oct_str(val, 32);
                Some((one, Some(result)))
            }
            ("java/lang/Long", "toOctalString") => {
                let val = self.encode_operand(args.first()?);
                let result = self.unsigned_bv_to_oct_str(val, 64);
                Some((one, Some(result)))
            }
            // Integer/Long.toUnsignedString(int/long)
            ("java/lang/Integer", "toUnsignedString") if target.desc.starts_with("(I)") => {
                let val = self.encode_operand(args.first()?);
                let result = self.unsigned_bv_to_str(val, 32);
                Some((one, Some(result)))
            }
            ("java/lang/Long", "toUnsignedString") if target.desc.starts_with("(J)") => {
                let val = self.encode_operand(args.first()?);
                let result = self.unsigned_bv_to_str(val, 64);
                Some((one, Some(result)))
            }
            // Short/Byte.toString
            ("java/lang/Short" | "java/lang/Byte", "toString")
                if target.desc.contains(")Ljava/lang/String;") =>
            {
                let val = if target.desc == "()Ljava/lang/String;" {
                    let recv = self.encode_operand(args.first()?);
                    let fk = (
                        target.class.clone(),
                        "$$value".to_string(),
                        "I".to_string(),
                    );
                    let arr = self.get_field_array(&fk, 32);
                    self.solver.array_select(arr, recv)
                } else {
                    self.encode_operand(args.first()?)
                };
                let result = self.signed_bv_to_str(val, 32);
                Some((one, Some(result)))
            }
            // Character.toString(char)
            ("java/lang/Character", "toString")
                if target.desc.contains(")Ljava/lang/String;") =>
            {
                let s = self.solver.fresh_str("char_str");
                let len = self.solver.str_len(s);
                let one_int = self.solver.int_const(1);
                let len_eq = self.solver.bveq(len, one_int);
                self.solver.assert(len_eq);
                Some((one, Some(s)))
            }
            // String.valueOf(int/long/boolean/char)
            ("java/lang/String", "valueOf")
                if !target.desc.starts_with("(L") && !target.desc.starts_with("([") =>
            {
                let val = self.encode_operand(args.first()?);
                if target.desc.starts_with("(Z)") {
                    let zero = self.solver.bv_const(0, 32);
                    let eq = self.solver.bveq(val, zero);
                    let is_nz = self.solver.not(eq);
                    let s_true = self.solver.str_const("true");
                    let s_false = self.solver.str_const("false");
                    let result = self.solver.ite(is_nz, s_true, s_false);
                    Some((one, Some(result)))
                } else if target.desc.starts_with("(C)") {
                    let s = self.solver.fresh_str("char_str");
                    let len = self.solver.str_len(s);
                    let one_int = self.solver.int_const(1);
                    let len_eq = self.solver.bveq(len, one_int);
                    self.solver.assert(len_eq);
                    Some((one, Some(s)))
                } else {
                    let w = if target.desc.starts_with("(J)") { 64 } else { 32 };
                    let result = self.signed_bv_to_str(val, w);
                    Some((one, Some(result)))
                }
            }
            _ => None,
        }
    }
}
