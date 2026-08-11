//! SMT encoding for Character utility methods (isDigit, isLetter, etc.).

use roast_core::smt::Term;
use roast_ir::*;

use super::ExploreCtx;

impl<'a> ExploreCtx<'a> {
    pub(super) fn is_char_or_wrapper_util(&self, class: &str, name: &str) -> bool {
        match class {
            "java/lang/Character" => matches!(
                name,
                "isDigit" | "isLetter" | "isLetterOrDigit"
                    | "isUpperCase" | "isLowerCase" | "isWhitespace" | "isSpaceChar"
                    | "isAlphabetic" | "isBmpCodePoint"
                    | "toUpperCase" | "toLowerCase"
                    | "charCount" | "isValidCodePoint"
                    | "isSupplementaryCodePoint" | "isISOControl"
                    | "isJavaIdentifierStart" | "isJavaIdentifierPart"
                    | "isJavaLetter" | "isJavaLetterOrDigit"
                    | "toCodePoint" | "digit" | "forDigit"
            ),
            _ => false,
        }
    }

    pub(super) fn encode_char_wrapper_call(&mut self, class: &str, name: &str, args: &[Operand]) -> Term {
        let one = self.solver.bv_const(1, 32);
        let zero = self.solver.bv_const(0, 32);

        match (class, name) {
            ("java/lang/Character", "isDigit") => {
                let c = self.encode_operand(&args[0]);
                let lo = self.solver.bv_const(0x30, 32);
                let hi = self.solver.bv_const(0x39, 32);
                let ge = self.solver.bvsge(c, lo);
                let le = self.solver.bvsle(c, hi);
                let result = self.solver.and(ge, le);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isLetter" | "isAlphabetic") => {
                let c = self.encode_operand(&args[0]);
                self.encode_is_alpha(c, one, zero)
            }
            ("java/lang/Character", "isLetterOrDigit") => {
                let c = self.encode_operand(&args[0]);
                let lo_d = self.solver.bv_const(0x30, 32);
                let hi_d = self.solver.bv_const(0x39, 32);
                let ge_d = self.solver.bvsge(c, lo_d);
                let le_d = self.solver.bvsle(c, hi_d);
                let digit = self.solver.and(ge_d, le_d);
                let alpha = self.encode_is_alpha(c, one, zero);
                let alpha_b = self.solver.bveq(alpha, one);
                let result = self.solver.or(digit, alpha_b);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isUpperCase") => {
                let c = self.encode_operand(&args[0]);
                let lo = self.solver.bv_const(0x41, 32);
                let hi = self.solver.bv_const(0x5A, 32);
                let ge = self.solver.bvsge(c, lo);
                let le = self.solver.bvsle(c, hi);
                let result = self.solver.and(ge, le);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isLowerCase") => {
                let c = self.encode_operand(&args[0]);
                let lo = self.solver.bv_const(0x61, 32);
                let hi = self.solver.bv_const(0x7A, 32);
                let ge = self.solver.bvsge(c, lo);
                let le = self.solver.bvsle(c, hi);
                let result = self.solver.and(ge, le);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isWhitespace") => {
                let c = self.encode_operand(&args[0]);
                let sp = self.solver.bv_const(0x20, 32);
                let is_space = self.solver.bveq(c, sp);
                let tab = self.solver.bv_const(0x09, 32);
                let is_tab = self.solver.bveq(c, tab);
                let nl = self.solver.bv_const(0x0A, 32);
                let is_nl = self.solver.bveq(c, nl);
                let cr = self.solver.bv_const(0x0D, 32);
                let is_cr = self.solver.bveq(c, cr);
                let ff = self.solver.bv_const(0x0C, 32);
                let is_ff = self.solver.bveq(c, ff);
                let r1 = self.solver.or(is_cr, is_ff);
                let r2 = self.solver.or(is_nl, r1);
                let r3 = self.solver.or(is_tab, r2);
                let result = self.solver.or(is_space, r3);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isSpaceChar") => {
                let c = self.encode_operand(&args[0]);
                let sp = self.solver.bv_const(0x20, 32);
                let result = self.solver.bveq(c, sp);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isBmpCodePoint") => {
                let cp = self.encode_operand(&args[0]);
                let hi = self.solver.bv_const(0xFFFF, 32);
                let ge = self.solver.bvsge(cp, zero);
                let le = self.solver.bvsle(cp, hi);
                let result = self.solver.and(ge, le);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isValidCodePoint") => {
                let cp = self.encode_operand(&args[0]);
                let hi = self.solver.bv_const(0x10FFFF, 32);
                let ge = self.solver.bvsge(cp, zero);
                let le = self.solver.bvsle(cp, hi);
                let result = self.solver.and(ge, le);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "toUpperCase") => {
                let c = self.encode_operand(&args[0]);
                let lo = self.solver.bv_const(0x61, 32);
                let hi = self.solver.bv_const(0x7A, 32);
                let ge = self.solver.bvsge(c, lo);
                let le = self.solver.bvsle(c, hi);
                let is_lower = self.solver.and(ge, le);
                let delta = self.solver.bv_const(0x20, 32);
                let upper = self.solver.bvsub(c, delta);
                self.solver.ite(is_lower, upper, c)
            }
            ("java/lang/Character", "toLowerCase") => {
                let c = self.encode_operand(&args[0]);
                let lo = self.solver.bv_const(0x41, 32);
                let hi = self.solver.bv_const(0x5A, 32);
                let ge = self.solver.bvsge(c, lo);
                let le = self.solver.bvsle(c, hi);
                let is_upper = self.solver.and(ge, le);
                let delta = self.solver.bv_const(0x20, 32);
                let lower = self.solver.bvadd(c, delta);
                self.solver.ite(is_upper, lower, c)
            }
            ("java/lang/Character", "charCount") => {
                let cp = self.encode_operand(&args[0]);
                let threshold = self.solver.bv_const(0x10000, 32);
                let supp = self.solver.bvsge(cp, threshold);
                let two = self.solver.bv_const(2, 32);
                self.solver.ite(supp, two, one)
            }
            ("java/lang/Character", "isSupplementaryCodePoint") => {
                let cp = self.encode_operand(&args[0]);
                let lo = self.solver.bv_const(0x10000, 32);
                let hi = self.solver.bv_const(0x10FFFF, 32);
                let ge = self.solver.bvsge(cp, lo);
                let le = self.solver.bvsle(cp, hi);
                let result = self.solver.and(ge, le);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isISOControl") => {
                let c = self.encode_operand(&args[0]);
                let hi1 = self.solver.bv_const(0x1F, 32);
                let ge0 = self.solver.bvsge(c, zero);
                let le1 = self.solver.bvsle(c, hi1);
                let range1 = self.solver.and(ge0, le1);
                let lo2 = self.solver.bv_const(0x7F, 32);
                let hi2 = self.solver.bv_const(0x9F, 32);
                let ge2 = self.solver.bvsge(c, lo2);
                let le2 = self.solver.bvsle(c, hi2);
                let range2 = self.solver.and(ge2, le2);
                let result = self.solver.or(range1, range2);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isJavaLetter" | "isJavaIdentifierStart") => {
                let c = self.encode_operand(&args[0]);
                let alpha = self.encode_is_alpha(c, one, zero);
                let alpha_b = self.solver.bveq(alpha, one);
                let dollar = self.solver.bv_const(0x24, 32);
                let is_dollar = self.solver.bveq(c, dollar);
                let underscore = self.solver.bv_const(0x5F, 32);
                let is_under = self.solver.bveq(c, underscore);
                let r = self.solver.or(alpha_b, is_dollar);
                let result = self.solver.or(r, is_under);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isJavaLetterOrDigit" | "isJavaIdentifierPart") => {
                let c = self.encode_operand(&args[0]);
                let alpha = self.encode_is_alpha(c, one, zero);
                let alpha_b = self.solver.bveq(alpha, one);
                let lo_d = self.solver.bv_const(0x30, 32);
                let hi_d = self.solver.bv_const(0x39, 32);
                let ge_d = self.solver.bvsge(c, lo_d);
                let le_d = self.solver.bvsle(c, hi_d);
                let digit = self.solver.and(ge_d, le_d);
                let dollar = self.solver.bv_const(0x24, 32);
                let is_dollar = self.solver.bveq(c, dollar);
                let underscore = self.solver.bv_const(0x5F, 32);
                let is_under = self.solver.bveq(c, underscore);
                let r1 = self.solver.or(alpha_b, digit);
                let r2 = self.solver.or(r1, is_dollar);
                let result = self.solver.or(r2, is_under);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "toCodePoint") => {
                let high = self.encode_operand(&args[0]);
                let low = self.encode_operand(&args[1]);
                let d800 = self.solver.bv_const(0xD800, 32);
                let dc00 = self.solver.bv_const(0xDC00, 32);
                let x400 = self.solver.bv_const(0x400, 32);
                let x10000 = self.solver.bv_const(0x10000, 32);
                let h = self.solver.bvsub(high, d800);
                let l = self.solver.bvsub(low, dc00);
                let hh = self.solver.bvmul(h, x400);
                let hl = self.solver.bvadd(hh, l);
                self.solver.bvadd(hl, x10000)
            }
            ("java/lang/Character", "digit") => {
                let c = self.encode_operand(&args[0]);
                let radix = self.encode_operand(&args[1]);
                let c0 = self.solver.bv_const(0x30, 32);
                let c9 = self.solver.bv_const(0x39, 32);
                let ca = self.solver.bv_const(0x61, 32);
                let cb = self.solver.bv_const(0x41, 32);
                let dval = self.solver.bvsub(c, c0);
                let ge0 = self.solver.bvsge(c, c0);
                let le9 = self.solver.bvsle(c, c9);
                let is_num = self.solver.and(ge0, le9);
                let dval_a = self.solver.bvsub(c, ca);
                let ten = self.solver.bv_const(10, 32);
                let dval_al = self.solver.bvadd(dval_a, ten);
                let za = self.solver.bv_const(0x7A, 32);
                let ge_a = self.solver.bvsge(c, ca);
                let le_a = self.solver.bvsle(c, za);
                let is_lower = self.solver.and(ge_a, le_a);
                let dval_b = self.solver.bvsub(c, cb);
                let dval_bu = self.solver.bvadd(dval_b, ten);
                let zb = self.solver.bv_const(0x5A, 32);
                let ge_b = self.solver.bvsge(c, cb);
                let le_b = self.solver.bvsle(c, zb);
                let is_upper = self.solver.and(ge_b, le_b);
                let neg1 = self.solver.bv_const(-1, 32);
                let v1 = self.solver.ite(is_num, dval, neg1);
                let v2 = self.solver.ite(is_lower, dval_al, v1);
                let v3 = self.solver.ite(is_upper, dval_bu, v2);
                let in_range = self.solver.bvslt(v3, radix);
                let valid = self.solver.bvsge(v3, zero);
                let ok = self.solver.and(in_range, valid);
                let neg1b = self.solver.bv_const(-1, 32);
                self.solver.ite(ok, v3, neg1b)
            }
            ("java/lang/Character", "forDigit") => {
                let d = self.encode_operand(&args[0]);
                let radix = self.encode_operand(&args[1]);
                let in_range = self.solver.bvslt(d, radix);
                let ge_zero = self.solver.bvsge(d, zero);
                let valid = self.solver.and(in_range, ge_zero);
                let ten = self.solver.bv_const(10, 32);
                let is_digit = self.solver.bvslt(d, ten);
                let c0 = self.solver.bv_const(0x30, 32);
                let ca = self.solver.bv_const(0x61, 32);
                let d_sub_10 = self.solver.bvsub(d, ten);
                let as_digit = self.solver.bvadd(d, c0);
                let as_letter = self.solver.bvadd(d_sub_10, ca);
                let ch = self.solver.ite(is_digit, as_digit, as_letter);
                self.solver.ite(valid, ch, zero)
            }
            _ => self.solver.fresh_bv("char_hv", 32),
        }
    }

    pub(super) fn encode_is_alpha(&mut self, c: Term, one: Term, zero: Term) -> Term {
        let lo_u = self.solver.bv_const(0x41, 32);
        let hi_u = self.solver.bv_const(0x5A, 32);
        let ge_u = self.solver.bvsge(c, lo_u);
        let le_u = self.solver.bvsle(c, hi_u);
        let upper = self.solver.and(ge_u, le_u);
        let lo_l = self.solver.bv_const(0x61, 32);
        let hi_l = self.solver.bv_const(0x7A, 32);
        let ge_l = self.solver.bvsge(c, lo_l);
        let le_l = self.solver.bvsle(c, hi_l);
        let lower = self.solver.and(ge_l, le_l);
        let result = self.solver.or(upper, lower);
        self.solver.ite(result, one, zero)
    }
}
