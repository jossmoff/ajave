//! SMT encoding for Character utility methods (isDigit, isLetter, etc.).

use ajave_core::smt::Term;
use ajave_ir::*;

use super::ExploreCtx;

impl<'a> ExploreCtx<'a> {
    pub(super) fn is_char_or_wrapper_util(&self, class: &str, name: &str) -> bool {
        match class {
            "java/lang/Character" => matches!(
                name,
                "isDigit" | "isLetter" | "isLetterOrDigit"
                    | "isUpperCase" | "isLowerCase" | "isWhitespace" | "isSpaceChar"
                    | "isAlphabetic" | "isBmpCodePoint"
                    | "toUpperCase" | "toLowerCase" | "toTitleCase"
                    | "charCount" | "isValidCodePoint"
                    | "isSupplementaryCodePoint" | "isISOControl"
                    | "isJavaIdentifierStart" | "isJavaIdentifierPart"
                    | "isJavaLetter" | "isJavaLetterOrDigit"
                    | "isSpace"
                    | "toCodePoint" | "digit" | "forDigit"
                    | "getType" | "isDefined" | "isMirrored" | "isTitleCase"
                    | "isUnicodeIdentifierPart" | "isUnicodeIdentifierStart"
                    | "isIdentifierIgnorable" | "getDirectionality"
                    | "getNumericValue" | "isIdeographic"
            ),
            _ => false,
        }
    }

    pub(super) fn encode_char_wrapper_call(&mut self, class: &str, name: &str, args: &[Operand]) -> Term {
        let one = self.solver.bv_const(1, 32);
        let zero = self.solver.bv_const(0, 32);

        // Constrain char arguments to ASCII range for classification methods
        // where our model is only sound for ASCII. This ensures witnesses are
        // replayable on the JVM. Non-classification methods (toCodePoint,
        // charCount, etc.) work for the full range.
        let is_classification = matches!(name,
            "isDigit" | "isLetter" | "isLetterOrDigit" | "isUpperCase" | "isLowerCase"
            | "isWhitespace" | "isSpaceChar" | "isAlphabetic" | "isSpace"
            | "isJavaIdentifierStart" | "isJavaIdentifierPart"
            | "isJavaLetter" | "isJavaLetterOrDigit"
        );
        if is_classification {
            for arg in args {
                let a = self.encode_operand(arg);
                let hi = self.solver.bv_const(127, 32);
                let in_range = self.solver.bvsle(a, hi);
                let ge_zero = self.solver.bvsge(a, zero);
                let ok = self.solver.and(in_range, ge_zero);
                self.solver.assert(ok);
            }
        }

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
                // ASCII: if 'a' <= c <= 'z', return c - 32; else return c
                let c = self.encode_operand(&args[0]);
                let a_lo = self.solver.bv_const(b'a' as i64, 32);
                let z_hi = self.solver.bv_const(b'z' as i64, 32);
                let ge_a = self.solver.bvsge(c, a_lo);
                let le_z = self.solver.bvsle(c, z_hi);
                let is_lower = self.solver.and(ge_a, le_z);
                let offset = self.solver.bv_const(32, 32);
                let upper = self.solver.bvsub(c, offset);
                self.solver.ite(is_lower, upper, c)
            }
            ("java/lang/Character", "toLowerCase") => {
                // ASCII: if 'A' <= c <= 'Z', return c + 32; else return c
                let c = self.encode_operand(&args[0]);
                let a_up = self.solver.bv_const(b'A' as i64, 32);
                let z_up = self.solver.bv_const(b'Z' as i64, 32);
                let ge_a = self.solver.bvsge(c, a_up);
                let le_z = self.solver.bvsle(c, z_up);
                let is_upper = self.solver.and(ge_a, le_z);
                let offset = self.solver.bv_const(32, 32);
                let lower = self.solver.bvadd(c, offset);
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
                // Constrain radix to valid range [2, 36]
                let two = self.solver.bv_const(2, 32);
                let thirtysix = self.solver.bv_const(36, 32);
                let radix_ge2 = self.solver.bvsge(radix, two);
                let radix_le36 = self.solver.bvsle(radix, thirtysix);
                let radix_ok = self.solver.and(radix_ge2, radix_le36);
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
                let ok = self.solver.and(ok, radix_ok);
                let neg1b = self.solver.bv_const(-1, 32);
                self.solver.ite(ok, v3, neg1b)
            }
            // isSpace (deprecated) — true for \t \n \f \r ' '
            ("java/lang/Character", "isSpace") => {
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
            ("java/lang/Character", "toTitleCase") => {
                // ASCII titleCase == toUpperCase
                let c = self.encode_operand(&args[0]);
                let a_lo = self.solver.bv_const(b'a' as i64, 32);
                let z_hi = self.solver.bv_const(b'z' as i64, 32);
                let ge_a = self.solver.bvsge(c, a_lo);
                let le_z = self.solver.bvsle(c, z_hi);
                let is_lower = self.solver.and(ge_a, le_z);
                let offset = self.solver.bv_const(32, 32);
                let upper = self.solver.bvsub(c, offset);
                self.solver.ite(is_lower, upper, c)
            }
            ("java/lang/Character", "forDigit") => {
                let d = self.encode_operand(&args[0]);
                let radix = self.encode_operand(&args[1]);
                let two = self.solver.bv_const(2, 32);
                let thirtysix = self.solver.bv_const(36, 32);
                let radix_ge2 = self.solver.bvsge(radix, two);
                let radix_le36 = self.solver.bvsle(radix, thirtysix);
                let radix_ok = self.solver.and(radix_ge2, radix_le36);
                let in_range = self.solver.bvslt(d, radix);
                let ge_zero = self.solver.bvsge(d, zero);
                let digit_ok = self.solver.and(in_range, ge_zero);
                let valid = self.solver.and(digit_ok, radix_ok);
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
            ("java/lang/Character", "getType") => {
                self.encode_get_type(&args[0])
            }
            ("java/lang/Character", "isDefined") => {
                // Defined: 0x0000-0xFFFD (BMP minus surrogates/nonchars)
                // Undefined: negative, surrogates (0xD800-0xDFFF), nonchars (0xFFFE-0xFFFF), > 0x10FFFF
                let c = self.encode_operand(&args[0]);
                let ge0 = self.solver.bvsge(c, zero);
                let max_cp = self.solver.bv_const(0x10FFFF, 32);
                let le_max = self.solver.bvsle(c, max_cp);
                let valid_range = self.solver.and(ge0, le_max);
                // Exclude surrogates
                let surr_lo = self.solver.bv_const(0xD800, 32);
                let surr_hi = self.solver.bv_const(0xDFFF, 32);
                let ge_surr = self.solver.bvsge(c, surr_lo);
                let le_surr = self.solver.bvsle(c, surr_hi);
                let is_surr = self.solver.and(ge_surr, le_surr);
                let not_surr = self.solver.not(is_surr);
                // Exclude 0xFFFE-0xFFFF
                let nc_lo = self.solver.bv_const(0xFFFE, 32);
                let nc_hi = self.solver.bv_const(0xFFFF, 32);
                let ge_nc = self.solver.bvsge(c, nc_lo);
                let le_nc = self.solver.bvsle(c, nc_hi);
                let is_nc = self.solver.and(ge_nc, le_nc);
                let not_nc = self.solver.not(is_nc);
                let defined = self.solver.and(valid_range, not_surr);
                let defined = self.solver.and(defined, not_nc);
                self.solver.ite(defined, one, zero)
            }
            ("java/lang/Character", "isMirrored") => {
                let c = self.encode_operand(&args[0]);
                let v_lp = self.solver.bv_const(b'(' as i64, 32);
                let v_rp = self.solver.bv_const(b')' as i64, 32);
                let v_lb = self.solver.bv_const(b'[' as i64, 32);
                let v_rb = self.solver.bv_const(b']' as i64, 32);
                let v_lc = self.solver.bv_const(b'{' as i64, 32);
                let v_rc = self.solver.bv_const(b'}' as i64, 32);
                let v_lt = self.solver.bv_const(b'<' as i64, 32);
                let v_gt = self.solver.bv_const(b'>' as i64, 32);
                let lp = self.solver.bveq(c, v_lp);
                let rp = self.solver.bveq(c, v_rp);
                let lb = self.solver.bveq(c, v_lb);
                let rb = self.solver.bveq(c, v_rb);
                let lc = self.solver.bveq(c, v_lc);
                let rc = self.solver.bveq(c, v_rc);
                let lt = self.solver.bveq(c, v_lt);
                let gt = self.solver.bveq(c, v_gt);
                let r1 = self.solver.or(lp, rp);
                let r2 = self.solver.or(lb, rb);
                let r3 = self.solver.or(lc, rc);
                let r4 = self.solver.or(lt, gt);
                let r12 = self.solver.or(r1, r2);
                let r34 = self.solver.or(r3, r4);
                let result = self.solver.or(r12, r34);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isTitleCase") => {
                // Unicode titlecase chars: DŽ=0x01C5, LJ=0x01C8, NJ=0x01CB, Dz=0x01F2
                let c = self.encode_operand(&args[0]);
                let t1 = self.bv_eq_char(c, 0xC5); // Would need 16-bit but using bv_const
                let v1 = self.solver.bv_const(0x01C5, 32);
                let v2 = self.solver.bv_const(0x01C8, 32);
                let v3 = self.solver.bv_const(0x01CB, 32);
                let v4 = self.solver.bv_const(0x01F2, 32);
                let eq1 = self.solver.bveq(c, v1);
                let eq2 = self.solver.bveq(c, v2);
                let eq3 = self.solver.bveq(c, v3);
                let eq4 = self.solver.bveq(c, v4);
                let r12 = self.solver.or(eq1, eq2);
                let r34 = self.solver.or(eq3, eq4);
                let result = self.solver.or(r12, r34);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "isIdeographic") => {
                // CJK Unified Ideographs: 0x4E00-0x9FFF
                let c = self.encode_operand(&args[0]);
                let is_cjk = self.bv_in_range(c, 0x4E00, 0x9FFF);
                self.solver.ite(is_cjk, one, zero)
            }
            ("java/lang/Character", "isUnicodeIdentifierStart") => {
                let c = self.encode_operand(&args[0]);
                self.encode_is_alpha(c, one, zero)
            }
            ("java/lang/Character", "isUnicodeIdentifierPart") => {
                let c = self.encode_operand(&args[0]);
                let is_alpha = self.encode_is_alpha(c, one, zero);
                let d_lo = self.solver.bv_const(b'0' as i64, 32);
                let d_hi = self.solver.bv_const(b'9' as i64, 32);
                let ge_d = self.solver.bvsge(c, d_lo);
                let le_d = self.solver.bvsle(c, d_hi);
                let is_dig = self.solver.and(ge_d, le_d);
                let und = self.solver.bv_const(b'_' as i64, 32);
                let is_und = self.solver.bveq(c, und);
                let r1 = self.solver.bveq(is_alpha, one);
                let r2 = self.solver.or(r1, is_dig);
                let r3 = self.solver.or(r2, is_und);
                let ctrl_hi2 = self.solver.bv_const(0x08, 32);
                let ge_ctrl = self.solver.bvsge(c, zero);
                let le_ctrl = self.solver.bvsle(c, ctrl_hi2);
                let ctrl1 = self.solver.and(ge_ctrl, le_ctrl);
                let r4 = self.solver.or(r3, ctrl1);
                self.solver.ite(r4, one, zero)
            }
            ("java/lang/Character", "isIdentifierIgnorable") => {
                let c = self.encode_operand(&args[0]);
                let r1_hi = self.solver.bv_const(0x08, 32);
                let ge1 = self.solver.bvsge(c, zero);
                let le1 = self.solver.bvsle(c, r1_hi);
                let range1 = self.solver.and(ge1, le1);
                let r2_lo = self.solver.bv_const(0x0E, 32);
                let r2_hi = self.solver.bv_const(0x1B, 32);
                let ge2 = self.solver.bvsge(c, r2_lo);
                let le2 = self.solver.bvsle(c, r2_hi);
                let range2 = self.solver.and(ge2, le2);
                let r3_lo = self.solver.bv_const(0x7F, 32);
                let r3_hi = self.solver.bv_const(0x9F, 32);
                let ge3 = self.solver.bvsge(c, r3_lo);
                let le3 = self.solver.bvsle(c, r3_hi);
                let range3 = self.solver.and(ge3, le3);
                let r12 = self.solver.or(range1, range2);
                let result = self.solver.or(r12, range3);
                self.solver.ite(result, one, zero)
            }
            ("java/lang/Character", "getDirectionality") => {
                self.encode_get_directionality(&args[0])
            }
            ("java/lang/Character", "getNumericValue") => {
                self.encode_get_numeric_value(&args[0])
            }
            _ => self.solver.fresh_bv("char_hv", 32),
        }
    }

    pub(super) fn encode_is_alpha(&mut self, c: Term, one: Term, zero: Term) -> Term {
        // ASCII A-Z
        let lo_u = self.solver.bv_const(0x41, 32);
        let hi_u = self.solver.bv_const(0x5A, 32);
        let ge_u = self.solver.bvsge(c, lo_u);
        let le_u = self.solver.bvsle(c, hi_u);
        let upper = self.solver.and(ge_u, le_u);
        // ASCII a-z
        let lo_l = self.solver.bv_const(0x61, 32);
        let hi_l = self.solver.bv_const(0x7A, 32);
        let ge_l = self.solver.bvsge(c, lo_l);
        let le_l = self.solver.bvsle(c, hi_l);
        let lower = self.solver.and(ge_l, le_l);
        // Latin-1 Supplement: À-Ö (0xC0-0xD6)
        let lo_l1a = self.solver.bv_const(0xC0, 32);
        let hi_l1a = self.solver.bv_const(0xD6, 32);
        let ge_l1a = self.solver.bvsge(c, lo_l1a);
        let le_l1a = self.solver.bvsle(c, hi_l1a);
        let latin1a = self.solver.and(ge_l1a, le_l1a);
        // Latin-1 Supplement: Ø-ö (0xD8-0xF6)
        let lo_l1b = self.solver.bv_const(0xD8, 32);
        let hi_l1b = self.solver.bv_const(0xF6, 32);
        let ge_l1b = self.solver.bvsge(c, lo_l1b);
        let le_l1b = self.solver.bvsle(c, hi_l1b);
        let latin1b = self.solver.and(ge_l1b, le_l1b);
        // Latin-1 Supplement: ø-ÿ (0xF8-0xFF)
        let lo_l1c = self.solver.bv_const(0xF8, 32);
        let hi_l1c = self.solver.bv_const(0xFF, 32);
        let ge_l1c = self.solver.bvsge(c, lo_l1c);
        let le_l1c = self.solver.bvsle(c, hi_l1c);
        let latin1c = self.solver.and(ge_l1c, le_l1c);
        // Combine all ranges
        let r1 = self.solver.or(upper, lower);
        let r2 = self.solver.or(r1, latin1a);
        let r3 = self.solver.or(r2, latin1b);
        let result = self.solver.or(r3, latin1c);
        self.solver.ite(result, one, zero)
    }

    /// Helper: BV range check [lo, hi] inclusive
    fn bv_in_range(&mut self, c: Term, lo: i64, hi: i64) -> Term {
        let lo_t = self.solver.bv_const(lo, 32);
        let hi_t = self.solver.bv_const(hi, 32);
        let ge = self.solver.bvsge(c, lo_t);
        let le = self.solver.bvsle(c, hi_t);
        self.solver.and(ge, le)
    }

    /// Helper: check if c equals a char literal
    fn bv_eq_char(&mut self, c: Term, ch: u8) -> Term {
        let v = self.solver.bv_const(ch as i64, 32);
        self.solver.bveq(c, v)
    }

    /// Helper: OR a slice of bool terms together
    fn or_chain(&mut self, terms: &[Term]) -> Term {
        let mut r = terms[0];
        for t in &terms[1..] {
            r = self.solver.or(r, *t);
        }
        r
    }

    fn encode_get_type(&mut self, arg: &Operand) -> Term {
        let c = self.encode_operand(arg);
        let zero = self.solver.bv_const(0, 32);
        // Category constants
        let upper_letter = self.solver.bv_const(1, 32);
        let lower_letter = self.solver.bv_const(2, 32);
        let titlecase_letter = self.solver.bv_const(3, 32);
        let other_letter = self.solver.bv_const(5, 32);
        let digit_num = self.solver.bv_const(9, 32);
        let space_sep = self.solver.bv_const(12, 32);
        let control = self.solver.bv_const(15, 32);
        let dash_punct = self.solver.bv_const(20, 32);
        let start_punct = self.solver.bv_const(21, 32);
        let end_punct = self.solver.bv_const(22, 32);
        let connector_punct = self.solver.bv_const(23, 32);
        let other_punct = self.solver.bv_const(24, 32);
        let math_sym = self.solver.bv_const(25, 32);
        let currency_sym = self.solver.bv_const(26, 32);
        let modifier_sym = self.solver.bv_const(27, 32);
        let unassigned = self.solver.bv_const(0, 32);

        let is_upper = self.bv_in_range(c, b'A' as i64, b'Z' as i64);
        let is_lower = self.bv_in_range(c, b'a' as i64, b'z' as i64);
        let is_digit = self.bv_in_range(c, b'0' as i64, b'9' as i64);
        let is_space = self.bv_eq_char(c, b' ');
        let is_ctrl1 = self.bv_in_range(c, 0, 0x1F);
        let is_del = self.bv_eq_char(c, 0x7F);
        let is_ctrl = self.solver.or(is_ctrl1, is_del);
        let is_dash = self.bv_eq_char(c, b'-');
        let s1 = self.bv_eq_char(c, b'(');
        let s2 = self.bv_eq_char(c, b'[');
        let s3 = self.bv_eq_char(c, b'{');
        let is_start = self.or_chain(&[s1, s2, s3]);
        let e1 = self.bv_eq_char(c, b')');
        let e2 = self.bv_eq_char(c, b']');
        let e3 = self.bv_eq_char(c, b'}');
        let is_end = self.or_chain(&[e1, e2, e3]);
        let is_conn = self.bv_eq_char(c, b'_');
        let m1 = self.bv_eq_char(c, b'+');
        let m2 = self.bv_eq_char(c, b'<');
        let m3 = self.bv_eq_char(c, b'=');
        let m4 = self.bv_eq_char(c, b'>');
        let m5 = self.bv_eq_char(c, b'|');
        let m6 = self.bv_eq_char(c, b'~');
        let m7 = self.bv_eq_char(c, b'^');
        let is_math = self.or_chain(&[m1, m2, m3, m4, m5, m6, m7]);
        let is_dollar = self.bv_eq_char(c, b'$');
        let is_mod = self.bv_eq_char(c, b'`');

        // Unicode ranges beyond ASCII
        let is_cjk = self.bv_in_range(c, 0x4E00, 0x9FFF);  // CJK Unified Ideographs (OTHER_LETTER)
        let is_latin_ext = self.bv_in_range(c, 0x00C0, 0x00FF); // Latin-1 Supplement letters
        // Titlecase chars: DŽ=0x01C5, LJ=0x01C8, NJ=0x01CB, Dz=0x01F2
        let tc1 = self.solver.bv_const(0x01C5, 32);
        let tc2 = self.solver.bv_const(0x01C8, 32);
        let tc3 = self.solver.bv_const(0x01CB, 32);
        let tc4 = self.solver.bv_const(0x01F2, 32);
        let is_tc1 = self.solver.bveq(c, tc1);
        let is_tc2 = self.solver.bveq(c, tc2);
        let is_tc3 = self.solver.bveq(c, tc3);
        let is_tc4 = self.solver.bveq(c, tc4);
        let tc12 = self.solver.or(is_tc1, is_tc2);
        let tc34 = self.solver.or(is_tc3, is_tc4);
        let is_titlecase = self.solver.or(tc12, tc34);

        // Build ITE chain
        let r = self.solver.ite(is_upper, upper_letter, unassigned);
        let r = self.solver.ite(is_lower, lower_letter, r);
        let r = self.solver.ite(is_digit, digit_num, r);
        let r = self.solver.ite(is_space, space_sep, r);
        let r = self.solver.ite(is_ctrl, control, r);
        let r = self.solver.ite(is_dash, dash_punct, r);
        let r = self.solver.ite(is_start, start_punct, r);
        let r = self.solver.ite(is_end, end_punct, r);
        let r = self.solver.ite(is_conn, connector_punct, r);
        let r = self.solver.ite(is_math, math_sym, r);
        let r = self.solver.ite(is_dollar, currency_sym, r);
        let r = self.solver.ite(is_mod, modifier_sym, r);
        // Unicode categories
        let r = self.solver.ite(is_cjk, other_letter, r);
        let r = self.solver.ite(is_titlecase, titlecase_letter, r);
        // Latin-1 supplement: approximate as upper/lower based on case
        // (0xC0-0xD6 upper, 0xD8-0xDE upper, 0xDF-0xF6 lower, 0xF8-0xFF lower)
        let is_lat_upper = self.bv_in_range(c, 0xC0, 0xDE);
        let is_lat_lower = self.bv_in_range(c, 0xDF, 0xFF);
        let r = self.solver.ite(is_lat_upper, upper_letter, r);
        let r = self.solver.ite(is_lat_lower, lower_letter, r);
        // Remaining ASCII printable → OTHER_PUNCTUATION
        let is_printable = self.bv_in_range(c, 0x21, 0x7E);
        let is_already = self.or_chain(&[
            is_upper, is_lower, is_digit, is_dash, is_start, is_end,
            is_conn, is_math, is_dollar, is_mod,
        ]);
        let not_already = self.solver.not(is_already);
        let is_other_punct = self.solver.and(is_printable, not_already);
        self.solver.ite(is_other_punct, other_punct, r)
    }

    fn encode_get_directionality(&mut self, arg: &Operand) -> Term {
        let c = self.encode_operand(arg);
        let l_dir = self.solver.bv_const(0, 32);   // LEFT_TO_RIGHT
        let en_dir = self.solver.bv_const(3, 32);   // EUROPEAN_NUMBER
        let es_dir = self.solver.bv_const(4, 32);   // EUROPEAN_NUMBER_SEPARATOR
        let et_dir = self.solver.bv_const(5, 32);   // EUROPEAN_NUMBER_TERMINATOR
        let cs_dir = self.solver.bv_const(6, 32);   // COMMON_NUMBER_SEPARATOR
        let ps_dir = self.solver.bv_const(8, 32);   // PARAGRAPH_SEPARATOR
        let ss_dir = self.solver.bv_const(9, 32);   // SEGMENT_SEPARATOR
        let ws_dir = self.solver.bv_const(12, 32);  // WHITESPACE
        let on_dir = self.solver.bv_const(13, 32);  // OTHER_NEUTRALS
        let bn_dir = self.solver.bv_const(18, 32);  // BOUNDARY_NEUTRAL
        let undef = self.solver.bv_const(-1_i64, 32); // UNDEFINED: -1 as signed byte → -1 as signed int
        let is_upper = self.bv_in_range(c, b'A' as i64, b'Z' as i64);
        let is_lower = self.bv_in_range(c, b'a' as i64, b'z' as i64);
        let is_digit = self.bv_in_range(c, b'0' as i64, b'9' as i64);
        let is_alpha = self.solver.or(is_upper, is_lower);
        // Default: UNDEFINED for non-ASCII, ON for ASCII misc
        let is_ascii = self.bv_in_range(c, 0, 0x7F);
        let default_val = self.solver.ite(is_ascii, on_dir, undef);
        let r = self.solver.ite(is_alpha, l_dir, default_val);
        let r = self.solver.ite(is_digit, en_dir, r);
        let is_sp = self.bv_eq_char(c, b' ');
        let r = self.solver.ite(is_sp, ws_dir, r);
        // Tab (0x09) → SEGMENT_SEPARATOR
        let is_tab = self.bv_eq_char(c, 0x09);
        let r = self.solver.ite(is_tab, ss_dir, r);
        // Paragraph separator: 0x0D (CR), 0x0A (LF), 0x1C-0x1E
        let is_cr = self.bv_eq_char(c, 0x0D);
        let is_lf = self.bv_eq_char(c, 0x0A);
        let is_fs = self.bv_in_range(c, 0x1C, 0x1E);
        let is_para = self.or_chain(&[is_cr, is_lf, is_fs]);
        let r = self.solver.ite(is_para, ps_dir, r);
        // Control chars → BN
        let is_ctrl = self.bv_in_range(c, 0, 0x08);
        let is_ctrl2 = self.bv_in_range(c, 0x0E, 0x1B);
        let ctrl = self.solver.or(is_ctrl, is_ctrl2);
        let r = self.solver.ite(ctrl, bn_dir, r);
        // Some punctuation: + is ES(4), $ is ET(5), comma/colon are CS(6)
        let is_plus = self.bv_eq_char(c, b'+');
        let is_minus = self.bv_eq_char(c, b'-');
        let is_es = self.solver.or(is_plus, is_minus);
        let r = self.solver.ite(is_es, es_dir, r);
        let is_dollar = self.bv_eq_char(c, b'$');
        let is_hash = self.bv_eq_char(c, b'#');
        let is_et = self.solver.or(is_dollar, is_hash);
        let r = self.solver.ite(is_et, et_dir, r);
        let is_comma = self.bv_eq_char(c, b',');
        let is_period = self.bv_eq_char(c, b'.');
        let is_colon = self.bv_eq_char(c, b':');
        let is_slash = self.bv_eq_char(c, b'/');
        let cs = self.or_chain(&[is_comma, is_period, is_colon, is_slash]);
        self.solver.ite(cs, cs_dir, r)
    }

    fn encode_get_numeric_value(&mut self, arg: &Operand) -> Term {
        let c = self.encode_operand(arg);
        let neg1 = self.solver.bv_const(-1_i64, 32);
        let ten = self.solver.bv_const(10, 32);
        let is_dig = self.bv_in_range(c, b'0' as i64, b'9' as i64);
        let d_base = self.solver.bv_const(b'0' as i64, 32);
        let dig_val = self.solver.bvsub(c, d_base);
        let is_up = self.bv_in_range(c, b'A' as i64, b'Z' as i64);
        let u_base = self.solver.bv_const(b'A' as i64, 32);
        let u_off = self.solver.bvsub(c, u_base);
        let up_val = self.solver.bvadd(u_off, ten);
        let is_low = self.bv_in_range(c, b'a' as i64, b'z' as i64);
        let l_base = self.solver.bv_const(b'a' as i64, 32);
        let l_off = self.solver.bvsub(c, l_base);
        let low_val = self.solver.bvadd(l_off, ten);
        let r = self.solver.ite(is_dig, dig_val, neg1);
        let r = self.solver.ite(is_up, up_val, r);
        self.solver.ite(is_low, low_val, r)
    }
}
