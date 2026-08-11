//! SMT encoding for Math, Integer, Long, Short, Byte wrapper method calls.

use roast_core::smt::Term;
use roast_ir::*;

use super::ExploreCtx;

impl<'a> ExploreCtx<'a> {
    /// Returns true only for methods that have a precise SMT encoding in
    /// `encode_math_call`. Methods listed here MUST have a corresponding arm
    /// in that function — otherwise they'd get `fresh_bv` (unconstrained but
    /// untainted), which causes spurious violations.
    pub(super) fn math_call_modelled(&self, target: &MethodKey) -> bool {
        match target.class.as_str() {
            "java/lang/Math" | "java/lang/StrictMath" => matches!(
                target.name.as_str(),
                "abs" | "min" | "max" | "addExact" | "subtractExact"
                    | "multiplyExact" | "negateExact" | "floorDiv" | "floorMod"
            ),
            "java/lang/Integer" => matches!(
                target.name.as_str(),
                "parseInt" | "max" | "min" | "sum"
                    | "signum" | "toUnsignedLong"
                    | "divideUnsigned" | "remainderUnsigned" | "compareUnsigned"
                    | "compare" | "compareTo" | "hashCode"
                    | "reverseBytes" | "highestOneBit" | "lowestOneBit"
                    | "rotateLeft" | "rotateRight"
                    | "bitCount" | "numberOfLeadingZeros" | "numberOfTrailingZeros"
                    | "reverse"
            ),
            "java/lang/Long" => matches!(
                target.name.as_str(),
                "parseLong" | "max" | "min" | "sum" | "signum"
                    | "divideUnsigned" | "remainderUnsigned" | "compareUnsigned"
                    | "compare" | "compareTo" | "hashCode"
                    | "reverseBytes" | "highestOneBit" | "lowestOneBit"
                    | "rotateLeft" | "rotateRight"
                    | "bitCount" | "numberOfLeadingZeros" | "numberOfTrailingZeros"
                    | "reverse"
            ),
            "java/lang/Short" => matches!(
                target.name.as_str(),
                "parseShort" | "compare" | "hashCode" | "reverseBytes" | "toUnsignedInt" | "toUnsignedLong"
            ),
            "java/lang/Byte" => matches!(
                target.name.as_str(),
                "parseByte" | "compare" | "hashCode" | "toUnsignedInt" | "toUnsignedLong"
            ),
            "java/lang/Character" => {
                self.is_char_or_wrapper_util(&target.class, &target.name)
                    || matches!(target.name.as_str(), "compare" | "hashCode" | "reverseBytes")
            }
            "java/lang/Boolean" => matches!(
                target.name.as_str(),
                "compareTo" | "hashCode"
            ),
            _ => false,
        }
    }

    pub(super) fn arg_width_from_desc(desc: &str, idx: usize) -> u32 {
        let inner = &desc[1..desc.find(')').unwrap_or(desc.len())];
        let mut pos = 0;
        let mut arg_idx = 0;
        let bytes = inner.as_bytes();
        while pos < bytes.len() {
            let w = match bytes[pos] {
                b'J' | b'D' => { pos += 1; 64 }
                b'L' => {
                    while pos < bytes.len() && bytes[pos] != b';' { pos += 1; }
                    pos += 1;
                    32
                }
                b'[' => {
                    while pos < bytes.len() && bytes[pos] == b'[' { pos += 1; }
                    if pos < bytes.len() && bytes[pos] == b'L' {
                        while pos < bytes.len() && bytes[pos] != b';' { pos += 1; }
                        pos += 1;
                    } else {
                        pos += 1;
                    }
                    32
                }
                _ => { pos += 1; 32 }
            };
            if arg_idx == idx { return w; }
            arg_idx += 1;
        }
        32
    }

    pub(super) fn encode_math_call(&mut self, target: &MethodKey, args: &[Operand]) -> Term {
        let class = target.class.as_str();
        let name = target.name.as_str();
        let arg0_w = Self::arg_width_from_desc(&target.desc, 0);
        let _arg1_w = Self::arg_width_from_desc(&target.desc, 1);
        match (class, name) {
            // ── Math / StrictMath ────────────────────────────────────────
            ("java/lang/Math" | "java/lang/StrictMath", "abs") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let zero = self.solver.bv_const(0, w);
                let neg = self.solver.bvneg(a);
                let is_neg = self.solver.bvslt(a, zero);
                self.solver.ite(is_neg, neg, a)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "min")
            | ("java/lang/Integer" | "java/lang/Long", "min") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let lt = self.solver.bvslt(a, b);
                self.solver.ite(lt, a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "max")
            | ("java/lang/Integer" | "java/lang/Long", "max") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let gt = self.solver.bvsgt(a, b);
                self.solver.ite(gt, a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "addExact")
            | ("java/lang/Integer" | "java/lang/Long", "sum") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvadd(a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "subtractExact") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsub(a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "multiplyExact") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvmul(a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "negateExact") => {
                let a = self.encode_operand(&args[0]);
                self.solver.bvneg(a)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "floorDiv") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsdiv(a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "floorMod") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsrem(a, b)
            }

            // ── Integer / Long numeric ──────────────────────────────────
            ("java/lang/Integer" | "java/lang/Long", "signum") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let zero = self.solver.bv_const(0, w);
                let one = self.solver.bv_const(1, 32);
                let mone = self.solver.bv_const(-1, 32);
                let zero32 = self.solver.bv_const(0, 32);
                let is_neg = self.solver.bvslt(a, zero);
                let is_zero = self.solver.bveq(a, zero);
                let inner = self.solver.ite(is_zero, zero32, one);
                self.solver.ite(is_neg, mone, inner)
            }
            ("java/lang/Integer", "toUnsignedLong") => {
                let a = self.encode_operand(&args[0]);
                self.solver.zero_extend(a, 32)
            }
            ("java/lang/Integer" | "java/lang/Long", "divideUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsdiv(a, b)
            }
            ("java/lang/Integer" | "java/lang/Long", "remainderUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsrem(a, b)
            }
            ("java/lang/Integer" | "java/lang/Long", "compareUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let w = arg0_w;
                let min_val = self.solver.bv_const(1i64 << (w - 1), w);
                let a_adj = self.solver.bvadd(a, min_val);
                let b_adj = self.solver.bvadd(b, min_val);
                let one = self.solver.bv_const(1, 32);
                let mone = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let lt = self.solver.bvslt(a_adj, b_adj);
                let eq = self.solver.bveq(a, b);
                let inner = self.solver.ite(eq, zero, one);
                self.solver.ite(lt, mone, inner)
            }
            ("java/lang/Integer", "parseInt") | ("java/lang/Long", "parseLong")
            | ("java/lang/Short", "parseShort") | ("java/lang/Byte", "parseByte") => {
                let w = if class == "java/lang/Long" { 64 } else { 32 };
                self.solver.fresh_bv("parse", w)
            }

            // ── compare / compareTo / hashCode ──────────────────────────
            ("java/lang/Integer" | "java/lang/Long", "compare") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let one = self.solver.bv_const(1, 32);
                let mone = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let lt = self.solver.bvslt(a, b);
                let eq = self.solver.bveq(a, b);
                let inner = self.solver.ite(eq, zero, one);
                self.solver.ite(lt, mone, inner)
            }
            ("java/lang/Short" | "java/lang/Byte" | "java/lang/Character", "compare") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsub(a, b)
            }
            ("java/lang/Integer" | "java/lang/Short" | "java/lang/Byte" | "java/lang/Character", "hashCode") => {
                self.encode_operand(&args[0])
            }
            ("java/lang/Long", "hashCode") => {
                let a = self.encode_operand(&args[0]);
                let c32 = self.solver.bv_const(32, 64);
                let shifted = self.solver.bvlshr(a, c32);
                let xored = self.solver.bvxor(a, shifted);
                self.solver.extract(xored, 31, 0)
            }
            ("java/lang/Integer", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = (class.to_string(), "$$value".to_string(), "I".to_string());
                let arr = self.get_field_array(&k, 32);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                let one = self.solver.bv_const(1, 32);
                let mone = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let lt = self.solver.bvslt(a, b);
                let eq = self.solver.bveq(a, b);
                let inner = self.solver.ite(eq, zero, one);
                self.solver.ite(lt, mone, inner)
            }
            ("java/lang/Short" | "java/lang/Byte" | "java/lang/Character", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = (class.to_string(), "$$value".to_string(), "I".to_string());
                let arr = self.get_field_array(&k, 32);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                self.solver.bvsub(a, b)
            }
            ("java/lang/Boolean", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = (class.to_string(), "$$value".to_string(), "I".to_string());
                let arr = self.get_field_array(&k, 32);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                self.solver.bvsub(a, b)
            }
            ("java/lang/Long", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = ("java/lang/Long".to_string(), "$$value".to_string(), "J".to_string());
                let w = 64u32;
                let arr = self.get_field_array(&k, w);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                let one = self.solver.bv_const(1, 32);
                let mone = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let lt = self.solver.bvslt(a, b);
                let eq = self.solver.bveq(a, b);
                let inner = self.solver.ite(eq, zero, one);
                self.solver.ite(lt, mone, inner)
            }

            // ── Bit manipulation ────────────────────────────────────────
            // bitCount: popcount via binary reduction tree.
            // O(log W) depth, narrow additions (2→3→...→6/7 bits).
            ("java/lang/Integer" | "java/lang/Long", "bitCount") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let mut nodes: Vec<_> = (0..w)
                    .map(|i| self.solver.extract(a, i, i))
                    .collect();
                let mut current_width: u32 = 1;
                while nodes.len() > 1 {
                    let mut next = Vec::with_capacity((nodes.len() + 1) / 2);
                    for chunk in nodes.chunks(2) {
                        if chunk.len() == 2 {
                            let l = self.solver.zero_extend(chunk[0], 1);
                            let r = self.solver.zero_extend(chunk[1], 1);
                            next.push(self.solver.bvadd(l, r));
                        } else {
                            next.push(self.solver.zero_extend(chunk[0], 1));
                        }
                    }
                    nodes = next;
                    current_width += 1;
                }
                let count = nodes.into_iter().next().unwrap();
                self.solver.zero_extend(count, 32 - current_width)
            }
            // numberOfTrailingZeros: ITE cascade from LSB
            ("java/lang/Integer" | "java/lang/Long", "numberOfTrailingZeros") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let mut result = self.solver.bv_const(w as i64, 32);
                for i in (0..w).rev() {
                    let bit_mask = self.solver.bv_const(1i64 << i, w);
                    let masked = self.solver.bvand(a, bit_mask);
                    let has_bit = self.solver.bveq(masked, bit_mask);
                    let val = self.solver.bv_const(i as i64, 32);
                    result = self.solver.ite(has_bit, val, result);
                }
                result
            }
            // numberOfLeadingZeros: ITE cascade from MSB
            ("java/lang/Integer" | "java/lang/Long", "numberOfLeadingZeros") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let mut result = self.solver.bv_const(w as i64, 32);
                for i in 0..w {
                    let bit_mask = self.solver.bv_const(1i64 << i, w);
                    let masked = self.solver.bvand(a, bit_mask);
                    let has_bit = self.solver.bveq(masked, bit_mask);
                    let val = self.solver.bv_const((w - 1 - i) as i64, 32);
                    result = self.solver.ite(has_bit, val, result);
                }
                result
            }
            // reverse: reverse all bit positions
            ("java/lang/Integer" | "java/lang/Long", "reverse") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let mut result = self.solver.bv_const(0, w);
                for i in 0..w {
                    let bit = self.solver.extract(a, i, i);
                    let bit_ext = self.solver.zero_extend(bit, w - 1);
                    let shift_amt = self.solver.bv_const((w - 1 - i) as i64, w);
                    let shifted = self.solver.bvshl(bit_ext, shift_amt);
                    result = self.solver.bvor(result, shifted);
                }
                result
            }
            // highestOneBit: ITE cascade from MSB
            ("java/lang/Integer" | "java/lang/Long", "highestOneBit") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let zero = self.solver.bv_const(0, w);
                let is_zero = self.solver.bveq(a, zero);
                let mut result = zero;
                for i in (0..w).rev() {
                    let bit_mask = self.solver.bv_const(1i64 << i, w);
                    let masked = self.solver.bvand(a, bit_mask);
                    let has_bit = self.solver.bveq(masked, bit_mask);
                    result = self.solver.ite(has_bit, bit_mask, result);
                }
                self.solver.ite(is_zero, zero, result)
            }
            // lowestOneBit: val & (-val)
            ("java/lang/Integer" | "java/lang/Long", "lowestOneBit") => {
                let a = self.encode_operand(&args[0]);
                let neg = self.solver.bvneg(a);
                self.solver.bvand(a, neg)
            }
            // rotateLeft
            ("java/lang/Integer" | "java/lang/Long", "rotateLeft") => {
                let a = self.encode_operand(&args[0]);
                let d = self.encode_operand(&args[1]);
                let w = arg0_w;
                let wc = self.solver.bv_const(w as i64, w);
                let d_w = if w == 64 { self.solver.zero_extend(d, 32) } else { d };
                let mask = self.solver.bv_const(w as i64 - 1, w);
                let dist = self.solver.bvand(d_w, mask);
                let complement = self.solver.bvsub(wc, dist);
                let left = self.solver.bvshl(a, dist);
                let right = self.solver.bvlshr(a, complement);
                self.solver.bvor(left, right)
            }
            // rotateRight
            ("java/lang/Integer" | "java/lang/Long", "rotateRight") => {
                let a = self.encode_operand(&args[0]);
                let d = self.encode_operand(&args[1]);
                let w = arg0_w;
                let wc = self.solver.bv_const(w as i64, w);
                let d_w = if w == 64 { self.solver.zero_extend(d, 32) } else { d };
                let mask = self.solver.bv_const(w as i64 - 1, w);
                let dist = self.solver.bvand(d_w, mask);
                let complement = self.solver.bvsub(wc, dist);
                let right = self.solver.bvlshr(a, dist);
                let left = self.solver.bvshl(a, complement);
                self.solver.bvor(right, left)
            }

            // ── Byte-level manipulation ─────────────────────────────────
            ("java/lang/Integer", "reverseBytes") => {
                let a = self.encode_operand(&args[0]);
                let b0 = self.solver.extract(a, 7, 0);
                let b1 = self.solver.extract(a, 15, 8);
                let b2 = self.solver.extract(a, 23, 16);
                let b3 = self.solver.extract(a, 31, 24);
                let b0_ext = self.solver.zero_extend(b0, 24);
                let c24 = self.solver.bv_const(24, 32);
                let r0 = self.solver.bvshl(b0_ext, c24);
                let b1_ext = self.solver.zero_extend(b1, 24);
                let c16 = self.solver.bv_const(16, 32);
                let r1 = self.solver.bvshl(b1_ext, c16);
                let b2_ext = self.solver.zero_extend(b2, 24);
                let c8 = self.solver.bv_const(8, 32);
                let r2 = self.solver.bvshl(b2_ext, c8);
                let b3_ext = self.solver.zero_extend(b3, 24);
                let r01 = self.solver.bvor(r0, r1);
                let r23 = self.solver.bvor(r2, b3_ext);
                self.solver.bvor(r01, r23)
            }
            ("java/lang/Long", "reverseBytes") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFF, 64);
                let c8 = self.solver.bv_const(8, 64);
                let c16 = self.solver.bv_const(16, 64);
                let c24 = self.solver.bv_const(24, 64);
                let c32 = self.solver.bv_const(32, 64);
                let c40 = self.solver.bv_const(40, 64);
                let c48 = self.solver.bv_const(48, 64);
                let c56 = self.solver.bv_const(56, 64);
                let b0 = self.solver.bvand(a, mask);
                let b0s = self.solver.bvshl(b0, c56);
                let s8 = self.solver.bvlshr(a, c8);
                let b1 = self.solver.bvand(s8, mask);
                let b1s = self.solver.bvshl(b1, c48);
                let s16 = self.solver.bvlshr(a, c16);
                let b2 = self.solver.bvand(s16, mask);
                let b2s = self.solver.bvshl(b2, c40);
                let s24 = self.solver.bvlshr(a, c24);
                let b3 = self.solver.bvand(s24, mask);
                let b3s = self.solver.bvshl(b3, c32);
                let s32 = self.solver.bvlshr(a, c32);
                let b4 = self.solver.bvand(s32, mask);
                let b4s = self.solver.bvshl(b4, c24);
                let s40 = self.solver.bvlshr(a, c40);
                let b5 = self.solver.bvand(s40, mask);
                let b5s = self.solver.bvshl(b5, c16);
                let s48 = self.solver.bvlshr(a, c48);
                let b6 = self.solver.bvand(s48, mask);
                let b6s = self.solver.bvshl(b6, c8);
                let s56 = self.solver.bvlshr(a, c56);
                let b7 = self.solver.bvand(s56, mask);
                let r01 = self.solver.bvor(b0s, b1s);
                let r23 = self.solver.bvor(b2s, b3s);
                let r45 = self.solver.bvor(b4s, b5s);
                let r67 = self.solver.bvor(b6s, b7);
                let r03 = self.solver.bvor(r01, r23);
                let r47 = self.solver.bvor(r45, r67);
                self.solver.bvor(r03, r47)
            }
            ("java/lang/Short", "reverseBytes") => {
                let a = self.encode_operand(&args[0]);
                let mask_ff = self.solver.bv_const(0xFF, 32);
                let lo = self.solver.bvand(a, mask_ff);
                let eight = self.solver.bv_const(8, 32);
                let lo_shifted = self.solver.bvshl(lo, eight);
                let a_shr = self.solver.bvlshr(a, eight);
                let hi = self.solver.bvand(a_shr, mask_ff);
                let result = self.solver.bvor(lo_shifted, hi);
                let sixteen = self.solver.bv_const(16, 32);
                let shifted = self.solver.bvshl(result, sixteen);
                self.solver.bvashr(shifted, sixteen)
            }
            ("java/lang/Character", "reverseBytes") => {
                let a = self.encode_operand(&args[0]);
                let mask_ff = self.solver.bv_const(0xFF, 32);
                let lo = self.solver.bvand(a, mask_ff);
                let eight = self.solver.bv_const(8, 32);
                let lo_shifted = self.solver.bvshl(lo, eight);
                let a_shr = self.solver.bvlshr(a, eight);
                let hi = self.solver.bvand(a_shr, mask_ff);
                self.solver.bvor(lo_shifted, hi)
            }

            // ── Unsigned conversions ────────────────────────────────────
            ("java/lang/Byte", "toUnsignedInt") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFF, 32);
                self.solver.bvand(a, mask)
            }
            ("java/lang/Byte", "toUnsignedLong") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFF, 32);
                let masked = self.solver.bvand(a, mask);
                self.solver.zero_extend(masked, 32)
            }
            ("java/lang/Short", "toUnsignedInt") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFFFF, 32);
                self.solver.bvand(a, mask)
            }
            ("java/lang/Short", "toUnsignedLong") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFFFF, 32);
                let masked = self.solver.bvand(a, mask);
                self.solver.zero_extend(masked, 32)
            }

            // ── Character utility methods ───────────────────────────────
            (_, _) if self.is_char_or_wrapper_util(class, name) => {
                self.encode_char_wrapper_call(class, name, args)
            }
            _ => {
                self.solver.fresh_bv("math_hv", 32)
            }
        }
    }
}
