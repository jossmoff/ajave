//! SMT encoding: operands, rvalues, binary ops, math calls, wrapper toString.

use roast_core::smt::Term;
use roast_ir::*;

use super::ExploreCtx;

impl<'a> ExploreCtx<'a> {
    pub(super) fn can_inline(&self, target: &MethodKey, is_virtual: bool) -> bool {
        if self.call_depth >= super::MAX_CALL_DEPTH {
            return false;
        }
        if is_virtual {
            let targets = self.prog.devirtualise(target);
            !targets.is_empty() && targets.iter().all(|t| self.prog.body(t).is_some())
        } else {
            self.prog.body(target).is_some()
        }
    }

    /// Returns true only for methods that have a precise SMT encoding in
    /// `encode_math_call`. Methods listed here MUST have a corresponding arm
    /// in that function — otherwise they'd get `fresh_bv` (unconstrained but
    /// untainted), which causes spurious violations.
    pub(super) fn math_call_modelled(&self, target: &MethodKey) -> bool {
        match target.class.as_str() {
            "java/lang/Math" | "java/lang/StrictMath" => matches!(
                target.name.as_str(),
                "abs"
                    | "min"
                    | "max"
                    | "addExact"
                    | "subtractExact"
                    | "multiplyExact"
                    | "negateExact"
                    | "floorDiv"
                    | "floorMod"
            ),
            "java/lang/Integer" => matches!(
                target.name.as_str(),
                "parseInt"
                    | "max"
                    | "min"
                    | "sum"
                    | "signum"
                    | "toUnsignedLong"
                    | "divideUnsigned"
                    | "remainderUnsigned"
                    | "compareUnsigned"
                    | "compare"
                    | "compareTo"
                    | "hashCode"
                    | "reverseBytes"
                    | "highestOneBit"
                    | "lowestOneBit"
                    | "rotateLeft"
                    | "rotateRight"
                    | "bitCount"
                    | "numberOfLeadingZeros"
                    | "numberOfTrailingZeros"
                    | "reverse"
            ),
            "java/lang/Long" => matches!(
                target.name.as_str(),
                "parseLong"
                    | "max"
                    | "min"
                    | "sum"
                    | "signum"
                    | "divideUnsigned"
                    | "remainderUnsigned"
                    | "compareUnsigned"
                    | "compare"
                    | "compareTo"
                    | "hashCode"
                    | "reverseBytes"
                    | "highestOneBit"
                    | "lowestOneBit"
                    | "rotateLeft"
                    | "rotateRight"
                    | "bitCount"
                    | "numberOfLeadingZeros"
                    | "numberOfTrailingZeros"
                    | "reverse"
            ),
            "java/lang/Short" => matches!(
                target.name.as_str(),
                "compare"
                    | "compareTo"
                    | "hashCode"
                    | "reverseBytes"
                    | "toUnsignedInt"
                    | "toUnsignedLong"
                    | "parseShort"
            ),
            "java/lang/Byte" => matches!(
                target.name.as_str(),
                "compare"
                    | "compareTo"
                    | "hashCode"
                    | "toUnsignedInt"
                    | "toUnsignedLong"
                    | "parseByte"
            ),
            "java/lang/Character" => matches!(
                target.name.as_str(),
                "compare"
                    | "compareTo"
                    | "hashCode"
                    | "reverseBytes"
                    | "isDigit"
                    | "isLetter"
                    | "isLetterOrDigit"
                    | "isUpperCase"
                    | "isLowerCase"
                    | "isWhitespace"
                    | "isSpaceChar"
                    | "isAlphabetic"
                    | "isBmpCodePoint"
                    | "toUpperCase"
                    | "toLowerCase"
                    | "charCount"
                    | "isValidCodePoint"
                    | "isSupplementaryCodePoint"
                    | "isISOControl"
                    | "isJavaIdentifierStart"
                    | "isJavaIdentifierPart"
                    | "isJavaLetter"
                    | "isJavaLetterOrDigit"
                    | "toCodePoint"
                    | "digit"
                    | "forDigit"
            ),
            "java/lang/Boolean" => matches!(target.name.as_str(), "compareTo"),
            _ => false,
        }
    }

    /// Parse method descriptor to get the width of the i-th argument.
    fn arg_width_from_desc(desc: &str, idx: usize) -> u32 {
        let inner = desc.trim_start_matches('(');
        let mut pos = 0;
        let mut i = 0;
        let bytes = inner.as_bytes();
        while pos < bytes.len() && bytes[pos] != b')' {
            let w = match bytes[pos] {
                b'J' | b'D' => 64,
                b'L' => {
                    // Skip to ';'
                    while pos < bytes.len() && bytes[pos] != b';' {
                        pos += 1;
                    }
                    32
                }
                b'[' => {
                    while pos < bytes.len() && bytes[pos] == b'[' {
                        pos += 1;
                    }
                    if pos < bytes.len() && bytes[pos] == b'L' {
                        while pos < bytes.len() && bytes[pos] != b';' {
                            pos += 1;
                        }
                    }
                    32
                }
                _ => 32,
            };
            if i == idx {
                return w;
            }
            pos += 1;
            i += 1;
        }
        32
    }

    pub(super) fn encode_math_call(&mut self, target: &MethodKey, args: &[Operand]) -> Term {
        let class = target.class.as_str();
        let name = target.name.as_str();
        // Derive argument widths from the method descriptor, not from
        // variable types (which can be wrong due to local slot reuse).
        let arg0_w = Self::arg_width_from_desc(&target.desc, 0);
        let _arg1_w = Self::arg_width_from_desc(&target.desc, 1);
        match (class, name) {
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
                // Unsigned compare: add MIN_VALUE to both, then signed compare
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
            ("java/lang/Integer", "parseInt")
            | ("java/lang/Long", "parseLong")
            | ("java/lang/Short", "parseShort")
            | ("java/lang/Byte", "parseByte") => {
                let w = if class == "java/lang/Long" { 64 } else { 32 };
                self.solver.fresh_bv("parse", w)
            }
            // Integer/Long.compare(a, b) → (a < b) ? -1 : (a == b) ? 0 : 1
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
            // Character/Short/Byte.compare(a, b) → a - b  (result fits in int)
            ("java/lang/Short" | "java/lang/Byte" | "java/lang/Character", "compare") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsub(a, b)
            }
            // hashCode for Integer/Short/Byte/Character: identity function
            (
                "java/lang/Integer" | "java/lang/Short" | "java/lang/Byte" | "java/lang/Character",
                "hashCode",
            ) => self.encode_operand(&args[0]),
            // Long.hashCode(long): (int)(value ^ (value >>> 32))
            ("java/lang/Long", "hashCode") => {
                let a = self.encode_operand(&args[0]);
                let c32 = self.solver.bv_const(32, 64);
                let shifted = self.solver.bvlshr(a, c32);
                let xored = self.solver.bvxor(a, shifted);
                self.solver.extract(xored, 31, 0)
            }
            // Integer.reverseBytes(int): swap byte order
            ("java/lang/Integer", "reverseBytes") => {
                let a = self.encode_operand(&args[0]);
                // Byte 3 (MSB) → byte 0, byte 2 → byte 1, etc.
                let b0 = self.solver.extract(a, 7, 0);
                let b1 = self.solver.extract(a, 15, 8);
                let b2 = self.solver.extract(a, 23, 16);
                let b3 = self.solver.extract(a, 31, 24);
                // Reassemble as b0|b1|b2|b3 using shifts and ors
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
            // Long.reverseBytes(long): swap byte order of 64-bit value
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
                // Upper 4 bytes go to lower positions — mirror
                let s32 = self.solver.bvlshr(a, c32);
                let b4 = self.solver.bvand(s32, mask);
                let b4s = self.solver.bvshl(b4, c24);
                // Actually simpler: swap upper and lower 32 bits, then swap bytes within each
                // Let's do it directly: byte i goes to position 7-i
                let s40 = self.solver.bvlshr(a, c40);
                let b5 = self.solver.bvand(s40, mask);
                let b5s = self.solver.bvshl(b5, c16);
                let s48 = self.solver.bvlshr(a, c48);
                let b6 = self.solver.bvand(s48, mask);
                let b6s = self.solver.bvshl(b6, c8);
                let s56 = self.solver.bvlshr(a, c56);
                let b7 = self.solver.bvand(s56, mask);
                // Combine: b0s | b1s | b2s | b3s | b4s | b5s | b6s | b7
                let r01 = self.solver.bvor(b0s, b1s);
                let r23 = self.solver.bvor(b2s, b3s);
                let r45 = self.solver.bvor(b4s, b5s);
                let r67 = self.solver.bvor(b6s, b7);
                let r03 = self.solver.bvor(r01, r23);
                let r47 = self.solver.bvor(r45, r67);
                self.solver.bvor(r03, r47)
            }
            // Integer/Long.highestOneBit
            ("java/lang/Integer" | "java/lang/Long", "highestOneBit") => {
                // This is hard to encode precisely in BV without loops.
                // Use a trick: result = (val == 0) ? 0 : (1 << (width-1-nlz(val)))
                // Since nlz is hard too, just use fresh_bv with constraints.
                // For now, use a simpler approach: the result is the value with only
                // the highest set bit retained. We can express this with ITE cascade.
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let zero = self.solver.bv_const(0, w);
                let is_zero = self.solver.bveq(a, zero);
                // Build cascade: check from MSB down
                let mut result = zero;
                for i in (0..w).rev() {
                    let bit_mask = self.solver.bv_const(1i64 << i, w);
                    let masked = self.solver.bvand(a, bit_mask);
                    let has_bit = self.solver.bveq(masked, bit_mask);
                    result = self.solver.ite(has_bit, bit_mask, result);
                }
                self.solver.ite(is_zero, zero, result)
            }
            // Integer/Long.lowestOneBit: val & (-val)
            ("java/lang/Integer" | "java/lang/Long", "lowestOneBit") => {
                let a = self.encode_operand(&args[0]);
                let neg = self.solver.bvneg(a);
                self.solver.bvand(a, neg)
            }
            // Integer/Long.rotateLeft(val, distance)
            ("java/lang/Integer" | "java/lang/Long", "rotateLeft") => {
                let a = self.encode_operand(&args[0]);
                let d = self.encode_operand(&args[1]);
                let w = arg0_w;
                let wc = self.solver.bv_const(w as i64, w);
                // Mask distance to [0, w) — but d is 32-bit for both int and long
                // For Long.rotateLeft(long, int): d is 32-bit, need to extend
                let d_w = if w == 64 {
                    self.solver.zero_extend(d, 32)
                } else {
                    d
                };
                let mask = self.solver.bv_const(w as i64 - 1, w);
                let dist = self.solver.bvand(d_w, mask);
                let complement = self.solver.bvsub(wc, dist);
                let left = self.solver.bvshl(a, dist);
                let right = self.solver.bvlshr(a, complement);
                self.solver.bvor(left, right)
            }
            // Integer/Long.rotateRight(val, distance)
            ("java/lang/Integer" | "java/lang/Long", "rotateRight") => {
                let a = self.encode_operand(&args[0]);
                let d = self.encode_operand(&args[1]);
                let w = arg0_w;
                let wc = self.solver.bv_const(w as i64, w);
                let d_w = if w == 64 {
                    self.solver.zero_extend(d, 32)
                } else {
                    d
                };
                let mask = self.solver.bv_const(w as i64 - 1, w);
                let dist = self.solver.bvand(d_w, mask);
                let complement = self.solver.bvsub(wc, dist);
                let right = self.solver.bvlshr(a, dist);
                let left = self.solver.bvshl(a, complement);
                self.solver.bvor(right, left)
            }
            // Byte.toUnsignedInt(byte) → b & 0xFF
            ("java/lang/Byte", "toUnsignedInt") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFF, 32);
                self.solver.bvand(a, mask)
            }
            // Byte.toUnsignedLong(byte) → b & 0xFF (as 64-bit)
            ("java/lang/Byte", "toUnsignedLong") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFF, 32);
                let masked = self.solver.bvand(a, mask);
                self.solver.zero_extend(masked, 32)
            }
            // Short.toUnsignedInt(short) → s & 0xFFFF
            ("java/lang/Short", "toUnsignedInt") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFFFF, 32);
                self.solver.bvand(a, mask)
            }
            // Short.toUnsignedLong(short) → s & 0xFFFF (as 64-bit)
            ("java/lang/Short", "toUnsignedLong") => {
                let a = self.encode_operand(&args[0]);
                let mask = self.solver.bv_const(0xFFFF, 32);
                let masked = self.solver.bvand(a, mask);
                self.solver.zero_extend(masked, 32)
            }
            // Short.reverseBytes(short): swap low two bytes
            ("java/lang/Short", "reverseBytes") => {
                let a = self.encode_operand(&args[0]);
                let mask_ff = self.solver.bv_const(0xFF, 32);
                let lo = self.solver.bvand(a, mask_ff);
                let eight = self.solver.bv_const(8, 32);
                let lo_shifted = self.solver.bvshl(lo, eight);
                let a_shr = self.solver.bvlshr(a, eight);
                let hi = self.solver.bvand(a_shr, mask_ff);
                let result = self.solver.bvor(lo_shifted, hi);
                // Sign-extend from 16 bits: shift left 16, then ashr 16
                let sixteen = self.solver.bv_const(16, 32);
                let shifted = self.solver.bvshl(result, sixteen);
                self.solver.bvashr(shifted, sixteen)
            }
            // Character.reverseBytes(char): swap low two bytes (unsigned)
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
            // Integer.compareTo(other): unbox both, compare with -1/0/1
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
            // Short/Byte/Character.compareTo(other): unbox both, return a - b
            ("java/lang/Short" | "java/lang/Byte" | "java/lang/Character", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = (class.to_string(), "$$value".to_string(), "I".to_string());
                let arr = self.get_field_array(&k, 32);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                self.solver.bvsub(a, b)
            }
            // Boolean.compareTo(other): unbox both, return a - b (for boolean 0/1)
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
                let k = (
                    "java/lang/Long".to_string(),
                    "$$value".to_string(),
                    "J".to_string(),
                );
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
            // Integer/Long.bitCount(val): count set bits using ITE cascade
            ("java/lang/Integer" | "java/lang/Long", "bitCount") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let zero32 = self.solver.bv_const(0, 32);
                let one32 = self.solver.bv_const(1, 32);
                let mut count = zero32;
                for i in 0..w {
                    let bit_mask = self.solver.bv_const(1i64 << i, w);
                    let masked = self.solver.bvand(a, bit_mask);
                    let has_bit = self.solver.bveq(masked, bit_mask);
                    let inc = self.solver.ite(has_bit, one32, zero32);
                    count = self.solver.bvadd(count, inc);
                }
                count
            }
            // Integer/Long.numberOfTrailingZeros(val)
            ("java/lang/Integer" | "java/lang/Long", "numberOfTrailingZeros") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                // Start with w (all zeros case), scan from LSB
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
            // Integer/Long.numberOfLeadingZeros(val)
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
            // Integer/Long.reverse(val): reverse all bits
            ("java/lang/Integer" | "java/lang/Long", "reverse") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                // Extract each bit, shift to reversed position, OR together
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
            // Character/Short/Byte/Integer/Long utility methods
            (_, _) if self.is_char_or_wrapper_util(class, name) => {
                self.encode_char_wrapper_call(class, name, args)
            }
            _ => self.solver.fresh_bv("math_hv", 32),
        }
    }

    fn is_char_or_wrapper_util(&self, class: &str, name: &str) -> bool {
        match class {
            "java/lang/Character" => matches!(
                name,
                "isDigit"
                    | "isLetter"
                    | "isLetterOrDigit"
                    | "isUpperCase"
                    | "isLowerCase"
                    | "isWhitespace"
                    | "isSpaceChar"
                    | "isAlphabetic"
                    | "isBmpCodePoint"
                    | "toUpperCase"
                    | "toLowerCase"
                    | "charCount"
                    | "isValidCodePoint"
                    | "isSupplementaryCodePoint"
                    | "isISOControl"
                    | "isJavaIdentifierStart"
                    | "isJavaIdentifierPart"
                    | "isJavaLetter"
                    | "isJavaLetterOrDigit"
                    | "toCodePoint"
                    | "digit"
                    | "forDigit"
            ),
            _ => false,
        }
    }

    fn encode_char_wrapper_call(&mut self, class: &str, name: &str, args: &[Operand]) -> Term {
        let one = self.solver.bv_const(1, 32);
        let zero = self.solver.bv_const(0, 32);

        match (class, name) {
            // Character.isDigit(char) → c >= '0' && c <= '9'
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
            // isSupplementaryCodePoint: cp >= 0x10000 && cp <= 0x10FFFF
            ("java/lang/Character", "isSupplementaryCodePoint") => {
                let cp = self.encode_operand(&args[0]);
                let lo = self.solver.bv_const(0x10000, 32);
                let hi = self.solver.bv_const(0x10FFFF, 32);
                let ge = self.solver.bvsge(cp, lo);
                let le = self.solver.bvsle(cp, hi);
                let result = self.solver.and(ge, le);
                self.solver.ite(result, one, zero)
            }
            // isISOControl: c <= 0x1F || (c >= 0x7F && c <= 0x9F)
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
            // isJavaLetter (deprecated) = isJavaIdentifierStart
            ("java/lang/Character", "isJavaLetter" | "isJavaIdentifierStart") => {
                let c = self.encode_operand(&args[0]);
                let alpha = self.encode_is_alpha(c, one, zero);
                let alpha_b = self.solver.bveq(alpha, one);
                let dollar = self.solver.bv_const(0x24, 32); // '$'
                let is_dollar = self.solver.bveq(c, dollar);
                let underscore = self.solver.bv_const(0x5F, 32); // '_'
                let is_under = self.solver.bveq(c, underscore);
                let r = self.solver.or(alpha_b, is_dollar);
                let result = self.solver.or(r, is_under);
                self.solver.ite(result, one, zero)
            }
            // isJavaLetterOrDigit (deprecated) = isJavaIdentifierPart
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
            // toCodePoint(high, low): (high - 0xD800) * 0x400 + (low - 0xDC00) + 0x10000
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
            // digit(ch, radix): for ASCII digits/letters within radix
            ("java/lang/Character", "digit") => {
                let c = self.encode_operand(&args[0]);
                let radix = self.encode_operand(&args[1]);
                let c0 = self.solver.bv_const(0x30, 32); // '0'
                let c9 = self.solver.bv_const(0x39, 32); // '9'
                let ca = self.solver.bv_const(0x61, 32); // 'a'
                let cb = self.solver.bv_const(0x41, 32); // 'A'
                                                         // digit value from '0'-'9': c - '0'
                let dval = self.solver.bvsub(c, c0);
                let ge0 = self.solver.bvsge(c, c0);
                let le9 = self.solver.bvsle(c, c9);
                let is_num = self.solver.and(ge0, le9);
                // digit value from 'a'-'z': c - 'a' + 10
                let dval_a = self.solver.bvsub(c, ca);
                let ten = self.solver.bv_const(10, 32);
                let dval_al = self.solver.bvadd(dval_a, ten);
                let za = self.solver.bv_const(0x7A, 32);
                let ge_a = self.solver.bvsge(c, ca);
                let le_a = self.solver.bvsle(c, za);
                let is_lower = self.solver.and(ge_a, le_a);
                // digit value from 'A'-'Z': c - 'A' + 10
                let dval_b = self.solver.bvsub(c, cb);
                let dval_bu = self.solver.bvadd(dval_b, ten);
                let zb = self.solver.bv_const(0x5A, 32);
                let ge_b = self.solver.bvsge(c, cb);
                let le_b = self.solver.bvsle(c, zb);
                let is_upper = self.solver.and(ge_b, le_b);
                // pick digit value
                let neg1 = self.solver.bv_const(-1, 32);
                let v1 = self.solver.ite(is_num, dval, neg1);
                let v2 = self.solver.ite(is_lower, dval_al, v1);
                let v3 = self.solver.ite(is_upper, dval_bu, v2);
                // check within radix
                let in_range = self.solver.bvslt(v3, radix);
                let valid = self.solver.bvsge(v3, zero);
                let ok = self.solver.and(in_range, valid);
                let neg1b = self.solver.bv_const(-1, 32);
                self.solver.ite(ok, v3, neg1b)
            }
            // forDigit(digit, radix): inverse of digit()
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

    fn encode_is_alpha(&mut self, c: Term, one: Term, zero: Term) -> Term {
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

    pub(super) fn encode_operand(&mut self, op: &Operand) -> Term {
        match op {
            Operand::Var(v) => self.get_var(*v),
            Operand::Const(Const::Int(n)) => self.solver.bv_const(*n as i64, 32),
            Operand::Const(Const::Long(n)) => self.solver.bv_const(*n, 64),
            Operand::Const(Const::Null) => self.solver.bv_const(0, 32),
            Operand::Const(Const::Str(_)) => self.solver.bv_const(1, 32),
            Operand::Const(Const::Float(f)) => self.solver.bv_const(f.to_bits() as i64, 32),
            Operand::Const(Const::Double(d)) => self.solver.bv_const(d.to_bits() as i64, 64),
            Operand::Const(_) => self.solver.bv_const(0, 32),
        }
    }

    pub(super) fn encode_str_operand(&mut self, op: &Operand) -> Option<Term> {
        match op {
            Operand::Var(v) => self.str_vars.get(v).copied(),
            Operand::Const(Const::Str(s)) => Some(self.solver.str_const(s)),
            _ => None,
        }
    }

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
                // Static: toString(boolean) — arg is int 0/1
                // Instance: toString() — receiver is Boolean, unbox $$value
                let val = if target.desc.starts_with("(Z)") {
                    // static toString(boolean)
                    self.encode_operand(args.first()?)
                } else if target.desc == "()Ljava/lang/String;" {
                    // instance toString()
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
            // Integer/Long.toHexString — unsigned hex representation
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
            // Integer/Long.toBinaryString — unsigned binary representation
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
            // Integer/Long.toOctalString — unsigned octal representation
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
            // Integer/Long.toUnsignedString(int/long) — unsigned decimal
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
            // Short.toString(short) / Byte.toString(byte) — static and instance
            ("java/lang/Short" | "java/lang/Byte", "toString")
                if target.desc.contains(")Ljava/lang/String;") =>
            {
                let val = if target.desc == "()Ljava/lang/String;" {
                    // Instance: unbox $$value from receiver
                    let recv = self.encode_operand(args.first()?);
                    let fk = (target.class.clone(), "$$value".to_string(), "I".to_string());
                    let arr = self.get_field_array(&fk, 32);
                    self.solver.array_select(arr, recv)
                } else {
                    self.encode_operand(args.first()?)
                };
                let result = self.signed_bv_to_str(val, 32);
                Some((one, Some(result)))
            }
            // Character.toString(char) — approximate with fresh string of length 1
            ("java/lang/Character", "toString") if target.desc.contains(")Ljava/lang/String;") => {
                let s = self.solver.fresh_str("char_str");
                let len = self.solver.str_len(s);
                let one_int = self.solver.int_const(1);
                let len_eq = self.solver.bveq(len, one_int);
                self.solver.assert(len_eq);
                Some((one, Some(s)))
            }
            // String.valueOf(int), String.valueOf(long), String.valueOf(boolean), etc.
            ("java/lang/String", "valueOf")
                if !target.desc.starts_with("(L") && !target.desc.starts_with("([") =>
            {
                // Already handled by encode_str_call, but also handle here
                // for cases where the String class isn't in STR_OWNERS
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
                    let w = if target.desc.starts_with("(J)") {
                        64
                    } else {
                        32
                    };
                    let result = self.signed_bv_to_str(val, w);
                    Some((one, Some(result)))
                }
            }
            _ => None,
        }
    }

    pub(super) fn encode_rvalue(&mut self, rv: &Rvalue) -> Term {
        match rv {
            Rvalue::Use(o) => self.encode_operand(o),
            Rvalue::Nondet(ty, jvm_byte) => {
                let w = self.width_of_ty(ty);
                let idx = self.nondet_terms.len();
                let t = self.solver.fresh_bv(&format!("nd_{idx}"), w);
                if *ty == Ty::Str {
                    self.assert_nonzero(t);
                }
                let range: Option<(i64, i64)> = match jvm_byte {
                    Some(b'Z') => Some((0, 1)),
                    Some(b'B') => Some((-128, 127)),
                    Some(b'S') => Some((-32768, 32767)),
                    // Constrain char to ASCII range where our Character method
                    // encodings are precise. Non-ASCII chars have Unicode-specific
                    // behavior (isLetter, isDigit, etc.) that our BV encoding
                    // doesn't model, leading to incorrect witnesses.
                    Some(b'C') => Some((0, 127)),
                    _ => None,
                };
                if let Some((lo, hi)) = range {
                    let lo_t = self.solver.bv_const(lo, w);
                    let hi_t = self.solver.bv_const(hi, w);
                    let ge = self.solver.bvsge(t, lo_t);
                    let le = self.solver.bvsle(t, hi_t);
                    let c = self.solver.and(ge, le);
                    self.solver.assert(c);
                }
                let str_term = if *ty == Ty::Str {
                    Some(self.solver.fresh_str(&format!("nds_{idx}")))
                } else {
                    None
                };
                if *ty != Ty::Ref {
                    self.nondet_terms.push((idx, t, w, *ty, str_term));
                }
                t
            }
            Rvalue::Havoc(ty) => {
                let w = self.width_of_ty(ty);
                self.solver.fresh_bv("hv", w)
            }
            Rvalue::Bin(op, a, b) => self.encode_binop(*op, a, b),
            Rvalue::Neg(o) => {
                let t = self.encode_operand(o);
                self.solver.bvneg(t)
            }
            Rvalue::Cast(ty, o) => {
                let t = self.encode_operand(o);
                match ty {
                    Ty::Long => self.solver.sign_extend(t, 32),
                    Ty::Int => self.solver.extract(t, 31, 0),
                    _ => t,
                }
            }
            Rvalue::Cmp(a, b) => {
                let at = self.encode_operand(a);
                let bt = self.encode_operand(b);
                let aw = self.width_of_operand(a);
                let bw = self.width_of_operand(b);
                let (at, bt) = if aw < bw {
                    (self.solver.sign_extend(at, bw - aw), bt)
                } else if bw < aw {
                    (at, self.solver.sign_extend(bt, aw - bw))
                } else {
                    (at, bt)
                };
                let lt = self.solver.bvslt(at, bt);
                let eq = self.solver.bveq(at, bt);
                let minus1 = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let one = self.solver.bv_const(1, 32);
                let inner = self.solver.ite(eq, zero, one);
                self.solver.ite(lt, minus1, inner)
            }
            Rvalue::GetStatic(fk) => {
                self.ensure_clinit(&fk.class);
                let k = Self::field_key_raw(fk);
                if let Some(&t) = self.statics.get(&k) {
                    t
                } else if self.is_program_class(&fk.class) {
                    let w = Self::field_elem_width(&fk.desc);
                    let t = self.solver.bv_const(0, w);
                    self.statics.insert(k, t);
                    t
                } else {
                    let w = Self::field_elem_width(&fk.desc);
                    let t = self.solver.fresh_bv("static", w);
                    if fk.desc.starts_with('L') || fk.desc.starts_with('[') {
                        let zero = self.solver.bv_const(0, 32);
                        let eq = self.solver.bveq(t, zero);
                        let neq = self.solver.not(eq);
                        self.solver.assert(neq);
                    }
                    self.statics.insert(k, t);
                    t
                }
            }
            Rvalue::GetField { field, obj, .. } => {
                let obj_term = self.encode_operand(obj);
                let k = self.field_key_resolved(field);
                let w = Self::field_elem_width(&field.desc);
                let arr = self.get_field_array(&k, w);
                self.solver.array_select(arr, obj_term)
            }
            Rvalue::New(class) => {
                let id = self.next_alloc_id;
                self.next_alloc_id += 1;
                let ref_term = self.solver.bv_const(id, 32);
                let type_id = self.get_type_id(class);
                let type_id_term = self.solver.bv_const(type_id, 32);
                let new_ta = self
                    .solver
                    .array_store(self.type_array, ref_term, type_id_term);
                self.type_array = new_ta;
                ref_term
            }
            Rvalue::NewArray { len, .. } => {
                let id = self.next_alloc_id;
                self.next_alloc_id += 1;
                let ref_term = self.solver.bv_const(id, 32);
                let len_term = self.encode_operand(len);
                // Java arrays are zero-initialized by the JVM spec.
                let zero = self.solver.bv_const(0, 32);
                let arr_term = self.solver.const_array(zero, 32);
                self.array_map.push((ref_term, arr_term, len_term));
                ref_term
            }
            Rvalue::ArrayLength(arr_op) => {
                let ref_term = self.encode_operand(arr_op);
                self.array_length_lookup(ref_term)
            }
            Rvalue::ArrayLoad { arr, idx } => {
                let ref_term = self.encode_operand(arr);
                let idx_term = self.encode_operand(idx);
                self.array_select_lookup(ref_term, idx_term)
            }
            Rvalue::InstanceOf { obj, class } => {
                let obj_term = self.encode_operand(obj);
                let zero = self.solver.bv_const(0, 32);
                let one = self.solver.bv_const(1, 32);
                let null_check = self.solver.bveq(obj_term, zero);
                let not_null = self.solver.not(null_check);
                // java/lang/Object: every non-null reference is an Object
                if class == "java/lang/Object" {
                    return self.solver.ite(not_null, one, zero);
                }
                // String constant: always a java/lang/String instance
                if matches!(obj, Operand::Const(Const::Str(_))) {
                    let is_str = self.prog.is_subtype("java/lang/String", class);
                    return if is_str { one } else { zero };
                }
                let obj_type = self.solver.array_select(self.type_array, obj_term);
                let subtypes = self.subtype_ids(class);
                let ff = self.solver.bool_const(false);
                let mut is_instance = ff;
                for sid in subtypes {
                    let st = self.solver.bv_const(sid, 32);
                    let eq = self.solver.bveq(obj_type, st);
                    is_instance = self.solver.or(is_instance, eq);
                }
                let result_bool = self.solver.and(not_null, is_instance);
                self.solver.ite(result_bool, one, zero)
            }
            Rvalue::Call { .. } => self.solver.fresh_bv("havoc", 32),
        }
    }

    pub(super) fn array_contents_lookup(&mut self, ref_term: Term) -> Term {
        let pairs: Vec<(Term, Term, Term)> = self.array_map.clone();
        let mut result = self.solver.fresh_array("arr_default", 32);
        // Iterate forward so later entries (from array_store_update) shadow earlier ones.
        for (r, arr, _len) in &pairs {
            let eq = self.solver.bveq(ref_term, *r);
            result = self.solver.ite(eq, *arr, result);
        }
        result
    }

    pub(super) fn array_length_lookup(&mut self, ref_term: Term) -> Term {
        let pairs: Vec<(Term, Term, Term)> = self.array_map.clone();
        let mut result = self.solver.fresh_bv("len_default", 32);
        for (r, _arr, len) in &pairs {
            let eq = self.solver.bveq(ref_term, *r);
            result = self.solver.ite(eq, *len, result);
        }
        result
    }

    pub(super) fn array_select_lookup(&mut self, ref_term: Term, idx_term: Term) -> Term {
        let arr = self.array_contents_lookup(ref_term);
        self.solver.array_select(arr, idx_term)
    }

    pub(super) fn array_store_update(&mut self, ref_term: Term, idx_term: Term, val_term: Term) {
        let arr = self.array_contents_lookup(ref_term);
        let new_arr = self.solver.array_store(arr, idx_term, val_term);
        let len = self.array_length_lookup(ref_term);
        self.array_map.push((ref_term, new_arr, len));
    }

    pub(super) fn encode_binop(&mut self, op: BinOp, a: &Operand, b: &Operand) -> Term {
        let at = self.encode_operand(a);
        let bt = self.encode_operand(b);
        let aw = self.width_of_operand(a);
        let bw = self.width_of_operand(b);
        let (at, bt) = if !matches!(op, BinOp::Shl | BinOp::Shr | BinOp::UShr) && aw != bw {
            if aw < bw {
                (self.solver.sign_extend(at, bw - aw), bt)
            } else {
                (at, self.solver.sign_extend(bt, aw - bw))
            }
        } else {
            (at, bt)
        };
        match op {
            BinOp::Add => self.solver.bvadd(at, bt),
            BinOp::Sub => self.solver.bvsub(at, bt),
            BinOp::Mul => self.solver.bvmul(at, bt),
            BinOp::Div => self.solver.bvsdiv(at, bt),
            BinOp::Rem => self.solver.bvsrem(at, bt),
            BinOp::And => self.solver.bvand(at, bt),
            BinOp::Or => self.solver.bvor(at, bt),
            BinOp::Xor => self.solver.bvxor(at, bt),
            BinOp::Shl | BinOp::Shr | BinOp::UShr => {
                let aw = self.width_of_operand(a);
                let mask = if aw == 64 { 0x3F } else { 0x1F };
                let mask_t = self.solver.bv_const(mask, 32);
                let bt = self.solver.bvand(bt, mask_t);
                let bt = if aw == 64 {
                    self.solver.zero_extend(bt, 32)
                } else {
                    bt
                };
                match op {
                    BinOp::Shl => self.solver.bvshl(at, bt),
                    BinOp::Shr => self.solver.bvashr(at, bt),
                    BinOp::UShr => self.solver.bvlshr(at, bt),
                    _ => unreachable!(),
                }
            }
            BinOp::Eq => {
                let cmp = self.solver.bveq(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Ne => {
                let cmp = self.solver.bveq(at, bt);
                let ncmp = self.solver.not(cmp);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(ncmp, one, zero)
            }
            BinOp::Lt => {
                let cmp = self.solver.bvslt(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Le => {
                let cmp = self.solver.bvsle(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Gt => {
                let cmp = self.solver.bvsgt(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Ge => {
                let cmp = self.solver.bvsge(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
        }
    }
}
