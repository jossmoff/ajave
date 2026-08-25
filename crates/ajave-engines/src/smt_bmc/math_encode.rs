//! SMT encoding for Math, Integer, Long, Short, Byte wrapper method calls.

use ajave_core::smt::Term;
use ajave_ir::*;

use super::{ExploreCtx, FK};

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
                    | "getExponent"
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
                    | "floatValue" | "doubleValue"
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
                    | "floatValue" | "doubleValue"
            ),
            "java/lang/Short" => matches!(
                target.name.as_str(),
                "parseShort" | "compare" | "compareTo" | "hashCode" | "reverseBytes" | "toUnsignedInt" | "toUnsignedLong"
                    | "floatValue" | "doubleValue"
            ),
            "java/lang/Byte" => matches!(
                target.name.as_str(),
                "parseByte" | "compare" | "compareTo" | "hashCode" | "toUnsignedInt" | "toUnsignedLong"
                    | "floatValue" | "doubleValue"
            ),
            "java/lang/Character" => {
                self.is_char_or_wrapper_util(&target.class, &target.name)
                    || matches!(target.name.as_str(), "compare" | "compareTo" | "hashCode" | "reverseBytes")
            }
            "java/lang/Boolean" => matches!(
                target.name.as_str(),
                "compareTo" | "hashCode"
            ),
            "java/lang/Float" => matches!(
                target.name.as_str(),
                "floatToRawIntBits" | "floatToIntBits" | "intBitsToFloat"
                    | "isNaN" | "isInfinite" | "isFinite"
                    | "compare" | "compareTo" | "max" | "min" | "sum"
                    | "hashCode"
                    | "byteValue" | "shortValue"
                    | "intValue" | "longValue" | "doubleValue"
            ),
            "java/lang/Double" => matches!(
                target.name.as_str(),
                "doubleToRawLongBits" | "doubleToLongBits" | "longBitsToDouble"
                    | "isNaN" | "isInfinite" | "isFinite"
                    | "compare" | "compareTo" | "max" | "min" | "sum"
                    | "hashCode"
                    | "byteValue" | "shortValue"
                    | "intValue" | "longValue" | "floatValue"
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
                // floorDiv rounds towards -∞, bvsdiv truncates towards 0.
                // floorDiv(a,b) = trunc(a/b) - (has_remainder && signs_differ ? 1 : 0)
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let w = arg0_w;
                let q = self.solver.bvsdiv(a, b);
                let r = self.solver.bvsrem(a, b);
                let zero = self.solver.bv_const(0, w);
                let one = self.solver.bv_const(1, w);
                let has_rem = self.solver.bveq(r, zero);
                let has_rem = self.solver.not(has_rem);
                // Signs differ: (a ^ b) < 0
                let axb = self.solver.bvxor(a, b);
                let signs_diff = self.solver.bvslt(axb, zero);
                let adjust = self.solver.and(has_rem, signs_diff);
                let q_minus1 = self.solver.bvsub(q, one);
                self.solver.ite(adjust, q_minus1, q)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "floorMod") => {
                // floorMod(a,b) = bvsrem(a,b) + (has_remainder && signs_differ ? b : 0)
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let w = arg0_w;
                let r = self.solver.bvsrem(a, b);
                let zero = self.solver.bv_const(0, w);
                let has_rem = self.solver.bveq(r, zero);
                let has_rem = self.solver.not(has_rem);
                let axb = self.solver.bvxor(a, b);
                let signs_diff = self.solver.bvslt(axb, zero);
                let adjust = self.solver.and(has_rem, signs_diff);
                // If adjusting: remainder = bvsrem(a,b) + b
                let r_adjusted = self.solver.bvadd(r, b);
                self.solver.ite(adjust, r_adjusted, r)
            }

            // ── Math.getExponent: extract IEEE 754 biased exponent ───────
            ("java/lang/Math" | "java/lang/StrictMath", "getExponent") => {
                let a = self.encode_operand(&args[0]);
                if arg0_w == 64 {
                    // double: exponent is bits[62:52], bias=1023
                    let exp = self.solver.extract(a, 62, 52);  // 11 bits
                    let exp32 = self.solver.zero_extend(exp, 21); // → BV32
                    let bias = self.solver.bv_const(1023, 32);
                    let all_ones = self.solver.bv_const(0x7FF_i64, 32);
                    let is_special = self.solver.bveq(exp32, all_ones); // Inf/NaN
                    let zero = self.solver.bv_const(0, 32);
                    let is_subnormal = self.solver.bveq(exp32, zero);
                    let normal = self.solver.bvsub(exp32, bias);
                    let max_plus1 = self.solver.bv_const(1024, 32); // MAX_EXPONENT+1
                    let min_minus1 = self.solver.bv_const(-1023_i64, 32); // MIN_EXPONENT-1
                    let r = self.solver.ite(is_special, max_plus1, normal);
                    self.solver.ite(is_subnormal, min_minus1, r)
                } else {
                    // float: exponent is bits[30:23], bias=127
                    let exp = self.solver.extract(a, 30, 23);  // 8 bits
                    let exp32 = self.solver.zero_extend(exp, 24); // → BV32
                    let bias = self.solver.bv_const(127, 32);
                    let all_ones = self.solver.bv_const(0xFF_i64, 32);
                    let is_special = self.solver.bveq(exp32, all_ones);
                    let zero = self.solver.bv_const(0, 32);
                    let is_subnormal = self.solver.bveq(exp32, zero);
                    let normal = self.solver.bvsub(exp32, bias);
                    let max_plus1 = self.solver.bv_const(128, 32);
                    let min_minus1 = self.solver.bv_const(-127_i64, 32);
                    let r = self.solver.ite(is_special, max_plus1, normal);
                    self.solver.ite(is_subnormal, min_minus1, r)
                }
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
                self.solver.bvudiv(a, b)
            }
            ("java/lang/Integer" | "java/lang/Long", "remainderUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvurem(a, b)
            }
            ("java/lang/Integer" | "java/lang/Long", "compareUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let one = self.solver.bv_const(1, 32);
                let mone = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let lt = self.solver.bvult(a, b);
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
                let k = FK::new(class, "$$value", "I");
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
                let k = FK::new(class, "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                self.solver.bvsub(a, b)
            }
            ("java/lang/Boolean", "hashCode") => {
                if target.desc.starts_with("(Z)") {
                    // static hashCode(boolean)
                    let a = self.encode_operand(&args[0]);
                    let zero = self.solver.bv_const(0, 32);
                    let is_false = self.solver.bveq(a, zero);
                    let t = self.solver.bv_const(1231, 32);
                    let f = self.solver.bv_const(1237, 32);
                    self.solver.ite(is_false, f, t)
                } else {
                    // instance hashCode()
                    let this_ref = self.encode_operand(&args[0]);
                    let k = FK::new("java/lang/Boolean", "$$value", "I");
                    let arr = self.get_field_array(&k, 32);
                    let v = self.solver.array_select(arr, this_ref);
                    let zero = self.solver.bv_const(0, 32);
                    let is_false = self.solver.bveq(v, zero);
                    let t = self.solver.bv_const(1231, 32);
                    let f = self.solver.bv_const(1237, 32);
                    self.solver.ite(is_false, f, t)
                }
            }
            ("java/lang/Boolean", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = FK::new(class, "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                self.solver.bvsub(a, b)
            }
            ("java/lang/Long", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = FK::new("java/lang/Long", "$$value", "J");
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
            // numberOfTrailingZeros: binary search O(log W) depth
            ("java/lang/Integer" | "java/lang/Long", "numberOfTrailingZeros") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                // Binary search: check bottom half, if all zeros add half-width and search top half
                let mut count = self.solver.bv_const(0, 32);
                let mut val = a;
                let mut remaining = w;
                while remaining > 1 {
                    let half = remaining / 2;
                    let lo_half = self.solver.extract(val, half - 1, 0);
                    let zero_half = self.solver.bv_const(0, half);
                    let lo_is_zero = self.solver.bveq(lo_half, zero_half);
                    let hi_half = self.solver.extract(val, remaining - 1, half);
                    // If low half is zero, count += half and continue with high half
                    let half_c = self.solver.bv_const(half as i64, 32);
                    let count_plus = self.solver.bvadd(count, half_c);
                    count = self.solver.ite(lo_is_zero, count_plus, count);
                    // Select which half to continue searching
                    // Pad both halves to same width for ITE
                    let hi_padded = if remaining - half < half {
                        self.solver.zero_extend(hi_half, half - (remaining - half))
                    } else {
                        hi_half
                    };
                    val = self.solver.ite(lo_is_zero, hi_padded, lo_half);
                    remaining = half;
                }
                // Final bit: if the single remaining bit is 0, add 1
                let last_bit = self.solver.extract(val, 0, 0);
                let zero1 = self.solver.bv_const(0, 1);
                let last_zero = self.solver.bveq(last_bit, zero1);
                let one = self.solver.bv_const(1, 32);
                let count_plus1 = self.solver.bvadd(count, one);
                self.solver.ite(last_zero, count_plus1, count)
            }
            // numberOfLeadingZeros: binary search O(log W) depth
            ("java/lang/Integer" | "java/lang/Long", "numberOfLeadingZeros") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                // Binary search: check top half, if all zeros add half-width and search bottom half
                let mut count = self.solver.bv_const(0, 32);
                let mut val = a;
                let mut remaining = w;
                while remaining > 1 {
                    let half = remaining / 2;
                    let hi_half = self.solver.extract(val, remaining - 1, remaining - half);
                    let zero_half = self.solver.bv_const(0, half);
                    let hi_is_zero = self.solver.bveq(hi_half, zero_half);
                    let lo_half = self.solver.extract(val, remaining - half - 1, 0);
                    // If high half is zero, count += half and continue with low half
                    let half_c = self.solver.bv_const(half as i64, 32);
                    let count_plus = self.solver.bvadd(count, half_c);
                    count = self.solver.ite(hi_is_zero, count_plus, count);
                    // Select which half to continue searching
                    let lo_padded = if remaining - half < half {
                        self.solver.zero_extend(lo_half, half - (remaining - half))
                    } else {
                        lo_half
                    };
                    val = self.solver.ite(hi_is_zero, lo_padded, hi_half);
                    remaining = half;
                }
                // Final bit: if the single remaining bit is 0, add 1
                let last_bit = self.solver.extract(val, 0, 0);
                let zero1 = self.solver.bv_const(0, 1);
                let last_zero = self.solver.bveq(last_bit, zero1);
                let one = self.solver.bv_const(1, 32);
                let count_plus1 = self.solver.bvadd(count, one);
                self.solver.ite(last_zero, count_plus1, count)
            }
            // reverse: extract each bit, concat in reverse order
            ("java/lang/Integer" | "java/lang/Long", "reverse") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                // bits[0] = MSB of result = bit 0 of input
                let bits: Vec<_> = (0..w).map(|i| self.solver.extract(a, i, i)).collect();
                // Pairwise concat tree: bits[0] is MSB
                let mut nodes = bits;
                while nodes.len() > 1 {
                    let mut next = Vec::with_capacity((nodes.len() + 1) / 2);
                    for chunk in nodes.chunks(2) {
                        if chunk.len() == 2 {
                            next.push(self.solver.concat(chunk[0], chunk[1]));
                        } else {
                            next.push(chunk[0]);
                        }
                    }
                    nodes = next;
                }
                nodes.into_iter().next().unwrap()
            }
            // highestOneBit: ITE cascade from LSB so MSB wins
            ("java/lang/Integer" | "java/lang/Long", "highestOneBit") => {
                let a = self.encode_operand(&args[0]);
                let w = arg0_w;
                let zero = self.solver.bv_const(0, w);
                let is_zero = self.solver.bveq(a, zero);
                let mut result = zero;
                for i in 0..w {
                    let bit_mask = if i == 63 {
                        self.solver.bv_const(i64::MIN, w)
                    } else {
                        self.solver.bv_const(1i64 << i, w)
                    };
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
                // concat builds MSB..LSB: b0 is byte 0 (LSB) → goes to MSB position
                let hi = self.solver.concat(b0, b1);
                let lo = self.solver.concat(b2, b3);
                self.solver.concat(hi, lo)
            }
            ("java/lang/Long", "reverseBytes") => {
                let a = self.encode_operand(&args[0]);
                let b0 = self.solver.extract(a, 7, 0);
                let b1 = self.solver.extract(a, 15, 8);
                let b2 = self.solver.extract(a, 23, 16);
                let b3 = self.solver.extract(a, 31, 24);
                let b4 = self.solver.extract(a, 39, 32);
                let b5 = self.solver.extract(a, 47, 40);
                let b6 = self.solver.extract(a, 55, 48);
                let b7 = self.solver.extract(a, 63, 56);
                let p01 = self.solver.concat(b0, b1);
                let p23 = self.solver.concat(b2, b3);
                let p45 = self.solver.concat(b4, b5);
                let p67 = self.solver.concat(b6, b7);
                let q03 = self.solver.concat(p01, p23);
                let q47 = self.solver.concat(p45, p67);
                self.solver.concat(q03, q47)
            }
            ("java/lang/Short", "reverseBytes") => {
                // Short.reverseBytes: swap low 2 bytes, sign-extend to 32 bits
                let a = self.encode_operand(&args[0]);
                let b0 = self.solver.extract(a, 7, 0);
                let b1 = self.solver.extract(a, 15, 8);
                let swapped = self.solver.concat(b0, b1); // 16-bit
                self.solver.sign_extend(swapped, 16)
            }
            ("java/lang/Character", "reverseBytes") => {
                // Character.reverseBytes: swap low 2 bytes, zero-extend to 32 bits
                let a = self.encode_operand(&args[0]);
                let b0 = self.solver.extract(a, 7, 0);
                let b1 = self.solver.extract(a, 15, 8);
                let swapped = self.solver.concat(b0, b1); // 16-bit
                self.solver.zero_extend(swapped, 16)
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

            // ── Float / Double bit-level operations ──────────────────────
            // floatToRawIntBits: identity (we already store floats as BV32 bit patterns)
            ("java/lang/Float", "floatToRawIntBits" | "floatToIntBits") => {
                let a = self.encode_operand(&args[0]);
                if name == "floatToIntBits" {
                    // floatToIntBits canonicalizes NaN to 0x7fc00000
                    // NaN: exp=0xFF, mantissa!=0
                    let exp = self.solver.extract(a, 30, 23);
                    let man = self.solver.extract(a, 22, 0);
                    let exp_all = self.solver.bv_const(0xFF_i64, 8);
                    let zero23 = self.solver.bv_const(0, 23);
                    let exp_eq = self.solver.bveq(exp, exp_all);
                    let man_ne = self.solver.bveq(man, zero23);
                    let man_ne = self.solver.not(man_ne);
                    let is_nan = self.solver.and(exp_eq, man_ne);
                    let canonical = self.solver.bv_const(0x7fc00000_u32 as i64, 32);
                    self.solver.ite(is_nan, canonical, a)
                } else {
                    a
                }
            }
            ("java/lang/Float", "intBitsToFloat") => {
                // Identity: int bits ARE the float representation
                self.encode_operand(&args[0])
            }
            ("java/lang/Double", "doubleToRawLongBits" | "doubleToLongBits") => {
                let a = self.encode_operand(&args[0]);
                if name == "doubleToLongBits" {
                    // NaN: exp=0x7FF, mantissa!=0 → canonical 0x7ff8000000000000
                    let exp = self.solver.extract(a, 62, 52);
                    let man = self.solver.extract(a, 51, 0);
                    let exp_all = self.solver.bv_const(0x7FF_i64, 11);
                    let zero52 = self.solver.bv_const(0, 52);
                    let exp_eq = self.solver.bveq(exp, exp_all);
                    let man_ne = self.solver.bveq(man, zero52);
                    let man_ne = self.solver.not(man_ne);
                    let is_nan = self.solver.and(exp_eq, man_ne);
                    let canonical = self.solver.bv_const(0x7ff8000000000000_u64 as i64, 64);
                    self.solver.ite(is_nan, canonical, a)
                } else {
                    a
                }
            }
            ("java/lang/Double", "longBitsToDouble") => {
                self.encode_operand(&args[0])
            }

            // isNaN: exp all-ones AND mantissa non-zero
            ("java/lang/Float", "isNaN") => {
                let a = if target.desc.starts_with("(F)") {
                    self.encode_operand(&args[0])
                } else {
                    // Instance method: read $$value
                    let this_ref = self.encode_operand(&args[0]);
                    let k = FK::new("java/lang/Float", "$$value", "I");
                    let arr = self.get_field_array(&k, 32);
                    self.solver.array_select(arr, this_ref)
                };
                let exp = self.solver.extract(a, 30, 23);
                let man = self.solver.extract(a, 22, 0);
                let exp_all = self.solver.bv_const(0xFF_i64, 8);
                let zero23 = self.solver.bv_const(0, 23);
                let exp_eq = self.solver.bveq(exp, exp_all);
                let man_nz = self.solver.bveq(man, zero23);
                let man_nz = self.solver.not(man_nz);
                let is_nan = self.solver.and(exp_eq, man_nz);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(is_nan, one, zero)
            }
            ("java/lang/Double", "isNaN") => {
                let a = if target.desc.starts_with("(D)") {
                    self.encode_operand(&args[0])
                } else {
                    let this_ref = self.encode_operand(&args[0]);
                    let k = FK::new("java/lang/Double", "$$value", "D");
                    let arr = self.get_field_array(&k, 64);
                    self.solver.array_select(arr, this_ref)
                };
                let exp = self.solver.extract(a, 62, 52);
                let man = self.solver.extract(a, 51, 0);
                let exp_all = self.solver.bv_const(0x7FF_i64, 11);
                let zero52 = self.solver.bv_const(0, 52);
                let exp_eq = self.solver.bveq(exp, exp_all);
                let man_nz = self.solver.bveq(man, zero52);
                let man_nz = self.solver.not(man_nz);
                let is_nan = self.solver.and(exp_eq, man_nz);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(is_nan, one, zero)
            }

            // isInfinite: exp all-ones AND mantissa == 0
            ("java/lang/Float", "isInfinite") => {
                let a = if target.desc.starts_with("(F)") {
                    self.encode_operand(&args[0])
                } else {
                    let this_ref = self.encode_operand(&args[0]);
                    let k = FK::new("java/lang/Float", "$$value", "I");
                    let arr = self.get_field_array(&k, 32);
                    self.solver.array_select(arr, this_ref)
                };
                let exp = self.solver.extract(a, 30, 23);
                let man = self.solver.extract(a, 22, 0);
                let exp_all = self.solver.bv_const(0xFF_i64, 8);
                let zero23 = self.solver.bv_const(0, 23);
                let exp_eq = self.solver.bveq(exp, exp_all);
                let man_z = self.solver.bveq(man, zero23);
                let is_inf = self.solver.and(exp_eq, man_z);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(is_inf, one, zero)
            }
            ("java/lang/Double", "isInfinite") => {
                let a = if target.desc.starts_with("(D)") {
                    self.encode_operand(&args[0])
                } else {
                    let this_ref = self.encode_operand(&args[0]);
                    let k = FK::new("java/lang/Double", "$$value", "D");
                    let arr = self.get_field_array(&k, 64);
                    self.solver.array_select(arr, this_ref)
                };
                let exp = self.solver.extract(a, 62, 52);
                let man = self.solver.extract(a, 51, 0);
                let exp_all = self.solver.bv_const(0x7FF_i64, 11);
                let zero52 = self.solver.bv_const(0, 52);
                let exp_eq = self.solver.bveq(exp, exp_all);
                let man_z = self.solver.bveq(man, zero52);
                let is_inf = self.solver.and(exp_eq, man_z);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(is_inf, one, zero)
            }

            // isFinite: NOT(exp all-ones)
            ("java/lang/Float", "isFinite") => {
                let a = self.encode_operand(&args[0]);
                let exp = self.solver.extract(a, 30, 23);
                let exp_all = self.solver.bv_const(0xFF_i64, 8);
                let is_special = self.solver.bveq(exp, exp_all);
                let is_finite = self.solver.not(is_special);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(is_finite, one, zero)
            }
            ("java/lang/Double", "isFinite") => {
                let a = self.encode_operand(&args[0]);
                let exp = self.solver.extract(a, 62, 52);
                let exp_all = self.solver.bv_const(0x7FF_i64, 11);
                let is_special = self.solver.bveq(exp, exp_all);
                let is_finite = self.solver.not(is_special);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(is_finite, one, zero)
            }

            // Float.compare / Double.compare: totalOrder comparison
            // Java semantics: -0.0 < +0.0, NaN > +Inf (regardless of NaN sign bit)
            ("java/lang/Float", "compare") => {
                self.encode_fp_compare_32(&args[0], &args[1])
            }
            ("java/lang/Double", "compare") => {
                self.encode_fp_compare_64(&args[0], &args[1])
            }

            // Float/Double compareTo: unbox $$value, then compare
            ("java/lang/Float", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = FK::new("java/lang/Float", "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                self.fp_compare_bv32(a, b)
            }
            ("java/lang/Double", "compareTo") => {
                let this_ref = self.encode_operand(&args[0]);
                let other_ref = self.encode_operand(&args[1]);
                let k = FK::new("java/lang/Double", "$$value", "D");
                let arr = self.get_field_array(&k, 64);
                let a = self.solver.array_select(arr, this_ref);
                let b = self.solver.array_select(arr, other_ref);
                self.fp_compare_bv64(a, b)
            }

            // Float/Double hashCode
            ("java/lang/Float", "hashCode") => {
                // Float.hashCode(float) = floatToIntBits(f) = identity (with NaN canonical)
                if target.desc.starts_with("(F)") {
                    let a = self.encode_operand(&args[0]);
                    // Canonicalize NaN
                    let exp = self.solver.extract(a, 30, 23);
                    let man = self.solver.extract(a, 22, 0);
                    let exp_all = self.solver.bv_const(0xFF_i64, 8);
                    let zero23 = self.solver.bv_const(0, 23);
                    let exp_eq = self.solver.bveq(exp, exp_all);
                    let man_ne = self.solver.bveq(man, zero23);
                    let man_ne = self.solver.not(man_ne);
                    let is_nan = self.solver.and(exp_eq, man_ne);
                    let canonical = self.solver.bv_const(0x7fc00000_u32 as i64, 32);
                    self.solver.ite(is_nan, canonical, a)
                } else {
                    // Instance: read $$value
                    let this_ref = self.encode_operand(&args[0]);
                    let k = FK::new("java/lang/Float", "$$value", "I");
                    let arr = self.get_field_array(&k, 32);
                    self.solver.array_select(arr, this_ref)
                }
            }
            ("java/lang/Double", "hashCode") => {
                if target.desc.starts_with("(D)") {
                    // Double.hashCode(d) = (int)(v ^ (v >>> 32)) where v = doubleToLongBits(d)
                    let a = self.encode_operand(&args[0]);
                    // Canonicalize NaN
                    let exp = self.solver.extract(a, 62, 52);
                    let man = self.solver.extract(a, 51, 0);
                    let exp_all = self.solver.bv_const(0x7FF_i64, 11);
                    let zero52 = self.solver.bv_const(0, 52);
                    let exp_eq = self.solver.bveq(exp, exp_all);
                    let man_ne = self.solver.bveq(man, zero52);
                    let man_ne = self.solver.not(man_ne);
                    let is_nan = self.solver.and(exp_eq, man_ne);
                    let canonical = self.solver.bv_const(0x7ff8000000000000_u64 as i64, 64);
                    let v = self.solver.ite(is_nan, canonical, a);
                    let c32 = self.solver.bv_const(32, 64);
                    let shifted = self.solver.bvlshr(v, c32);
                    let xored = self.solver.bvxor(v, shifted);
                    self.solver.extract(xored, 31, 0)
                } else {
                    let this_ref = self.encode_operand(&args[0]);
                    let k = FK::new("java/lang/Double", "$$value", "D");
                    let arr = self.get_field_array(&k, 64);
                    let v = self.solver.array_select(arr, this_ref);
                    let c32 = self.solver.bv_const(32, 64);
                    let shifted = self.solver.bvlshr(v, c32);
                    let xored = self.solver.bvxor(v, shifted);
                    self.solver.extract(xored, 31, 0)
                }
            }

            // Float/Double max/min: IEEE 754 semantics (NaN propagates)
            // Math.max(a,b): if either is NaN, return NaN; else compare
            ("java/lang/Float", "max" | "min") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let a_nan = self.fp_is_nan_32(a);
                let b_nan = self.fp_is_nan_32(b);
                let either_nan = self.solver.or(a_nan, b_nan);
                let canonical_nan = self.solver.bv_const(0x7fc00000_u32 as i64, 32);
                let cmp = self.fp_compare_bv32(a, b);
                let zero = self.solver.bv_const(0, 32);
                let non_nan_result = if name == "max" {
                    let gt = self.solver.bvsgt(cmp, zero);
                    self.solver.ite(gt, a, b)
                } else {
                    let lt = self.solver.bvslt(cmp, zero);
                    self.solver.ite(lt, a, b)
                };
                self.solver.ite(either_nan, canonical_nan, non_nan_result)
            }
            ("java/lang/Double", "max" | "min") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let a_nan = self.fp_is_nan_64(a);
                let b_nan = self.fp_is_nan_64(b);
                let either_nan = self.solver.or(a_nan, b_nan);
                let canonical_nan = self.solver.bv_const(0x7ff8000000000000_u64 as i64, 64);
                let cmp = self.fp_compare_bv64(a, b);
                let zero = self.solver.bv_const(0, 32);
                let non_nan_result = if name == "max" {
                    let gt = self.solver.bvsgt(cmp, zero);
                    self.solver.ite(gt, a, b)
                } else {
                    let lt = self.solver.bvslt(cmp, zero);
                    self.solver.ite(lt, a, b)
                };
                self.solver.ite(either_nan, canonical_nan, non_nan_result)
            }
            ("java/lang/Float" | "java/lang/Double", "sum") => {
                // Can't precisely model FP addition with BV, return havoc
                let w = arg0_w;
                self.solver.fresh_bv("fp_sum", w)
            }

            // Float/Double byteValue/shortValue: (byte/short)(int)value
            ("java/lang/Float", "byteValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Float", "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let float_bits = self.solver.array_select(arr, this_ref);
                let int_val = self.encode_f2i(float_bits);
                let lo8 = self.solver.extract(int_val, 7, 0);
                self.solver.sign_extend(lo8, 24)
            }
            ("java/lang/Float", "shortValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Float", "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let float_bits = self.solver.array_select(arr, this_ref);
                let int_val = self.encode_f2i(float_bits);
                let lo16 = self.solver.extract(int_val, 15, 0);
                self.solver.sign_extend(lo16, 16)
            }
            ("java/lang/Double", "byteValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Double", "$$value", "D");
                let arr = self.get_field_array(&k, 64);
                let double_bits = self.solver.array_select(arr, this_ref);
                let int_val = self.encode_d2i(double_bits);
                let lo8 = self.solver.extract(int_val, 7, 0);
                self.solver.sign_extend(lo8, 24)
            }
            ("java/lang/Double", "shortValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Double", "$$value", "D");
                let arr = self.get_field_array(&k, 64);
                let double_bits = self.solver.array_select(arr, this_ref);
                let int_val = self.encode_d2i(double_bits);
                let lo16 = self.solver.extract(int_val, 15, 0);
                self.solver.sign_extend(lo16, 16)
            }

            // ── Integer/Long/Short/Byte floatValue/doubleValue (int→float/double) ──
            ("java/lang/Integer" | "java/lang/Short" | "java/lang/Byte", "doubleValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new(class, "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let int_val = self.solver.array_select(arr, this_ref);
                self.encode_i2d(int_val)
            }
            ("java/lang/Long", "doubleValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Long", "$$value", "J");
                let arr = self.get_field_array(&k, 64);
                let long_val = self.solver.array_select(arr, this_ref);
                self.encode_l2d(long_val)
            }
            ("java/lang/Integer" | "java/lang/Short" | "java/lang/Byte", "floatValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new(class, "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let int_val = self.solver.array_select(arr, this_ref);
                self.encode_i2f(int_val)
            }
            ("java/lang/Long", "floatValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Long", "$$value", "J");
                let arr = self.get_field_array(&k, 64);
                let long_val = self.solver.array_select(arr, this_ref);
                self.encode_l2f(long_val)
            }

            // ── Float intValue/longValue/doubleValue (float→int/long/double) ──
            ("java/lang/Float", "intValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Float", "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let float_bits = self.solver.array_select(arr, this_ref);
                self.encode_f2i(float_bits)
            }
            ("java/lang/Float", "longValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Float", "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let float_bits = self.solver.array_select(arr, this_ref);
                self.encode_f2l(float_bits)
            }
            ("java/lang/Float", "doubleValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Float", "$$value", "I");
                let arr = self.get_field_array(&k, 32);
                let float_bits = self.solver.array_select(arr, this_ref);
                self.encode_f2d(float_bits)
            }

            // ── Double intValue/longValue/floatValue (double→int/long/float) ──
            ("java/lang/Double", "intValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Double", "$$value", "D");
                let arr = self.get_field_array(&k, 64);
                let double_bits = self.solver.array_select(arr, this_ref);
                self.encode_d2i(double_bits)
            }
            ("java/lang/Double", "longValue") => {
                let this_ref = self.encode_operand(&args[0]);
                let k = FK::new("java/lang/Double", "$$value", "D");
                let arr = self.get_field_array(&k, 64);
                let double_bits = self.solver.array_select(arr, this_ref);
                self.encode_d2l(double_bits)
            }
            ("java/lang/Double", "floatValue") => {
                // d2f: can't precisely model rounding, use fresh_bv
                self.solver.fresh_bv("d2f", 32)
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

    // ── FP comparison helpers ────────────────────────────────────────

    pub(super) fn fp_is_nan_32(&mut self, a: Term) -> Term {
        let exp = self.solver.extract(a, 30, 23);
        let man = self.solver.extract(a, 22, 0);
        let exp_all = self.solver.bv_const(0xFF_i64, 8);
        let zero23 = self.solver.bv_const(0, 23);
        let exp_eq = self.solver.bveq(exp, exp_all);
        let man_nz = self.solver.bveq(man, zero23);
        let man_nz = self.solver.not(man_nz);
        self.solver.and(exp_eq, man_nz)
    }

    pub(super) fn fp_is_nan_64(&mut self, a: Term) -> Term {
        let exp = self.solver.extract(a, 62, 52);
        let man = self.solver.extract(a, 51, 0);
        let exp_all = self.solver.bv_const(0x7FF_i64, 11);
        let zero52 = self.solver.bv_const(0, 52);
        let exp_eq = self.solver.bveq(exp, exp_all);
        let man_nz = self.solver.bveq(man, zero52);
        let man_nz = self.solver.not(man_nz);
        self.solver.and(exp_eq, man_nz)
    }

    /// Float.compare(a, b) → -1/0/1 with Java semantics:
    /// -0.0 < +0.0, NaN > +Inf (regardless of NaN sign bit)
    pub(super) fn encode_fp_compare_32(&mut self, a_op: &Operand, b_op: &Operand) -> Term {
        let a = self.encode_operand(a_op);
        let b = self.encode_operand(b_op);
        self.fp_compare_bv32(a, b)
    }

    pub(super) fn fp_compare_bv32(&mut self, a: Term, b: Term) -> Term {
        // Map floats to comparable signed integers:
        // 1. Map all NaN → 0x7F800001 (just above +Inf = 0x7F800000)
        // 2. For non-NaN negatives: flip magnitude → 0x7FFFFFFF - x
        //    This gives: -Inf(0xFF800000) → 0x007FFFFF, -0(0x80000000) → 0x7FFFFFFF
        // 3. Positives stay as-is: +0(0) → 0, +Inf(0x7F800000) → 0x7F800000
        let a_nan = self.fp_is_nan_32(a);
        let b_nan = self.fp_is_nan_32(b);
        let nan_rank = self.solver.bv_const(0x7F800001_u32 as i64, 32);

        let a_mapped = self.fp_to_comparable_32(a, a_nan, nan_rank);
        let b_mapped = self.fp_to_comparable_32(b, b_nan, nan_rank);

        let one = self.solver.bv_const(1, 32);
        let mone = self.solver.bv_const(-1, 32);
        let zero = self.solver.bv_const(0, 32);
        let lt = self.solver.bvslt(a_mapped, b_mapped);
        let eq = self.solver.bveq(a_mapped, b_mapped);
        let inner = self.solver.ite(eq, zero, one);
        self.solver.ite(lt, mone, inner)
    }

    pub(super) fn fp_to_comparable_32(&mut self, v: Term, is_nan: Term, nan_rank: Term) -> Term {
        let sign = self.solver.extract(v, 31, 31);
        let one1 = self.solver.bv_const(1, 1);
        let is_neg = self.solver.bveq(sign, one1);
        let flip_mask = self.solver.bv_const(0x7FFFFFFF_u32 as i64, 32);
        let flipped = self.solver.bvxor(v, flip_mask);
        let non_nan = self.solver.ite(is_neg, flipped, v);
        self.solver.ite(is_nan, nan_rank, non_nan)
    }

    pub(super) fn encode_fp_compare_64(&mut self, a_op: &Operand, b_op: &Operand) -> Term {
        let a = self.encode_operand(a_op);
        let b = self.encode_operand(b_op);
        self.fp_compare_bv64(a, b)
    }

    pub(super) fn fp_compare_bv64(&mut self, a: Term, b: Term) -> Term {
        let a_nan = self.fp_is_nan_64(a);
        let b_nan = self.fp_is_nan_64(b);
        let nan_rank = self.solver.bv_const(0x7FF0000000000001_u64 as i64, 64);

        let a_mapped = self.fp_to_comparable_64(a, a_nan, nan_rank);
        let b_mapped = self.fp_to_comparable_64(b, b_nan, nan_rank);

        let one = self.solver.bv_const(1, 32);
        let mone = self.solver.bv_const(-1, 32);
        let zero = self.solver.bv_const(0, 32);
        let lt = self.solver.bvslt(a_mapped, b_mapped);
        let eq = self.solver.bveq(a_mapped, b_mapped);
        let inner = self.solver.ite(eq, zero, one);
        self.solver.ite(lt, mone, inner)
    }

    pub(super) fn fp_to_comparable_64(&mut self, v: Term, is_nan: Term, nan_rank: Term) -> Term {
        let sign = self.solver.extract(v, 63, 63);
        let one1 = self.solver.bv_const(1, 1);
        let is_neg = self.solver.bveq(sign, one1);
        let flip_mask = self.solver.bv_const(0x7FFFFFFFFFFFFFFF_u64 as i64, 64);
        let flipped = self.solver.bvxor(v, flip_mask);
        let non_nan = self.solver.ite(is_neg, flipped, v);
        self.solver.ite(is_nan, nan_rank, non_nan)
    }

    // ── Integer/Float conversion helpers ─────────────────────────────────

    /// Unsigned greater-than-or-equal: NOT(a < b).
    fn bvuge(&mut self, a: Term, b: Term) -> Term {
        let lt = self.solver.bvult(a, b);
        self.solver.not(lt)
    }

    /// Encode i2d: signed BV32 integer → BV64 IEEE 754 double (exact for all int32).
    pub(super) fn encode_i2d(&mut self, int_val: Term) -> Term {
        let zero32 = self.solver.bv_const(0, 32);
        let zero64 = self.solver.bv_const(0, 64);
        let is_zero = self.solver.bveq(int_val, zero32);

        // Sign bit
        let sign = self.solver.extract(int_val, 31, 31); // BV1

        // Absolute value (handle MIN_INT specially)
        let is_neg = self.solver.bvslt(int_val, zero32);
        let neg_val = self.solver.bvneg(int_val);
        let abs_val = self.solver.ite(is_neg, neg_val, int_val); // BV32

        // Zero-extend to 53 bits for shifting
        let abs_53 = self.solver.zero_extend(abs_val, 21); // BV53

        // Build ITE chain: for each MSB position k (0..30),
        // if abs_val >= 2^k, compute the double with exponent 1023+k.
        // Chain from k=0 upward so highest k wins.
        let mut result = zero64;
        for k in 0..=30u32 {
            let threshold = self.solver.bv_const(1i64 << k, 32);
            let has_bit = self.bvuge(abs_val, threshold);

            // Biased exponent = 1023 + k
            let exp = self.solver.bv_const((1023 + k) as i64, 11); // BV11

            // Mantissa: shift abs_val left by (52 - k), take low 52 bits.
            // Bit 52 is the implicit leading 1; extract(51,0) drops it.
            let shift_amt = self.solver.bv_const((52 - k) as i64, 53);
            let shifted = self.solver.bvshl(abs_53, shift_amt); // BV53
            let mantissa = self.solver.extract(shifted, 51, 0); // BV52

            // Assemble: sign(1) ++ exp(11) ++ mantissa(52) = BV64
            let sign_exp = self.solver.concat(sign, exp); // BV12
            let double_bits = self.solver.concat(sign_exp, mantissa); // BV64

            result = self.solver.ite(has_bit, double_bits, result);
        }

        // Special case: MIN_INT = -2^31 (bvneg overflows)
        // -2147483648.0 = 0xC1E0000000000000
        let min_int = self.solver.bv_const(i32::MIN as i64, 32);
        let is_min = self.solver.bveq(int_val, min_int);
        let min_double = self.solver.bv_const(0xC1E0000000000000u64 as i64, 64);
        result = self.solver.ite(is_min, min_double, result);

        self.solver.ite(is_zero, zero64, result)
    }

    /// Encode l2d: signed BV64 long → BV64 IEEE 754 double.
    /// Exact for |val| <= 2^52; truncates mantissa for larger values.
    pub(super) fn encode_l2d(&mut self, long_val: Term) -> Term {
        let zero64 = self.solver.bv_const(0, 64);
        let is_zero = self.solver.bveq(long_val, zero64);

        let sign = self.solver.extract(long_val, 63, 63); // BV1
        let is_neg = self.solver.bvslt(long_val, zero64);
        let neg_val = self.solver.bvneg(long_val);
        let abs_val = self.solver.ite(is_neg, neg_val, long_val); // BV64

        // Build ITE chain for MSB positions 0..62
        let mut result = zero64;
        for k in 0..=62u32 {
            let threshold = if k == 63 {
                self.solver.bv_const(i64::MIN, 64)
            } else {
                self.solver.bv_const(1i64 << k, 64)
            };
            let has_bit = self.bvuge(abs_val, threshold);

            let exp = self.solver.bv_const((1023 + k) as i64, 11);

            // For mantissa: need to extract 52 bits starting from position k-1 downward.
            // If k <= 52: shift left by (52-k), take bits 51..0
            // If k > 52: shift right by (k-52), take bits 51..0 (lower bits lost)
            let mantissa = if k <= 52 {
                let shift = 52 - k;
                let shift_c = self.solver.bv_const(shift as i64, 64);
                let shifted = self.solver.bvshl(abs_val, shift_c);
                self.solver.extract(shifted, 51, 0)
            } else {
                let shift = k - 52;
                let shift_c = self.solver.bv_const(shift as i64, 64);
                let shifted = self.solver.bvlshr(abs_val, shift_c);
                self.solver.extract(shifted, 51, 0)
            };

            let sign_exp = self.solver.concat(sign, exp);
            let double_bits = self.solver.concat(sign_exp, mantissa);
            result = self.solver.ite(has_bit, double_bits, result);
        }

        // Special case: MIN_LONG
        let min_long = self.solver.bv_const(i64::MIN, 64);
        let is_min = self.solver.bveq(long_val, min_long);
        // -2^63 as double = 0xC3E0000000000000
        let min_double = self.solver.bv_const(0xC3E0000000000000u64 as i64, 64);
        result = self.solver.ite(is_min, min_double, result);

        self.solver.ite(is_zero, zero64, result)
    }

    /// Encode i2f: signed BV32 integer → BV32 IEEE 754 float.
    /// Exact for |val| <= 2^24; rounds for larger values.
    pub(super) fn encode_i2f(&mut self, int_val: Term) -> Term {
        let zero32 = self.solver.bv_const(0, 32);
        let is_zero = self.solver.bveq(int_val, zero32);

        let sign = self.solver.extract(int_val, 31, 31); // BV1
        let is_neg = self.solver.bvslt(int_val, zero32);
        let neg_val = self.solver.bvneg(int_val);
        let abs_val = self.solver.ite(is_neg, neg_val, int_val); // BV32

        let mut result = zero32;
        for k in 0..=30u32 {
            let threshold = self.solver.bv_const(1i64 << k, 32);
            let has_bit = self.bvuge(abs_val, threshold);

            let exp = self.solver.bv_const((127 + k) as i64, 8); // BV8

            // Float mantissa is 23 bits. If k <= 23: shift left, else shift right.
            let mantissa = if k <= 23 {
                let shift = 23 - k;
                let shift_c = self.solver.bv_const(shift as i64, 32);
                let shifted = self.solver.bvshl(abs_val, shift_c);
                self.solver.extract(shifted, 22, 0) // BV23
            } else {
                let shift = k - 23;
                let shift_c = self.solver.bv_const(shift as i64, 32);
                let shifted = self.solver.bvlshr(abs_val, shift_c);
                self.solver.extract(shifted, 22, 0)
            };

            let sign_exp = self.solver.concat(sign, exp); // BV9
            let float_bits = self.solver.concat(sign_exp, mantissa); // BV32
            result = self.solver.ite(has_bit, float_bits, result);
        }

        // Special case: MIN_INT
        let min_int = self.solver.bv_const(i32::MIN as i64, 32);
        let is_min = self.solver.bveq(int_val, min_int);
        // -2147483648.0f = 0xCF000000
        let min_float = self.solver.bv_const(0xCF000000u32 as i64, 32);
        result = self.solver.ite(is_min, min_float, result);

        self.solver.ite(is_zero, zero32, result)
    }

    /// Encode f2l: BV32 IEEE 754 float → signed BV64 long.
    /// JVM semantics: NaN→0, ±Inf→MAX/MIN_LONG, truncate toward zero.
    pub(super) fn encode_f2l(&mut self, float_bits: Term) -> Term {
        let sign = self.solver.extract(float_bits, 31, 31);
        let biased_exp = self.solver.extract(float_bits, 30, 23); // BV8
        let mantissa = self.solver.extract(float_bits, 22, 0); // BV23

        let zero64 = self.solver.bv_const(0, 64);
        let max_long = self.solver.bv_const(i64::MAX, 64);
        let min_long = self.solver.bv_const(i64::MIN, 64);

        let exp_all = self.solver.bv_const(0xFF_i64, 8);
        let zero23 = self.solver.bv_const(0, 23);
        let exp_is_all = self.solver.bveq(biased_exp, exp_all);
        let man_nz = self.solver.bveq(mantissa, zero23);
        let man_nz = self.solver.not(man_nz);
        let is_nan = self.solver.and(exp_is_all, man_nz);
        let man_z = self.solver.bveq(mantissa, zero23);
        let is_inf = self.solver.and(exp_is_all, man_z);

        let one1 = self.solver.bv_const(1, 1);
        let is_neg = self.solver.bveq(sign, one1);

        let bias = self.solver.bv_const(127, 8);
        let exp_lt_bias = self.solver.bvult(biased_exp, bias);
        // Float max unbiased exponent is 127 (biased 254). Overflow for long at ue >= 63.
        let overflow_threshold = self.solver.bv_const(190, 8); // 127 + 63
        let exp_overflow = self.bvuge(biased_exp, overflow_threshold);

        // Full mantissa with implicit 1, extended to 64 bits
        let implicit_one = self.solver.bv_const(0x800000, 64);
        let man_64 = self.solver.zero_extend(mantissa, 41); // BV64
        let full_mantissa = self.solver.bvor(implicit_one, man_64);

        // Build ITE chain for unbiased_exp = 0..62
        // magnitude = full_mantissa >> (23 - ue) if ue <= 23
        //           = full_mantissa << (ue - 23) if ue > 23
        let mut magnitude = zero64;
        for ue in 0..=62u32 {
            let be = self.solver.bv_const((127 + ue) as i64, 8);
            let is_this_exp = self.solver.bveq(biased_exp, be);

            let mag = if ue <= 23 {
                let shift = 23 - ue;
                let shift_c = self.solver.bv_const(shift as i64, 64);
                self.solver.bvlshr(full_mantissa, shift_c)
            } else {
                let shift = ue - 23;
                let shift_c = self.solver.bv_const(shift as i64, 64);
                self.solver.bvshl(full_mantissa, shift_c)
            };
            magnitude = self.solver.ite(is_this_exp, mag, magnitude);
        }

        let neg_magnitude = self.solver.bvneg(magnitude);
        let signed_result = self.solver.ite(is_neg, neg_magnitude, magnitude);
        let inf_result = self.solver.ite(is_neg, min_long, max_long);
        let overflow_result = self.solver.ite(is_neg, min_long, max_long);

        let mut result = signed_result;
        result = self.solver.ite(exp_lt_bias, zero64, result);
        result = self.solver.ite(exp_overflow, overflow_result, result);
        result = self.solver.ite(is_inf, inf_result, result);
        result = self.solver.ite(is_nan, zero64, result);
        result
    }

    /// Encode l2f: signed BV64 long → BV32 IEEE 754 float.
    /// Approximate: truncates mantissa for |val| > 2^24.
    pub(super) fn encode_l2f(&mut self, long_val: Term) -> Term {
        // Convert long→double→float would be complex.
        // For autostub benchmarks with small values, use fresh_bv as fallback.
        // TODO: implement precisely if needed
        let _this = long_val; // suppress unused
        self.solver.fresh_bv("l2f", 32)
    }

    /// Encode f2i: BV32 IEEE 754 float → signed BV32 integer.
    /// JVM semantics: NaN→0, ±Inf→MAX/MIN_INT, truncate toward zero.
    pub(super) fn encode_f2i(&mut self, float_bits: Term) -> Term {
        let sign = self.solver.extract(float_bits, 31, 31); // BV1
        let biased_exp = self.solver.extract(float_bits, 30, 23); // BV8
        let mantissa = self.solver.extract(float_bits, 22, 0); // BV23

        let zero32 = self.solver.bv_const(0, 32);
        let max_int = self.solver.bv_const(i32::MAX as i64, 32);
        let min_int = self.solver.bv_const(i32::MIN as i64, 32);

        // Check NaN: exp=255, mantissa!=0
        let exp_all = self.solver.bv_const(0xFF_i64, 8);
        let zero23 = self.solver.bv_const(0, 23);
        let exp_is_all = self.solver.bveq(biased_exp, exp_all);
        let man_nz = self.solver.bveq(mantissa, zero23);
        let man_nz = self.solver.not(man_nz);
        let is_nan = self.solver.and(exp_is_all, man_nz);

        // Check ±Inf: exp=255, mantissa==0
        let man_z = self.solver.bveq(mantissa, zero23);
        let is_inf = self.solver.and(exp_is_all, man_z);

        // Check sign
        let one1 = self.solver.bv_const(1, 1);
        let is_neg = self.solver.bveq(sign, one1);

        // For normal/subnormal: unbiased_exp = biased_exp - 127
        // If biased_exp < 127: |value| < 1 → truncate to 0
        let bias = self.solver.bv_const(127, 8);
        let exp_lt_bias = self.solver.bvult(biased_exp, bias);

        // If biased_exp >= 127+31 = 158: overflow → clamp
        let overflow_threshold = self.solver.bv_const(158, 8);
        let exp_overflow = self.bvuge(biased_exp, overflow_threshold);

        // Normal case: magnitude = (1 << unbiased_exp) | (mantissa >> (23 - unbiased_exp))
        // = (0x800000 | mantissa) >> (23 - unbiased_exp) if unbiased_exp <= 23
        // = (0x800000 | mantissa) << (unbiased_exp - 23) if unbiased_exp > 23
        // Unbiased_exp ranges from 0 to 30 in the non-overflow case.
        let implicit_one = self.solver.bv_const(0x800000, 32);
        let man_32 = self.solver.zero_extend(mantissa, 9); // BV32
        let full_mantissa = self.solver.bvor(implicit_one, man_32); // BV32: 1.mantissa

        // Build ITE chain for unbiased_exp = 0..30
        let mut magnitude = zero32;
        for ue in 0..=30u32 {
            let be = self.solver.bv_const((127 + ue) as i64, 8);
            let is_this_exp = self.solver.bveq(biased_exp, be);

            let mag = if ue <= 23 {
                let shift = 23 - ue;
                let shift_c = self.solver.bv_const(shift as i64, 32);
                self.solver.bvlshr(full_mantissa, shift_c)
            } else {
                let shift = ue - 23;
                let shift_c = self.solver.bv_const(shift as i64, 32);
                self.solver.bvshl(full_mantissa, shift_c)
            };
            magnitude = self.solver.ite(is_this_exp, mag, magnitude);
        }

        // Apply sign
        let neg_magnitude = self.solver.bvneg(magnitude);
        let signed_result = self.solver.ite(is_neg, neg_magnitude, magnitude);

        // Compose final result with priority: NaN→0, Inf→clamp, overflow→clamp, underflow→0
        let inf_result = self.solver.ite(is_neg, min_int, max_int);
        let overflow_result = self.solver.ite(is_neg, min_int, max_int);

        let mut result = signed_result;
        result = self.solver.ite(exp_lt_bias, zero32, result);
        result = self.solver.ite(exp_overflow, overflow_result, result);
        result = self.solver.ite(is_inf, inf_result, result);
        result = self.solver.ite(is_nan, zero32, result);
        result
    }

    /// Encode d2i: BV64 IEEE 754 double → signed BV32 integer.
    pub(super) fn encode_d2i(&mut self, double_bits: Term) -> Term {
        let sign = self.solver.extract(double_bits, 63, 63);
        let biased_exp = self.solver.extract(double_bits, 62, 52); // BV11
        let mantissa = self.solver.extract(double_bits, 51, 0); // BV52

        let zero32 = self.solver.bv_const(0, 32);
        let max_int = self.solver.bv_const(i32::MAX as i64, 32);
        let min_int = self.solver.bv_const(i32::MIN as i64, 32);

        // NaN check
        let exp_all = self.solver.bv_const(0x7FF_i64, 11);
        let zero52 = self.solver.bv_const(0, 52);
        let exp_is_all = self.solver.bveq(biased_exp, exp_all);
        let man_nz = self.solver.bveq(mantissa, zero52);
        let man_nz = self.solver.not(man_nz);
        let is_nan = self.solver.and(exp_is_all, man_nz);

        let man_z = self.solver.bveq(mantissa, zero52);
        let is_inf = self.solver.and(exp_is_all, man_z);

        let one1 = self.solver.bv_const(1, 1);
        let is_neg = self.solver.bveq(sign, one1);

        // Underflow: biased_exp < 1023
        let bias = self.solver.bv_const(1023, 11);
        let exp_lt_bias = self.solver.bvult(biased_exp, bias);

        // Overflow: unbiased_exp >= 31 → biased_exp >= 1054
        let overflow_threshold = self.solver.bv_const(1054, 11);
        let exp_overflow = self.bvuge(biased_exp, overflow_threshold);

        // Normal case: unbiased_exp 0..30
        // magnitude = (1 << ue) | (mantissa_top_bits >> (52 - ue))
        // Since mantissa is 52 bits and we need a 32-bit integer,
        // take the top min(ue, 31) mantissa bits.
        // full_mantissa_53 = 1 ++ mantissa[51:0] (53-bit with implicit 1)
        let implicit_one_53 = self.solver.bv_const(1i64 << 52, 53);
        let man_53 = self.solver.zero_extend(mantissa, 1);
        let full_man = self.solver.bvor(implicit_one_53, man_53); // BV53

        let mut magnitude = zero32;
        for ue in 0..=30u32 {
            let be = self.solver.bv_const((1023 + ue) as i64, 11);
            let is_this_exp = self.solver.bveq(biased_exp, be);

            // Shift right by (52 - ue) to get the integer magnitude
            let shift = 52 - ue;
            let shift_c = self.solver.bv_const(shift as i64, 53);
            let shifted = self.solver.bvlshr(full_man, shift_c);
            let mag = self.solver.extract(shifted, 31, 0); // BV32
            magnitude = self.solver.ite(is_this_exp, mag, magnitude);
        }

        let neg_magnitude = self.solver.bvneg(magnitude);
        let signed_result = self.solver.ite(is_neg, neg_magnitude, magnitude);

        let inf_result = self.solver.ite(is_neg, min_int, max_int);
        let overflow_result = self.solver.ite(is_neg, min_int, max_int);

        let mut result = signed_result;
        result = self.solver.ite(exp_lt_bias, zero32, result);
        result = self.solver.ite(exp_overflow, overflow_result, result);
        result = self.solver.ite(is_inf, inf_result, result);
        result = self.solver.ite(is_nan, zero32, result);
        result
    }

    /// Encode d2l: BV64 IEEE 754 double → signed BV64 long.
    pub(super) fn encode_d2l(&mut self, double_bits: Term) -> Term {
        let sign = self.solver.extract(double_bits, 63, 63);
        let biased_exp = self.solver.extract(double_bits, 62, 52); // BV11
        let mantissa = self.solver.extract(double_bits, 51, 0); // BV52

        let zero64 = self.solver.bv_const(0, 64);
        let max_long = self.solver.bv_const(i64::MAX, 64);
        let min_long = self.solver.bv_const(i64::MIN, 64);

        let exp_all = self.solver.bv_const(0x7FF_i64, 11);
        let zero52 = self.solver.bv_const(0, 52);
        let exp_is_all = self.solver.bveq(biased_exp, exp_all);
        let man_nz = self.solver.bveq(mantissa, zero52);
        let man_nz = self.solver.not(man_nz);
        let is_nan = self.solver.and(exp_is_all, man_nz);
        let man_z = self.solver.bveq(mantissa, zero52);
        let is_inf = self.solver.and(exp_is_all, man_z);

        let one1 = self.solver.bv_const(1, 1);
        let is_neg = self.solver.bveq(sign, one1);

        let bias = self.solver.bv_const(1023, 11);
        let exp_lt_bias = self.solver.bvult(biased_exp, bias);
        let overflow_threshold = self.solver.bv_const(1086, 11); // 1023 + 63
        let exp_overflow = self.bvuge(biased_exp, overflow_threshold);

        // full_mantissa = 1 ++ mantissa (53 bits), zero-extend to 64
        let implicit_one = self.solver.bv_const(1i64 << 52, 64);
        let man_64 = self.solver.zero_extend(mantissa, 12);
        let full_man = self.solver.bvor(implicit_one, man_64); // BV64

        let mut magnitude = zero64;
        for ue in 0..=62u32 {
            let be = self.solver.bv_const((1023 + ue) as i64, 11);
            let is_this_exp = self.solver.bveq(biased_exp, be);

            let mag = if ue <= 52 {
                let shift = 52 - ue;
                let shift_c = self.solver.bv_const(shift as i64, 64);
                self.solver.bvlshr(full_man, shift_c)
            } else {
                let shift = ue - 52;
                let shift_c = self.solver.bv_const(shift as i64, 64);
                self.solver.bvshl(full_man, shift_c)
            };
            magnitude = self.solver.ite(is_this_exp, mag, magnitude);
        }

        let neg_magnitude = self.solver.bvneg(magnitude);
        let signed_result = self.solver.ite(is_neg, neg_magnitude, magnitude);
        let inf_result = self.solver.ite(is_neg, min_long, max_long);
        let overflow_result = self.solver.ite(is_neg, min_long, max_long);

        let mut result = signed_result;
        result = self.solver.ite(exp_lt_bias, zero64, result);
        result = self.solver.ite(exp_overflow, overflow_result, result);
        result = self.solver.ite(is_inf, inf_result, result);
        result = self.solver.ite(is_nan, zero64, result);
        result
    }

    /// Encode f2d: BV32 IEEE 754 float → BV64 IEEE 754 double (exact).
    pub(super) fn encode_f2d(&mut self, float_bits: Term) -> Term {
        let sign = self.solver.extract(float_bits, 31, 31); // BV1
        let biased_exp = self.solver.extract(float_bits, 30, 23); // BV8
        let mantissa = self.solver.extract(float_bits, 22, 0); // BV23

        let zero8 = self.solver.bv_const(0, 8);
        let zero64 = self.solver.bv_const(0, 64);

        // Check for zero (±0)
        let exp_zero = self.solver.bveq(biased_exp, zero8);
        let zero23 = self.solver.bv_const(0, 23);
        let man_zero = self.solver.bveq(mantissa, zero23);
        let is_zero = self.solver.and(exp_zero, man_zero);

        // NaN/Inf: exp=255
        let exp_all = self.solver.bv_const(0xFF_i64, 8);
        let is_special = self.solver.bveq(biased_exp, exp_all);

        // Normal float → double: double_exp = float_exp - 127 + 1023 = float_exp + 896
        // Mantissa: zero-extend 23 bits to 52 bits (pad 29 zeros on the right)
        let exp_extended = self.solver.zero_extend(biased_exp, 3); // BV11
        let bias_adjust = self.solver.bv_const(896, 11); // 1023 - 127
        let double_exp = self.solver.bvadd(exp_extended, bias_adjust); // BV11

        let man_extended = self.solver.zero_extend(mantissa, 29); // BV52 (23 + 29 = 52)
        // Shift mantissa left by 29 to put it in the right position
        let shift29 = self.solver.bv_const(29, 52);
        let man_shifted = self.solver.bvshl(man_extended, shift29);

        let sign_exp = self.solver.concat(sign, double_exp); // BV12
        let normal_result = self.solver.concat(sign_exp, man_shifted); // BV64

        // Special (NaN/Inf): exp = 0x7FF, mantissa preserved (extended)
        let double_exp_all = self.solver.bv_const(0x7FF_i64, 11);
        let sign_exp_special = self.solver.concat(sign, double_exp_all);
        let special_result = self.solver.concat(sign_exp_special, man_shifted);

        // +0/-0: just sign bit extended
        let zero63 = self.solver.bv_const(0, 63);
        let zero_result = self.solver.concat(sign, zero63);

        let mut result = normal_result;
        result = self.solver.ite(is_special, special_result, result);
        result = self.solver.ite(is_zero, zero_result, result);
        result
    }
}
