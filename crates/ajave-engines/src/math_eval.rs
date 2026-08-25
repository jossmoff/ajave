//! Concrete evaluation of Math, Integer, Long, Character, Short, Byte,
//! Boolean, Double, and Float utility method calls.
//!
//! Extracted from `concrete.rs` for modularity.

use std::collections::HashMap;

use ajave_ir::*;

use crate::concrete::Value;

/// Check if a method is a math/utility call that the concrete engine can evaluate.
pub(crate) fn is_concrete_math_call(owner: &str, name: &str) -> bool {
    match owner {
        "java/lang/Math" | "java/lang/StrictMath" => matches!(
            name,
            "abs" | "min" | "max" | "addExact" | "subtractExact"
                | "multiplyExact" | "negateExact" | "floorDiv" | "floorMod"
                | "round"
        ),
        "java/lang/Integer" => matches!(
            name,
            "parseInt" | "max" | "min" | "sum" | "reverse" | "reverseBytes"
                | "numberOfLeadingZeros" | "numberOfTrailingZeros" | "bitCount"
                | "highestOneBit" | "lowestOneBit" | "signum" | "toUnsignedLong"
                | "divideUnsigned" | "remainderUnsigned" | "compareUnsigned"
                | "hashCode" | "compare"
        ),
        "java/lang/Long" => matches!(
            name,
            "parseLong" | "max" | "min" | "sum" | "signum"
                | "divideUnsigned" | "remainderUnsigned" | "compareUnsigned"
                | "hashCode" | "compare"
        ),
        "java/lang/Character" => matches!(
            name,
            "isDigit" | "isLetter" | "isLetterOrDigit" | "isUpperCase" | "isLowerCase"
                | "isWhitespace" | "isSpaceChar" | "isAlphabetic" | "isBmpCodePoint"
                | "isSupplementaryCodePoint" | "isHighSurrogate" | "isLowSurrogate"
                | "isSurrogate" | "isSurrogatePair" | "isValidCodePoint"
                | "toUpperCase" | "toLowerCase" | "toTitleCase"
                | "getNumericValue" | "getType" | "digit" | "forDigit"
                | "charCount" | "codePointAt" | "codePointBefore" | "codePointCount"
                | "compare" | "hashCode" | "reverseBytes"
                | "highSurrogate" | "lowSurrogate" | "toCodePoint" | "toChars"
                | "isISOControl" | "isMirrored" | "isDefined" | "isTitleCase"
                | "isJavaIdentifierStart" | "isJavaIdentifierPart"
                | "isUnicodeIdentifierStart" | "isUnicodeIdentifierPart"
        ),
        "java/lang/Short" => matches!(
            name,
            "parseShort" | "compare" | "hashCode" | "reverseBytes" | "toUnsignedInt" | "toUnsignedLong"
        ),
        "java/lang/Byte" => matches!(
            name,
            "parseByte" | "compare" | "hashCode" | "toUnsignedInt" | "toUnsignedLong"
        ),
        "java/lang/Boolean" => matches!(
            name,
            "logicalAnd" | "logicalOr" | "logicalXor" | "compare" | "hashCode"
        ),
        "java/lang/Double" => matches!(name, "compare" | "hashCode" | "isNaN" | "isInfinite" | "isFinite"),
        "java/lang/Float" => matches!(name, "compare" | "hashCode" | "isNaN" | "isInfinite" | "isFinite"),
        _ => false,
    }
}

/// Evaluate a math/utility call concretely.
pub(crate) fn eval_math_call(
    target: &MethodKey,
    args: &[Operand],
    store: &HashMap<VarId, Value>,
) -> Value {
    let get_val = |i: usize| -> Value {
        match args.get(i) {
            Some(Operand::Var(vid)) => store.get(vid).copied().unwrap_or(Value::Unknown),
            Some(Operand::Const(Const::Int(n))) => Value::I32(*n),
            Some(Operand::Const(Const::Long(n))) => Value::I64(*n),
            _ => Value::Unknown,
        }
    };
    let get_i32 = |i: usize| -> Option<i32> {
        match get_val(i) {
            Value::I32(v) => Some(v),
            _ => None,
        }
    };
    let get_i64 = |i: usize| -> Option<i64> {
        match get_val(i) {
            Value::I64(v) => Some(v),
            Value::I32(v) => Some(v as i64),
            _ => None,
        }
    };

    let owner = target.class.as_str();
    let name = target.name.as_str();

    match owner {
        "java/lang/Math" | "java/lang/StrictMath" => {
            match name {
                "abs" => match get_val(0) {
                    Value::I32(v) => Value::I32(v.wrapping_abs()),
                    Value::I64(v) => Value::I64(v.wrapping_abs()),
                    _ => Value::Unknown,
                },
                "min" => match (get_val(0), get_val(1)) {
                    (Value::I32(a), Value::I32(b)) => Value::I32(a.min(b)),
                    (Value::I64(a), Value::I64(b)) => Value::I64(a.min(b)),
                    _ => Value::Unknown,
                },
                "max" => match (get_val(0), get_val(1)) {
                    (Value::I32(a), Value::I32(b)) => Value::I32(a.max(b)),
                    (Value::I64(a), Value::I64(b)) => Value::I64(a.max(b)),
                    _ => Value::Unknown,
                },
                "addExact" => match (get_val(0), get_val(1)) {
                    (Value::I32(a), Value::I32(b)) => match a.checked_add(b) {
                        Some(r) => Value::I32(r),
                        None => Value::Unknown, // ArithmeticException
                    },
                    (Value::I64(a), Value::I64(b)) => match a.checked_add(b) {
                        Some(r) => Value::I64(r),
                        None => Value::Unknown,
                    },
                    _ => Value::Unknown,
                },
                "subtractExact" => match (get_val(0), get_val(1)) {
                    (Value::I32(a), Value::I32(b)) => match a.checked_sub(b) {
                        Some(r) => Value::I32(r),
                        None => Value::Unknown,
                    },
                    (Value::I64(a), Value::I64(b)) => match a.checked_sub(b) {
                        Some(r) => Value::I64(r),
                        None => Value::Unknown,
                    },
                    _ => Value::Unknown,
                },
                "multiplyExact" => match (get_val(0), get_val(1)) {
                    (Value::I32(a), Value::I32(b)) => match a.checked_mul(b) {
                        Some(r) => Value::I32(r),
                        None => Value::Unknown,
                    },
                    (Value::I64(a), Value::I64(b)) => match a.checked_mul(b) {
                        Some(r) => Value::I64(r),
                        None => Value::Unknown,
                    },
                    _ => Value::Unknown,
                },
                "negateExact" => match get_val(0) {
                    Value::I32(v) => match v.checked_neg() {
                        Some(r) => Value::I32(r),
                        None => Value::Unknown,
                    },
                    Value::I64(v) => match v.checked_neg() {
                        Some(r) => Value::I64(r),
                        None => Value::Unknown,
                    },
                    _ => Value::Unknown,
                },
                "floorDiv" => match (get_i32(0), get_i32(1)) {
                    (Some(a), Some(b)) if b != 0 => Value::I32(a.div_euclid(b)),
                    _ => match (get_i64(0), get_i64(1)) {
                        (Some(a), Some(b)) if b != 0 => Value::I64(a.div_euclid(b)),
                        _ => Value::Unknown,
                    },
                },
                "floorMod" => match (get_i32(0), get_i32(1)) {
                    (Some(a), Some(b)) if b != 0 => Value::I32(a.rem_euclid(b)),
                    _ => match (get_i64(0), get_i64(1)) {
                        (Some(a), Some(b)) if b != 0 => Value::I64(a.rem_euclid(b)),
                        _ => Value::Unknown,
                    },
                },
                "round" => {
                    // Java: Math.round(float) = (int) Math.floor(x + 0.5f)
                    //       Math.round(double) = (long) Math.floor(x + 0.5d)
                    if target.desc.starts_with("(D)") {
                        match get_i64(0) {
                            Some(bits) => {
                                let d = f64::from_bits(bits as u64);
                                Value::I64((d + 0.5_f64).floor() as i64)
                            }
                            None => Value::Unknown,
                        }
                    } else {
                        match get_i32(0) {
                            Some(bits) => {
                                let f = f32::from_bits(bits as u32);
                                Value::I32((f + 0.5_f32).floor() as i32)
                            }
                            None => Value::Unknown,
                        }
                    }
                },
                _ => Value::Unknown,
            }
        }
        "java/lang/Integer" => match name {
            "sum" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32(a.wrapping_add(b)),
                _ => Value::Unknown,
            },
            "max" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32(a.max(b)),
                _ => Value::Unknown,
            },
            "min" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32(a.min(b)),
                _ => Value::Unknown,
            },
            "reverse" => match get_i32(0) {
                Some(v) => Value::I32((v as u32).reverse_bits() as i32),
                None => Value::Unknown,
            },
            "reverseBytes" => match get_i32(0) {
                Some(v) => Value::I32((v as u32).swap_bytes() as i32),
                None => Value::Unknown,
            },
            "numberOfLeadingZeros" => match get_i32(0) {
                Some(v) => Value::I32((v as u32).leading_zeros() as i32),
                None => Value::Unknown,
            },
            "numberOfTrailingZeros" => match get_i32(0) {
                Some(v) => Value::I32((v as u32).trailing_zeros() as i32),
                None => Value::Unknown,
            },
            "bitCount" => match get_i32(0) {
                Some(v) => Value::I32((v as u32).count_ones() as i32),
                None => Value::Unknown,
            },
            "highestOneBit" => match get_i32(0) {
                Some(0) => Value::I32(0),
                Some(v) => Value::I32(1i32 << (31 - (v as u32).leading_zeros() as i32)),
                None => Value::Unknown,
            },
            "lowestOneBit" => match get_i32(0) {
                Some(v) => Value::I32(v & v.wrapping_neg()),
                None => Value::Unknown,
            },
            "signum" => match get_i32(0) {
                Some(v) => Value::I32(v.signum()),
                None => Value::Unknown,
            },
            "toUnsignedLong" => match get_i32(0) {
                Some(v) => Value::I64((v as u32) as i64),
                None => Value::Unknown,
            },
            "divideUnsigned" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) if b != 0 => Value::I32(((a as u32) / (b as u32)) as i32),
                _ => Value::Unknown,
            },
            "remainderUnsigned" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) if b != 0 => Value::I32(((a as u32) % (b as u32)) as i32),
                _ => Value::Unknown,
            },
            "compareUnsigned" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32((a as u32).cmp(&(b as u32)) as i32),
                _ => Value::Unknown,
            },
            "compare" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32(a.cmp(&b) as i32),
                _ => Value::Unknown,
            },
            "hashCode" => match get_i32(0) {
                Some(v) => Value::I32(v),
                None => Value::Unknown,
            },
            "parseInt" => Value::Unknown,
            _ => Value::Unknown,
        },
        "java/lang/Long" => match name {
            "sum" => match (get_i64(0), get_i64(1)) {
                (Some(a), Some(b)) => Value::I64(a.wrapping_add(b)),
                _ => Value::Unknown,
            },
            "max" => match (get_i64(0), get_i64(1)) {
                (Some(a), Some(b)) => Value::I64(a.max(b)),
                _ => Value::Unknown,
            },
            "min" => match (get_i64(0), get_i64(1)) {
                (Some(a), Some(b)) => Value::I64(a.min(b)),
                _ => Value::Unknown,
            },
            "signum" => match get_i64(0) {
                Some(v) => Value::I64(v.signum()),
                None => Value::Unknown,
            },
            "compare" => match (get_i64(0), get_i64(1)) {
                (Some(a), Some(b)) => Value::I32(a.cmp(&b) as i32),
                _ => Value::Unknown,
            },
            "hashCode" => match get_i64(0) {
                Some(v) => Value::I32((v ^ (v >> 32)) as i32),
                None => Value::Unknown,
            },
            "divideUnsigned" => match (get_i64(0), get_i64(1)) {
                (Some(a), Some(b)) if b != 0 => Value::I64(((a as u64) / (b as u64)) as i64),
                _ => Value::Unknown,
            },
            "remainderUnsigned" => match (get_i64(0), get_i64(1)) {
                (Some(a), Some(b)) if b != 0 => Value::I64(((a as u64) % (b as u64)) as i64),
                _ => Value::Unknown,
            },
            "compareUnsigned" => match (get_i64(0), get_i64(1)) {
                (Some(a), Some(b)) => Value::I32((a as u64).cmp(&(b as u64)) as i32),
                _ => Value::Unknown,
            },
            "parseLong" => Value::Unknown,
            _ => Value::Unknown,
        },
        "java/lang/Character" => {
            let ch = match get_i32(0) {
                Some(v) => v,
                None => return Value::Unknown,
            };
            let c = char::from_u32(ch as u32);
            match name {
                "isDigit" => Value::I32(c.map(|c| c.is_ascii_digit()).unwrap_or(false) as i32),
                "isLetter" => Value::I32(c.map(|c| c.is_alphabetic()).unwrap_or(false) as i32),
                "isLetterOrDigit" => Value::I32(c.map(|c| c.is_alphanumeric()).unwrap_or(false) as i32),
                "isUpperCase" => Value::I32(c.map(|c| c.is_uppercase()).unwrap_or(false) as i32),
                "isLowerCase" => Value::I32(c.map(|c| c.is_lowercase()).unwrap_or(false) as i32),
                "isWhitespace" => Value::I32(c.map(|c| c.is_whitespace()).unwrap_or(false) as i32),
                "isSpaceChar" => Value::I32(c.map(|c| c == ' ' || c == '\u{a0}' || c == '\u{2007}' || c == '\u{202f}').unwrap_or(false) as i32),
                "isAlphabetic" => Value::I32(c.map(|c| c.is_alphabetic()).unwrap_or(false) as i32),
                "toUpperCase" => Value::I32(c.map(|c| c.to_uppercase().next().unwrap_or(c) as i32).unwrap_or(ch)),
                "toLowerCase" => Value::I32(c.map(|c| c.to_lowercase().next().unwrap_or(c) as i32).unwrap_or(ch)),
                "toTitleCase" => Value::I32(c.map(|c| c.to_uppercase().next().unwrap_or(c) as i32).unwrap_or(ch)),
                "isBmpCodePoint" => Value::I32(if (ch as u32) <= 0xFFFF { 1 } else { 0 }),
                "isSupplementaryCodePoint" => Value::I32(if (ch as u32) >= 0x10000 && (ch as u32) <= 0x10FFFF { 1 } else { 0 }),
                "isHighSurrogate" => Value::I32(if (ch as u32) >= 0xD800 && (ch as u32) <= 0xDBFF { 1 } else { 0 }),
                "isLowSurrogate" => Value::I32(if (ch as u32) >= 0xDC00 && (ch as u32) <= 0xDFFF { 1 } else { 0 }),
                "isSurrogate" => Value::I32(if (ch as u32) >= 0xD800 && (ch as u32) <= 0xDFFF { 1 } else { 0 }),
                "isValidCodePoint" => Value::I32(if (ch as u32) <= 0x10FFFF { 1 } else { 0 }),
                "charCount" => Value::I32(if (ch as u32) >= 0x10000 { 2 } else { 1 }),
                "compare" => match get_i32(1) {
                    Some(b) => Value::I32((ch as u16 as i32) - (b as u16 as i32)),
                    None => Value::Unknown,
                },
                "hashCode" => Value::I32(ch),
                "reverseBytes" => Value::I32(((ch as u16).swap_bytes()) as i32),
                "digit" => match get_i32(1) {
                    Some(radix) if radix >= 2 && radix <= 36 => {
                        let d = char::from_u32(ch as u32).and_then(|c| c.to_digit(radix as u32));
                        Value::I32(d.map(|d| d as i32).unwrap_or(-1))
                    }
                    _ => Value::Unknown,
                },
                "getNumericValue" => {
                    let d = char::from_u32(ch as u32).and_then(|c| c.to_digit(10));
                    Value::I32(d.map(|d| d as i32).unwrap_or(-1))
                },
                "isSurrogatePair" => match get_i32(1) {
                    Some(lo) => {
                        let hi_ok = (ch as u32) >= 0xD800 && (ch as u32) <= 0xDBFF;
                        let lo_ok = (lo as u32) >= 0xDC00 && (lo as u32) <= 0xDFFF;
                        Value::I32((hi_ok && lo_ok) as i32)
                    }
                    None => Value::Unknown,
                },
                "toCodePoint" => match get_i32(1) {
                    Some(lo) => {
                        let cp = ((ch as u32 - 0xD800) << 10) + (lo as u32 - 0xDC00) + 0x10000;
                        Value::I32(cp as i32)
                    }
                    None => Value::Unknown,
                },
                "highSurrogate" => {
                    let cp = ch as u32;
                    Value::I32(((cp >> 10) + 0xD7C0) as i32)
                },
                "lowSurrogate" => {
                    let cp = ch as u32;
                    Value::I32(((cp & 0x3FF) + 0xDC00) as i32)
                },
                "isISOControl" => Value::I32(if (ch as u32) <= 0x1F || ((ch as u32) >= 0x7F && (ch as u32) <= 0x9F) { 1 } else { 0 }),
                "isDefined" => Value::I32(c.is_some() as i32),
                "isTitleCase" => Value::I32(0), // approximate: Java has specific titlecase chars
                "isMirrored" => Value::I32(0), // approximate
                "isJavaIdentifierStart" => Value::I32(c.map(|c| c.is_alphabetic() || c == '_' || c == '$').unwrap_or(false) as i32),
                "isJavaIdentifierPart" => {
                    let is_part = c.map(|c| {
                        let cp = c as u32;
                        c.is_alphanumeric() || c == '_' || c == '$'
                            // isIdentifierIgnorable: 0x00-0x08, 0x0E-0x1B, 0x7F-0x9F
                            || cp <= 0x08
                            || (cp >= 0x0E && cp <= 0x1B)
                            || (cp >= 0x7F && cp <= 0x9F)
                    }).unwrap_or(false);
                    Value::I32(is_part as i32)
                },
                "isUnicodeIdentifierStart" => Value::I32(c.map(|c| c.is_alphabetic()).unwrap_or(false) as i32),
                "isUnicodeIdentifierPart" => Value::I32(c.map(|c| c.is_alphanumeric() || c == '_').unwrap_or(false) as i32),
                _ => Value::Unknown,
            }
        }
        "java/lang/Short" => match name {
            "parseShort" => Value::Unknown,
            "compare" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32((a as i16).cmp(&(b as i16)) as i32),
                _ => Value::Unknown,
            },
            "hashCode" => match get_i32(0) {
                Some(v) => Value::I32(v as i16 as i32),
                None => Value::Unknown,
            },
            "reverseBytes" => match get_i32(0) {
                Some(v) => Value::I32((v as u16).swap_bytes() as i16 as i32),
                None => Value::Unknown,
            },
            "toUnsignedInt" => match get_i32(0) {
                Some(v) => Value::I32((v as u16) as i32),
                None => Value::Unknown,
            },
            "toUnsignedLong" => match get_i32(0) {
                Some(v) => Value::I64((v as u16) as i64),
                None => Value::Unknown,
            },
            _ => Value::Unknown,
        },
        "java/lang/Byte" => match name {
            "parseByte" => Value::Unknown,
            "compare" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32((a as i8).cmp(&(b as i8)) as i32),
                _ => Value::Unknown,
            },
            "hashCode" => match get_i32(0) {
                Some(v) => Value::I32(v as i8 as i32),
                None => Value::Unknown,
            },
            "toUnsignedInt" => match get_i32(0) {
                Some(v) => Value::I32((v as u8) as i32),
                None => Value::Unknown,
            },
            "toUnsignedLong" => match get_i32(0) {
                Some(v) => Value::I64((v as u8) as i64),
                None => Value::Unknown,
            },
            _ => Value::Unknown,
        },
        "java/lang/Boolean" => match name {
            "logicalAnd" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32(((a != 0) && (b != 0)) as i32),
                _ => Value::Unknown,
            },
            "logicalOr" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32(((a != 0) || (b != 0)) as i32),
                _ => Value::Unknown,
            },
            "logicalXor" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32(((a != 0) ^ (b != 0)) as i32),
                _ => Value::Unknown,
            },
            "compare" => match (get_i32(0), get_i32(1)) {
                (Some(a), Some(b)) => Value::I32((a != 0).cmp(&(b != 0)) as i32),
                _ => Value::Unknown,
            },
            "hashCode" => match get_i32(0) {
                Some(v) => Value::I32(if v != 0 { 1231 } else { 1237 }),
                None => Value::Unknown,
            },
            _ => Value::Unknown,
        },
        "java/lang/Double" | "java/lang/Float" => match name {
            "compare" | "hashCode" | "isNaN" | "isInfinite" | "isFinite" => Value::Unknown,
            _ => Value::Unknown,
        },
        _ => Value::Unknown,
    }
}
