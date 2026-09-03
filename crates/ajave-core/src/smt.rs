//! Minimal solver abstraction for SMT-backed engines.
//!
//! The trait is object-safe (`Box<dyn Solver>`) by using opaque `Term(u64)`
//! handles rather than associated types. Future milestones extend this with
//! interpolation (M5) and CHC (M6).

/// Opaque handle into a solver's internal term store.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Term(pub u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Sort {
    Bv(u32),
    Bool,
    Str,
    Int,
    /// `(Array (_ BitVec idx_width) (_ BitVec elem_width))`
    Array { idx: u32, elem: u32 },
    /// `(Array (_ BitVec 32) String)`
    StrArray,
    /// IEEE-754 binary float: `Float32` (width 32) or `Float64` (width 64).
    ///
    /// Distinct from `Bv(32)`/`Bv(64)` on purpose. Encoding a double as a
    /// bitvector and applying `bvadd`/`bvmul` to its bit pattern computes
    /// something that is not floating-point addition at all, so any witness
    /// derived from it fails to reproduce the bug on a real JVM.
    Fp(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

pub trait Solver {
    fn name(&self) -> &'static str;

    // -- Term construction --

    fn fresh_bv(&mut self, name: &str, width: u32) -> Term;
    fn bv_const(&mut self, value: i64, width: u32) -> Term;
    fn bool_const(&mut self, value: bool) -> Term;

    // -- BV arithmetic --

    fn bvadd(&mut self, a: Term, b: Term) -> Term;
    fn bvsub(&mut self, a: Term, b: Term) -> Term;
    fn bvmul(&mut self, a: Term, b: Term) -> Term;
    fn bvsdiv(&mut self, a: Term, b: Term) -> Term;
    fn bvsrem(&mut self, a: Term, b: Term) -> Term;
    fn bvudiv(&mut self, a: Term, b: Term) -> Term;
    fn bvurem(&mut self, a: Term, b: Term) -> Term;
    fn bvneg(&mut self, a: Term) -> Term;

    // -- BV bitwise --

    fn bvand(&mut self, a: Term, b: Term) -> Term;
    fn bvor(&mut self, a: Term, b: Term) -> Term;
    fn bvxor(&mut self, a: Term, b: Term) -> Term;
    fn bvshl(&mut self, a: Term, b: Term) -> Term;
    fn bvashr(&mut self, a: Term, b: Term) -> Term;
    fn bvlshr(&mut self, a: Term, b: Term) -> Term;

    // -- BV comparison (return Bool) --

    fn bveq(&mut self, a: Term, b: Term) -> Term;
    fn bvslt(&mut self, a: Term, b: Term) -> Term;
    fn bvsle(&mut self, a: Term, b: Term) -> Term;
    fn bvsgt(&mut self, a: Term, b: Term) -> Term;
    fn bvsge(&mut self, a: Term, b: Term) -> Term;
    fn bvult(&mut self, a: Term, b: Term) -> Term;

    // -- Conversion --

    fn sign_extend(&mut self, t: Term, extra_bits: u32) -> Term;
    fn zero_extend(&mut self, t: Term, extra_bits: u32) -> Term;
    fn extract(&mut self, t: Term, hi: u32, lo: u32) -> Term;
    fn concat(&mut self, hi: Term, lo: Term) -> Term;

    // -- Boolean / control --

    // ── IEEE-754 floating point ─────────────────────────────────────────
    // Modelled with the SMT-LIB FloatingPoint theory so that NaN, the signed
    // zeroes, the infinities and rounding all behave as the JVM specifies.
    // Java arithmetic uses round-nearest-even, which is what these emit.
    fn fresh_fp(&mut self, name: &str, width: u32) -> Term;
    fn fp_const(&mut self, value: f64, width: u32) -> Term;
    fn fp_add(&mut self, a: Term, b: Term) -> Term;
    fn fp_sub(&mut self, a: Term, b: Term) -> Term;
    fn fp_mul(&mut self, a: Term, b: Term) -> Term;
    fn fp_div(&mut self, a: Term, b: Term) -> Term;
    fn fp_rem(&mut self, a: Term, b: Term) -> Term;
    fn fp_neg(&mut self, a: Term) -> Term;
    fn fp_abs(&mut self, a: Term) -> Term;
    /// `fp.eq`: IEEE equality, so NaN != NaN and -0.0 == 0.0.
    fn fp_eq(&mut self, a: Term, b: Term) -> Term;
    fn fp_lt(&mut self, a: Term, b: Term) -> Term;
    fn fp_le(&mut self, a: Term, b: Term) -> Term;
    fn fp_gt(&mut self, a: Term, b: Term) -> Term;
    fn fp_ge(&mut self, a: Term, b: Term) -> Term;
    fn fp_is_nan(&mut self, a: Term) -> Term;
    fn fp_is_infinite(&mut self, a: Term) -> Term;
    /// Reinterpret a bit pattern as a float — `Double.longBitsToDouble`.
    fn fp_from_bits(&mut self, bits: Term, width: u32) -> Term;
    /// Reinterpret a float as its bit pattern — `Double.doubleToRawLongBits`.
    fn fp_to_bits(&mut self, f: Term, width: u32) -> Term;
    /// Widen/narrow between Float32 and Float64 (`f2d`, `d2f`).
    fn fp_convert(&mut self, f: Term, to_width: u32) -> Term;
    /// Signed integer to float (`i2d`, `l2f`, ...).
    fn sbv_to_fp(&mut self, bv: Term, width: u32) -> Term;
    /// Float to signed integer, truncating toward zero (`d2i`, `f2l`).
    fn fp_to_sbv(&mut self, f: Term, width: u32) -> Term;
    /// Signed bitvector -> float, round-to-nearest-even.
    ///
    /// This is the JVM's `l2f`/`i2d`/`l2d` widening conversion (JLS 5.1.2):
    /// the value is converted to the nearest representable float, ties to even.
    /// `to_width` is the float width, 32 or 64.
    fn fp_from_sbv(&mut self, bv: Term, to_width: u32) -> Term;

    fn ite(&mut self, cond: Term, then_: Term, else_: Term) -> Term;
    fn not(&mut self, t: Term) -> Term;
    fn and(&mut self, a: Term, b: Term) -> Term;
    fn or(&mut self, a: Term, b: Term) -> Term;

    // -- Int/BV conversion --

    fn int_const(&mut self, value: i64) -> Term;
    fn int_to_bv32(&mut self, t: Term) -> Term;
    fn bv32_to_int(&mut self, t: Term) -> Term;

    // -- String theory --

    fn fresh_str(&mut self, name: &str) -> Term;
    fn str_const(&mut self, value: &str) -> Term;
    fn str_len(&mut self, s: Term) -> Term;
    fn str_contains(&mut self, haystack: Term, needle: Term) -> Term;
    fn str_prefixof(&mut self, pre: Term, s: Term) -> Term;
    fn str_suffixof(&mut self, suf: Term, s: Term) -> Term;
    fn str_concat(&mut self, a: Term, b: Term) -> Term;
    fn str_substr(&mut self, s: Term, offset: Term, len: Term) -> Term;
    fn str_indexof(&mut self, s: Term, t: Term, start: Term) -> Term;
    fn str_at(&mut self, s: Term, i: Term) -> Term;
    fn str_to_int(&mut self, s: Term) -> Term;
    fn str_from_int(&mut self, i: Term) -> Term;
    fn str_eq(&mut self, a: Term, b: Term) -> Term;
    /// `(str.to_code s)` — code point of single-char string, -1 if len!=1.
    fn str_to_code(&mut self, s: Term) -> Term;
    /// `(str.from_code i)` — single-char string from code point.
    fn str_from_code(&mut self, i: Term) -> Term;
    /// Constrain `s` to contain only characters in `[lo, hi]` (inclusive,
    /// as code points).
    ///
    /// Exists so a solver-chosen string can be held to a character range where
    /// SMT-LIB and Java agree. SMT-LIB strings are sequences of **code
    /// points**; Java strings are sequences of **UTF-16 code units**. A
    /// supplementary character is one SMT character and two Java `char`s, so
    /// every index-returning operation disagrees on any string containing one
    /// — `str.indexof` gives a code-point index where `String.indexOf` gives a
    /// UTF-16 index.
    fn str_chars_within(&mut self, s: Term, lo: u32, hi: u32) -> Term;
    /// `(str.replace_all s t1 t2)` — replace all occurrences of t1 with t2.
    fn str_replace_all(&mut self, s: Term, from: Term, to: Term) -> Term;
    /// `(str.< a b)` — lexicographic less-than.
    fn str_lt(&mut self, a: Term, b: Term) -> Term;

    // -- Array theory --

    /// Create a fresh unconstrained array: `(Array (_ BitVec 32) (_ BitVec elem_width))`.
    fn fresh_array(&mut self, name: &str, elem_width: u32) -> Term;
    /// Create a constant array where every element is `val`.
    fn const_array(&mut self, val: Term, elem_width: u32) -> Term;
    /// `(select arr idx)` — read element at index.
    fn array_select(&mut self, arr: Term, idx: Term) -> Term;
    /// `(store arr idx val)` — write element at index, returning new array.
    fn array_store(&mut self, arr: Term, idx: Term, val: Term) -> Term;

    // -- String-array theory --

    /// Create a fresh unconstrained array: `(Array (_ BitVec 32) String)`.
    fn fresh_str_array(&mut self, name: &str) -> Term;
    /// Create a constant string array where every element is `val`.
    fn const_str_array(&mut self, val: Term) -> Term;

    // -- Solver state --

    fn assert(&mut self, t: Term);
    fn push(&mut self);
    fn pop(&mut self);
    fn check_sat(&mut self) -> SatResult;
    fn get_value_i64(&mut self, t: Term) -> Option<i64>;
    fn get_value_string(&mut self, t: Term) -> Option<String>;
}

pub trait SolverFactory: Send {
    fn create(&self) -> Result<Box<dyn Solver>, String>;
}
