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
