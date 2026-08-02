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

    // -- Conversion --

    fn sign_extend(&mut self, t: Term, extra_bits: u32) -> Term;
    fn extract(&mut self, t: Term, hi: u32, lo: u32) -> Term;

    // -- Boolean / control --

    fn ite(&mut self, cond: Term, then_: Term, else_: Term) -> Term;
    fn not(&mut self, t: Term) -> Term;
    fn and(&mut self, a: Term, b: Term) -> Term;
    fn or(&mut self, a: Term, b: Term) -> Term;

    // -- Solver state --

    fn assert(&mut self, t: Term);
    fn push(&mut self);
    fn pop(&mut self);
    fn check_sat(&mut self) -> SatResult;
    fn get_value_i64(&mut self, t: Term) -> Option<i64>;
}

pub trait SolverFactory: Send {
    fn create(&self) -> Result<Box<dyn Solver>, String>;
}
