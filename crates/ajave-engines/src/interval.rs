//! The interval domain: `[lo, hi]` per integer-typed variable.
//!
//! This is Tier 1 from ARCHITECTURE.md, made real. It implements `Cpa`
//! (`core::cpa`) rather than being a bespoke analysis, so it rides the shared
//! fixpoint loop and composes with anything else that implements the trait.
//!
//! Two design choices worth being explicit about, because both trade
//! precision for a smaller amount of code, and both stay sound while doing
//! it:
//!
//! * **No widening.** We rely on the default `merge_sep`/`stop_sep` from
//!   `Cpa` -- states are kept separate rather than joined, and a state is
//!   dropped only when another already-reached state subsumes it exactly.
//!   That is enough to terminate on the loop-free, diamond-shaped code the
//!   `assume`/`assert` idiom produces (see the module doc on why path
//!   sensitivity, not joining, is what makes `x > 5 => x > 3` provable here).
//!   It will not terminate on an unbounded loop; `reachability`'s state cap
//!   catches that, and the `complete` flag it returns is what stops an
//!   incomplete search from being reported as a proof.
//! * **Overflow widens to Top, never narrows silently.** Java `int` wraps on
//!   overflow. Rather than model wraparound precisely, any arithmetic whose
//!   result could leave the `i32` range collapses to the fully unconstrained
//!   interval. A wrong *narrow* bound would be unsound (claiming a value is
//!   impossible when it isn't); a wrong *wide* bound only costs precision.
//!
//! ## Why path-sensitivity alone proves `assume(x > 5) => assert(x > 3)`
//!
//! javac never reifies a comparison as a boolean register -- it always lowers
//! `x > 5` to a branch that pushes a literal `0` or `1`. So `Verifier.assume`
//! sees a fresh variable holding an already-erased boolean, and narrowing
//! *has* to happen at the branch that produced it, not at the `assume` call.
//! Concretely: `if x <= 5 goto L1 else L2`, with `L1` setting the assume
//! argument to `0` and `L2` to `1`. The interval domain narrows `x` on both
//! edges of that branch (`(-inf, 5]` on `L1`, `[6, +inf)` on `L2`). With
//! states kept separate through the diamond, the `L1` branch's state is the
//! one where the eventual `Stmt::Assume` operand evaluates to the constant
//! `0` -- and *that* is what gets pruned, leaving only the already-narrowed
//! `x in [6, MAX]` state alive by the time the assertion is checked.

use std::collections::{BTreeMap, HashSet};
use std::ops::{Add, Mul, Neg, Sub};

use ajave_core::artifact::ProgramPoint;
use ajave_core::cpa::{Cpa, HasLocation, Lattice, MergeResult};
use ajave_ir::{BinOp, BlockId, CmpKind, Const, Edge, FieldKey, Operand, Program, Rvalue, Stmt, Ty, VarId};

use crate::body_analysis::{find_defining_bin, negate_binop};

pub const NEG_INF: i64 = i32::MIN as i64;
pub const POS_INF: i64 = i32::MAX as i64;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Interval {
    pub lo: i64,
    pub hi: i64,
}

impl Interval {
    pub fn point(v: i64) -> Self {
        Interval { lo: v, hi: v }
    }
    pub fn top() -> Self {
        Interval {
            lo: NEG_INF,
            hi: POS_INF,
        }
    }
    pub fn bottom() -> Self {
        Interval { lo: 1, hi: 0 }
    }
    pub fn is_bottom(&self) -> bool {
        self.lo > self.hi
    }
    /// Clamp to `i32` range, widening to Top if the true result could have
    /// left it -- the overflow rule from the module doc.
    fn clamp(lo: i128, hi: i128) -> Interval {
        if lo < NEG_INF as i128 || hi > POS_INF as i128 {
            Interval::top()
        } else {
            Interval {
                lo: lo as i64,
                hi: hi as i64,
            }
        }
    }
    /// Does this interval definitely, possibly, or never contain `v`?
    pub fn contains(&self, v: i64) -> bool {
        !self.is_bottom() && self.lo <= v && v <= self.hi
    }
    /// `true` only if every value in the interval satisfies `!= 0`.
    pub fn definitely_nonzero(&self) -> bool {
        !self.is_bottom() && (self.lo > 0 || self.hi < 0)
    }
    pub fn definitely_zero(&self) -> bool {
        *self == Interval::point(0)
    }
    pub fn join(self, o: Interval) -> Interval {
        if self.is_bottom() {
            return o;
        }
        if o.is_bottom() {
            return self;
        }
        Interval {
            lo: self.lo.min(o.lo),
            hi: self.hi.max(o.hi),
        }
    }
    fn leq(self, o: Interval) -> bool {
        self.is_bottom() || (!o.is_bottom() && o.lo <= self.lo && self.hi <= o.hi)
    }
    /// Greatest lower bound: the tightest interval contained in both. Yields
    /// a bottom interval (`lo > hi`) when the two do not overlap.
    pub fn meet(self, o: Interval) -> Interval {
        if self.is_bottom() || o.is_bottom() {
            return Interval { lo: 1, hi: 0 };
        }
        Interval {
            lo: self.lo.max(o.lo),
            hi: self.hi.min(o.hi),
        }
    }

    /// Narrow both operands of `a OP b` given the comparison holds. Returns
    /// `None` for operator/type combinations we don't bother narrowing --
    /// safe to skip, it only costs precision.
    fn narrow(op: BinOp, a: Interval, b: Interval) -> Option<(Interval, Interval)> {
        use BinOp::*;
        if a.is_bottom() || b.is_bottom() {
            return Some((Interval::bottom(), Interval::bottom()));
        }
        let na = match op {
            Lt => Interval {
                lo: a.lo,
                hi: a.hi.min(b.hi.saturating_sub(1)),
            },
            Le => Interval {
                lo: a.lo,
                hi: a.hi.min(b.hi),
            },
            Gt => Interval {
                lo: a.lo.max(b.lo.saturating_add(1)),
                hi: a.hi,
            },
            Ge => Interval {
                lo: a.lo.max(b.lo),
                hi: a.hi,
            },
            Eq => Interval {
                lo: a.lo.max(b.lo),
                hi: a.hi.min(b.hi),
            },
            _ => a,
        };
        let nb = match op {
            Lt => Interval {
                lo: b.lo.max(a.lo.saturating_add(1)),
                hi: b.hi,
            },
            Le => Interval {
                lo: b.lo.max(a.lo),
                hi: b.hi,
            },
            Gt => Interval {
                lo: b.lo,
                hi: b.hi.min(a.hi.saturating_sub(1)),
            },
            Ge => Interval {
                lo: b.lo,
                hi: b.hi.min(a.hi),
            },
            Eq => Interval {
                lo: b.lo.max(a.lo),
                hi: b.hi.min(a.hi),
            },
            _ => b,
        };
        Some((na, nb))
    }
}

impl Add for Interval {
    type Output = Interval;
    fn add(self, o: Interval) -> Interval {
        if self.is_bottom() || o.is_bottom() {
            return Interval::bottom();
        }
        Interval::clamp(
            self.lo as i128 + o.lo as i128,
            self.hi as i128 + o.hi as i128,
        )
    }
}

impl Sub for Interval {
    type Output = Interval;
    fn sub(self, o: Interval) -> Interval {
        if self.is_bottom() || o.is_bottom() {
            return Interval::bottom();
        }
        Interval::clamp(
            self.lo as i128 - o.hi as i128,
            self.hi as i128 - o.lo as i128,
        )
    }
}

impl Mul for Interval {
    type Output = Interval;
    fn mul(self, o: Interval) -> Interval {
        if self.is_bottom() || o.is_bottom() {
            return Interval::bottom();
        }
        let cands = [
            self.lo as i128 * o.lo as i128,
            self.lo as i128 * o.hi as i128,
            self.hi as i128 * o.lo as i128,
            self.hi as i128 * o.hi as i128,
        ];
        Interval::clamp(*cands.iter().min().unwrap(), *cands.iter().max().unwrap())
    }
}

impl Neg for Interval {
    type Output = Interval;
    fn neg(self) -> Interval {
        if self.is_bottom() {
            return self;
        }
        Interval::clamp(-(self.hi as i128), -(self.lo as i128))
    }
}

// ── Float interval domain ──────────────────────────────────────────────────

/// Interval domain over IEEE 754 doubles. Uses `f64::NEG_INFINITY` /
/// `f64::INFINITY` for top bounds. Bottom is represented by `lo > hi` (NaN
/// bounds). All arithmetic over-approximates: rounding goes outward.
#[derive(Clone, Copy, Debug)]
pub struct FloatInterval {
    pub lo: f64,
    pub hi: f64,
}

impl PartialEq for FloatInterval {
    fn eq(&self, other: &Self) -> bool {
        (self.is_bottom() && other.is_bottom())
            || (self.lo == other.lo && self.hi == other.hi)
    }
}
impl Eq for FloatInterval {}

impl FloatInterval {
    pub fn point(v: f64) -> Self {
        FloatInterval { lo: v, hi: v }
    }
    pub fn top() -> Self {
        FloatInterval {
            lo: f64::NEG_INFINITY,
            hi: f64::INFINITY,
        }
    }
    pub fn bottom() -> Self {
        FloatInterval { lo: 1.0, hi: 0.0 }
    }
    pub fn is_bottom(&self) -> bool {
        self.lo > self.hi
    }
    pub fn is_top(&self) -> bool {
        self.lo == f64::NEG_INFINITY && self.hi == f64::INFINITY
    }
    pub fn contains(&self, v: f64) -> bool {
        !self.is_bottom() && self.lo <= v && v <= self.hi
    }
    pub fn definitely_positive(&self) -> bool {
        !self.is_bottom() && self.lo > 0.0
    }
    pub fn definitely_nonnegative(&self) -> bool {
        !self.is_bottom() && self.lo >= 0.0
    }
    pub fn join(self, o: FloatInterval) -> FloatInterval {
        if self.is_bottom() {
            return o;
        }
        if o.is_bottom() {
            return self;
        }
        FloatInterval {
            lo: self.lo.min(o.lo),
            hi: self.hi.max(o.hi),
        }
    }
    pub fn leq(self, o: FloatInterval) -> bool {
        self.is_bottom() || (!o.is_bottom() && o.lo <= self.lo && self.hi <= o.hi)
    }
    /// Threshold widening: if a bound grows, jump to the next threshold instead
    /// of ±∞. Falls back to ±∞ if no threshold is beyond the new bound.
    pub fn widen_thresholded(old: FloatInterval, new: FloatInterval, thresholds: &[f64]) -> FloatInterval {
        if new.is_bottom() {
            return old;
        }
        if old.is_bottom() {
            return new;
        }
        let lo = if new.lo < old.lo {
            // Find the largest threshold ≤ new.lo.
            thresholds
                .iter()
                .rev()
                .copied()
                .find(|&t| t <= new.lo)
                .unwrap_or(f64::NEG_INFINITY)
        } else {
            old.lo
        };
        let hi = if new.hi > old.hi {
            // Find the smallest threshold ≥ new.hi.
            thresholds
                .iter()
                .copied()
                .find(|&t| t >= new.hi)
                .unwrap_or(f64::INFINITY)
        } else {
            old.hi
        };
        FloatInterval { lo, hi }
    }
    /// Standard widening: if the new bound exceeds the old, push to ±∞.
    pub fn widen(old: FloatInterval, new: FloatInterval) -> FloatInterval {
        if new.is_bottom() {
            return old;
        }
        if old.is_bottom() {
            return new;
        }
        FloatInterval {
            lo: if new.lo < old.lo {
                f64::NEG_INFINITY
            } else {
                old.lo
            },
            hi: if new.hi > old.hi {
                f64::INFINITY
            } else {
                old.hi
            },
        }
    }
    /// Narrow both operands of `a OP b` given the comparison holds.
    fn narrow(op: BinOp, a: FloatInterval, b: FloatInterval) -> Option<(FloatInterval, FloatInterval)> {
        if a.is_bottom() || b.is_bottom() {
            return Some((FloatInterval::bottom(), FloatInterval::bottom()));
        }
        let na = match op {
            BinOp::Lt => FloatInterval { lo: a.lo, hi: a.hi.min(b.hi) },
            BinOp::Le => FloatInterval { lo: a.lo, hi: a.hi.min(b.hi) },
            BinOp::Gt => FloatInterval { lo: a.lo.max(b.lo), hi: a.hi },
            BinOp::Ge => FloatInterval { lo: a.lo.max(b.lo), hi: a.hi },
            BinOp::Eq => FloatInterval { lo: a.lo.max(b.lo), hi: a.hi.min(b.hi) },
            _ => a,
        };
        let nb = match op {
            BinOp::Lt => FloatInterval { lo: b.lo.max(a.lo), hi: b.hi },
            BinOp::Le => FloatInterval { lo: b.lo.max(a.lo), hi: b.hi },
            BinOp::Gt => FloatInterval { lo: b.lo, hi: b.hi.min(a.hi) },
            BinOp::Ge => FloatInterval { lo: b.lo, hi: b.hi.min(a.hi) },
            BinOp::Eq => FloatInterval { lo: b.lo.max(a.lo), hi: b.hi.min(a.hi) },
            _ => b,
        };
        Some((na, nb))
    }
}

impl Add for FloatInterval {
    type Output = FloatInterval;
    fn add(self, o: FloatInterval) -> FloatInterval {
        if self.is_bottom() || o.is_bottom() {
            return FloatInterval::bottom();
        }
        FloatInterval {
            lo: self.lo + o.lo,
            hi: self.hi + o.hi,
        }
    }
}

impl Sub for FloatInterval {
    type Output = FloatInterval;
    fn sub(self, o: FloatInterval) -> FloatInterval {
        if self.is_bottom() || o.is_bottom() {
            return FloatInterval::bottom();
        }
        FloatInterval {
            lo: self.lo - o.hi,
            hi: self.hi - o.lo,
        }
    }
}

impl Mul for FloatInterval {
    type Output = FloatInterval;
    fn mul(self, o: FloatInterval) -> FloatInterval {
        if self.is_bottom() || o.is_bottom() {
            return FloatInterval::bottom();
        }
        let corners = [
            self.lo * o.lo,
            self.lo * o.hi,
            self.hi * o.lo,
            self.hi * o.hi,
        ];
        let lo = corners.iter().copied().fold(f64::INFINITY, f64::min);
        let hi = corners.iter().copied().fold(f64::NEG_INFINITY, f64::max);
        if lo.is_nan() || hi.is_nan() {
            return FloatInterval::top();
        }
        FloatInterval { lo, hi }
    }
}

impl Neg for FloatInterval {
    type Output = FloatInterval;
    fn neg(self) -> FloatInterval {
        if self.is_bottom() {
            return self;
        }
        FloatInterval {
            lo: -self.hi,
            hi: -self.lo,
        }
    }
}

impl FloatInterval {
    pub fn div(self, o: FloatInterval) -> FloatInterval {
        if self.is_bottom() || o.is_bottom() {
            return FloatInterval::bottom();
        }
        // If divisor contains zero, result is unbounded.
        if o.lo <= 0.0 && o.hi >= 0.0 {
            return FloatInterval::top();
        }
        let corners = [
            self.lo / o.lo,
            self.lo / o.hi,
            self.hi / o.lo,
            self.hi / o.hi,
        ];
        let lo = corners.iter().copied().fold(f64::INFINITY, f64::min);
        let hi = corners.iter().copied().fold(f64::NEG_INFINITY, f64::max);
        if lo.is_nan() || hi.is_nan() {
            return FloatInterval::top();
        }
        FloatInterval { lo, hi }
    }

    pub fn rem(self, o: FloatInterval) -> FloatInterval {
        if self.is_bottom() || o.is_bottom() {
            return FloatInterval::bottom();
        }
        // Conservative: |a % b| < |b|
        let max_abs = o.lo.abs().max(o.hi.abs());
        FloatInterval {
            lo: -max_abs,
            hi: max_abs,
        }
    }
}

fn eval_float_comparison(op: BinOp, a: FloatInterval, b: FloatInterval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::bottom();
    }
    let (definitely_true, definitely_false) = match op {
        BinOp::Eq => (
            a.lo == a.hi && b.lo == b.hi && a.lo == b.lo,
            a.hi < b.lo || b.hi < a.lo,
        ),
        BinOp::Ne => (a.hi < b.lo || b.hi < a.lo, a.lo == a.hi && b.lo == b.hi && a.lo == b.lo),
        BinOp::Lt => (a.hi < b.lo, a.lo >= b.hi),
        BinOp::Le => (a.hi <= b.lo, a.lo > b.hi),
        BinOp::Gt => (a.lo > b.hi, a.hi <= b.lo),
        BinOp::Ge => (a.lo >= b.hi, a.hi < b.lo),
        _ => (false, false),
    };
    if definitely_true {
        Interval::point(1)
    } else if definitely_false {
        Interval::point(0)
    } else {
        Interval { lo: 0, hi: 1 }
    }
}

/// Evaluate `cmp(kind, a, b)` where a, b are float intervals.
/// Returns an integer interval in {-1, 0, 1}.
fn eval_float_cmp(a: FloatInterval, b: FloatInterval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::bottom();
    }
    // Determine the possible outcomes of the three-way comparison.
    let can_lt = a.lo < b.hi; // a might be < b
    let can_gt = a.hi > b.lo; // a might be > b
    let can_eq = a.lo <= b.hi && b.lo <= a.hi; // intervals overlap
    let mut lo = 1i64;
    let mut hi = -1i64;
    if can_lt {
        lo = lo.min(-1);
        hi = hi.max(-1);
    }
    if can_eq {
        lo = lo.min(0);
        hi = hi.max(0);
    }
    if can_gt {
        lo = lo.min(1);
        hi = hi.max(1);
    }
    if lo > hi {
        // Shouldn't happen, but fall back to full range.
        Interval { lo: -1, hi: 1 }
    } else {
        Interval { lo, hi }
    }
}

/// Nullness lattice for reference variables.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Nullness {
    /// Definitely non-null (e.g. result of `new`, string constant).
    NonNull,
    /// Definitely null (assigned from `Const::Null`).
    Null,
    /// Unknown — could be either.
    Unknown,
}

impl Nullness {
    fn join(self, other: Self) -> Self {
        if self == other { self } else { Nullness::Unknown }
    }
    fn leq(self, other: Self) -> bool {
        self == other || other == Nullness::Unknown
    }
}

/// `VarId -> Interval`. A variable missing from the map is implicitly Top:
/// this keeps the map small (only entries we've learned something about)
/// rather than pre-populating every variable in the body.
#[derive(Clone, Debug)]
pub struct IState {
    pub at: ProgramPoint,
    pub vars: BTreeMap<VarId, Interval>,
    /// Float/Double interval tracking. Missing = Top (unconstrained).
    pub float_vars: BTreeMap<VarId, FloatInterval>,
    /// Nullness tracking for reference variables. Missing = Unknown.
    pub nullness: BTreeMap<VarId, Nullness>,
    /// Length of the array a reference variable points at. Missing = Top.
    ///
    /// Seeded at `NewArray` from the allocation length and propagated through
    /// copies. A JVM array's length is immutable after allocation, so once a
    /// variable is known to hold an array of length `n`, every `arraylength`
    /// on it yields `n` — which is what discharges the constant-index
    /// `ArrayBounds` checks javac emits for array initialisers.
    pub array_lens: BTreeMap<VarId, Interval>,
    /// Value of a field, abstracted **flatly**: one cell per `(class, name)`,
    /// with the receiving instance ignored. Missing = Top.
    ///
    /// Merging every instance of a field into one cell is an over-approximation,
    /// which is what an Over-direction engine needs, and it is exact whenever a
    /// class has a single live instance — the common shape in this benchmark
    /// set. Writes are therefore only allowed to be *strong* (replacing the
    /// cell) when the receiver is provably unique; otherwise they are *weak*
    /// (joined into it). See `FieldPrec` for how that is decided.
    pub fields: BTreeMap<FieldKey, Interval>,
    /// Nullness of the same flat field cells. Missing = Unknown.
    pub field_null: BTreeMap<FieldKey, Nullness>,
}

impl IState {
    pub fn get(&self, v: VarId) -> Interval {
        self.vars.get(&v).copied().unwrap_or_else(Interval::top)
    }
    fn set(&mut self, v: VarId, i: Interval) {
        // Don't store Top explicitly; an absent entry already means Top, and
        // this keeps `leq`/`join` cheap by keeping maps small.
        if i == Interval::top() {
            self.vars.remove(&v);
        } else {
            self.vars.insert(v, i);
        }
    }
    pub fn get_array_len(&self, v: VarId) -> Interval {
        self.array_lens.get(&v).copied().unwrap_or_else(Interval::top)
    }
    pub fn get_field(&self, f: &FieldKey) -> Interval {
        self.fields.get(f).copied().unwrap_or_else(Interval::top)
    }
    fn set_field(&mut self, f: &FieldKey, i: Interval, strong: bool) {
        // A weak update cannot claim the cell now holds only the new value —
        // some other instance may still hold the old one — so it joins instead.
        let v = if strong { i } else { self.get_field(f).join(i) };
        if v == Interval::top() {
            self.fields.remove(f);
        } else {
            self.fields.insert(f.clone(), v);
        }
    }
    pub fn get_field_null(&self, f: &FieldKey) -> Nullness {
        self.field_null.get(f).copied().unwrap_or(Nullness::Unknown)
    }
    fn set_field_null(&mut self, f: &FieldKey, n: Nullness, strong: bool) {
        let v = if strong { n } else { self.get_field_null(f).join(n) };
        if v == Nullness::Unknown {
            self.field_null.remove(f);
        } else {
            self.field_null.insert(f.clone(), v);
        }
    }
    /// Drop everything we know about the given field cells. Used when a call
    /// may have written them: our analysis is intra-procedural, so anything a
    /// callee touches has to fall back to Top.
    fn invalidate_fields(&mut self, fs: &std::collections::HashSet<FieldKey>) {
        for f in fs {
            self.fields.remove(f);
            self.field_null.remove(f);
        }
    }
    fn set_array_len(&mut self, v: VarId, i: Interval) {
        if i == Interval::top() {
            self.array_lens.remove(&v);
        } else {
            self.array_lens.insert(v, i);
        }
    }
    pub fn get_float(&self, v: VarId) -> FloatInterval {
        self.float_vars
            .get(&v)
            .copied()
            .unwrap_or_else(FloatInterval::top)
    }
    fn set_float(&mut self, v: VarId, i: FloatInterval) {
        if i.is_top() {
            self.float_vars.remove(&v);
        } else {
            self.float_vars.insert(v, i);
        }
    }
    pub fn get_nullness(&self, v: VarId) -> Nullness {
        self.nullness.get(&v).copied().unwrap_or(Nullness::Unknown)
    }
    fn set_nullness(&mut self, v: VarId, n: Nullness) {
        if n == Nullness::Unknown {
            self.nullness.remove(&v);
        } else {
            self.nullness.insert(v, n);
        }
    }
    /// Get nullness for an operand.
    fn operand_nullness(&self, op: &Operand) -> Nullness {
        match op {
            Operand::Var(v) => self.get_nullness(*v),
            Operand::Const(Const::Null) => Nullness::Null,
            Operand::Const(Const::Str(_) | Const::Class(_)) => Nullness::NonNull,
            _ => Nullness::Unknown,
        }
    }
    /// Evaluate an operand as a float interval.
    pub fn eval_operand_float(&self, op: &Operand) -> FloatInterval {
        match op {
            Operand::Var(v) => self.get_float(*v),
            Operand::Const(Const::Float(f)) => FloatInterval::point(*f as f64),
            Operand::Const(Const::Double(d)) => FloatInterval::point(*d),
            Operand::Const(Const::Int(n)) => FloatInterval::point(*n as f64),
            _ => FloatInterval::top(),
        }
    }
    /// Evaluate an operand under this state.
    pub fn eval_operand(&self, op: &Operand) -> Interval {
        match op {
            Operand::Var(v) => self.get(*v),
            Operand::Const(Const::Int(n)) => Interval::point(*n as i64),
            Operand::Const(Const::Long(n)) => {
                // Long arithmetic isn't modelled precisely by this i32-ranged
                // domain; treat as unconstrained rather than misrepresenting
                // it as an i32-sized point.
                let _ = n;
                Interval::top()
            }
            _ => Interval::top(),
        }
    }
    /// Evaluate an rvalue, with float-awareness when `var_types` is provided.
    /// The result is always an integer interval (float rvalues that produce
    /// float results update `float_vars` separately in the transfer function).
    pub fn eval_rvalue(&self, rv: &Rvalue) -> Interval {
        self.eval_rvalue_inner(rv, None)
    }
    /// Float-aware rvalue evaluation. When `var_types` is available, handles
    /// `Cmp(FloatL/FloatG, ..)` precisely.
    pub fn eval_rvalue_typed(&self, rv: &Rvalue, var_types: &[ajave_ir::VarInfo]) -> Interval {
        self.eval_rvalue_inner(rv, Some(var_types))
    }
    fn eval_rvalue_inner(&self, rv: &Rvalue, var_types: Option<&[ajave_ir::VarInfo]>) -> Interval {
        match rv {
            Rvalue::Use(o) => self.eval_operand(o),
            Rvalue::Neg(o) => self.eval_operand(o).neg(),
            // An array's length is fixed at allocation, so reading it back
            // yields whatever we recorded for that reference. A JVM array
            // length is also never negative, which is enough on its own to
            // discharge the `idx >= 0` half of a bounds check.
            Rvalue::ArrayLength(Operand::Var(a)) => {
                let known = self.get_array_len(*a);
                if known == Interval::top() {
                    Interval { lo: 0, hi: i32::MAX as i64 }
                } else {
                    known
                }
            }
            Rvalue::ArrayLength(_) => Interval { lo: 0, hi: i32::MAX as i64 },
            // Flat field cells. Absent reads as Top, so this is sound even
            // when field tracking is disabled or the cell was invalidated.
            Rvalue::GetField { field, .. } => self.get_field(field),
            Rvalue::GetStatic(fk) => self.get_field(fk),
            Rvalue::Cmp(kind, a, b) => {
                match kind {
                    CmpKind::FloatL | CmpKind::FloatG => {
                        let (fa, fb) = (self.eval_operand_float(a), self.eval_operand_float(b));
                        eval_float_cmp(fa, fb)
                    }
                    CmpKind::Long => Interval { lo: -1, hi: 1 },
                }
            }
            Rvalue::Bin(op, a, b) => {
                // Check if operands are float-typed.
                let is_float_op = var_types.is_some() && match a {
                    Operand::Var(v) => {
                        let vt = var_types.unwrap();
                        matches!(
                            vt.get(v.0 as usize).map(|vi| vi.ty),
                            Some(Ty::Float | Ty::Double)
                        )
                    }
                    Operand::Const(Const::Float(_) | Const::Double(_)) => true,
                    _ => false,
                };
                if is_float_op && matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) {
                    let (fa, fb) = (self.eval_operand_float(a), self.eval_operand_float(b));
                    return eval_float_comparison(*op, fa, fb);
                }

                // Nullness-aware comparison: if one side is Null and the other
                // has known nullness, we can resolve the comparison precisely.
                if matches!(op, BinOp::Ne | BinOp::Eq) {
                    let na = self.operand_nullness(a);
                    let nb = self.operand_nullness(b);
                    let null_cmp = match (na, nb) {
                        (Nullness::NonNull, Nullness::Null) | (Nullness::Null, Nullness::NonNull) => {
                            Some(matches!(op, BinOp::Ne))
                        }
                        (Nullness::Null, Nullness::Null) => {
                            Some(matches!(op, BinOp::Eq))
                        }
                        _ => None,
                    };
                    if let Some(result) = null_cmp {
                        return Interval::point(if result { 1 } else { 0 });
                    }
                }
                let (ia, ib) = (self.eval_operand(a), self.eval_operand(b));
                match op {
                    BinOp::Add => ia.add(ib),
                    BinOp::Sub => ia.sub(ib),
                    BinOp::Mul => ia.mul(ib),
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        eval_comparison(*op, ia, ib)
                    }
                    // javac compiles `a && b` over comparison results into a
                    // bitwise `&` of two 0/1 values, so a bounds check like
                    // `idx >= 0 & idx < len` is unprovable without this.
                    BinOp::And | BinOp::Or | BinOp::Xor => eval_bitwise(*op, ia, ib),
                    _ => Interval::top(),
                }
            }
            _ => Interval::top(),
        }
    }
    /// Evaluate a float-producing rvalue.
    pub fn eval_rvalue_float(&self, rv: &Rvalue) -> FloatInterval {
        match rv {
            Rvalue::Use(o) => self.eval_operand_float(o),
            Rvalue::Neg(o) => self.eval_operand_float(o).neg(),
            Rvalue::Bin(op, a, b) => {
                let (fa, fb) = (self.eval_operand_float(a), self.eval_operand_float(b));
                match op {
                    BinOp::Add => fa.add(fb),
                    BinOp::Sub => fa.sub(fb),
                    BinOp::Mul => fa.mul(fb),
                    BinOp::Div => fa.div(fb),
                    BinOp::Rem => fa.rem(fb),
                    _ => FloatInterval::top(),
                }
            }
            Rvalue::Nondet(Ty::Float | Ty::Double, _) | Rvalue::Havoc(Ty::Float | Ty::Double, _) => {
                FloatInterval::top()
            }
            // `java.lang.Math` bounds. Without these every call is `top`, and a
            // program whose assertion rests on `Math.sin` cannot be proved no
            // matter how precise the rest of the analysis is.
            //
            // `math_interval::eval` over-approximates and returns `top`
            // wherever the call could produce NaN, so this cannot introduce an
            // unsound narrowing.
            Rvalue::Call { target, args, .. } => {
                let ranges: Vec<crate::math_interval::Range> = args
                    .iter()
                    .map(|a| {
                        let fi = self.eval_operand_float(a);
                        crate::math_interval::Range::new(fi.lo, fi.hi)
                    })
                    .collect();
                match crate::math_interval::eval(target, &ranges) {
                    Some(r) if !r.is_top() => FloatInterval { lo: r.lo, hi: r.hi },
                    _ => FloatInterval::top(),
                }
            }
            // Int-to-float cast: use the integer interval bounds.
            Rvalue::Use(Operand::Var(v)) => {
                let iv = self.get(*v);
                if iv.is_bottom() {
                    FloatInterval::bottom()
                } else {
                    FloatInterval {
                        lo: iv.lo as f64,
                        hi: iv.hi as f64,
                    }
                }
            }
            _ => FloatInterval::top(),
        }
    }
}

/// Abstract `&`, `|` and `^` on intervals.
///
/// Exact when both operands are confined to `{0,1}` — which is the case that
/// matters, since javac lowers `&&`/`||` over comparison results to bitwise ops
/// on 0/1 values. Outside that range we fall back to bounds that hold for any
/// non-negative operands, and to Top when either side may be negative (the
/// two's-complement result is not interval-representable there).
fn eval_bitwise(op: BinOp, a: Interval, b: Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval { lo: 1, hi: 0 };
    }
    let boolean = |i: Interval| i.lo >= 0 && i.hi <= 1;
    if boolean(a) && boolean(b) {
        // Both in {0,1}: evaluate pointwise over the (at most four) pairs.
        let mut lo = i64::MAX;
        let mut hi = i64::MIN;
        for x in a.lo..=a.hi {
            for y in b.lo..=b.hi {
                let r = match op {
                    BinOp::And => x & y,
                    BinOp::Or => x | y,
                    _ => x ^ y,
                };
                lo = lo.min(r);
                hi = hi.max(r);
            }
        }
        return Interval { lo, hi };
    }
    if a.lo < 0 || b.lo < 0 {
        return Interval::top();
    }
    // Non-negative operands: `x & y <= min(x,y)`, and `x | y` / `x ^ y` are
    // bounded above by the next power of two covering both maxima.
    match op {
        BinOp::And => Interval { lo: 0, hi: a.hi.min(b.hi) },
        BinOp::Or | BinOp::Xor => {
            let m = a.hi.max(b.hi);
            // Smallest all-ones mask that covers `m`.
            let bound = if m <= 0 {
                0
            } else {
                let bits = 64 - (m as u64).leading_zeros();
                if bits >= 63 { i64::MAX } else { (1i64 << bits) - 1 }
            };
            Interval { lo: 0, hi: bound }
        }
        _ => Interval::top(),
    }
}

fn eval_comparison(op: BinOp, a: Interval, b: Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::bottom();
    }
    // Definitely true, definitely false, or genuinely unknown (both possible).
    let (definitely_true, definitely_false) = match op {
        BinOp::Eq => (a == b && a.lo == a.hi, a.hi < b.lo || b.hi < a.lo),
        BinOp::Ne => (a.hi < b.lo || b.hi < a.lo, a == b && a.lo == a.hi),
        BinOp::Lt => (a.hi < b.lo, a.lo >= b.hi),
        BinOp::Le => (a.hi <= b.lo, a.lo > b.hi),
        BinOp::Gt => (a.lo > b.hi, a.hi <= b.lo),
        BinOp::Ge => (a.lo >= b.hi, a.hi < b.lo),
        _ => (false, false),
    };
    if definitely_true {
        Interval::point(1)
    } else if definitely_false {
        Interval::point(0)
    } else {
        Interval { lo: 0, hi: 1 }
    }
}

/// Static fields guaranteed non-null by the JLS / JDK contract.
pub fn is_nonnull_static(fk: &FieldKey) -> bool {
    // NOTE: `System.out`/`err`/`in` are deliberately absent. They are not
    // `final` — `System.setOut(null)` is legal and makes the field null — so
    // they carry no non-null guarantee. Every entry below is `static final`
    // with a non-null initialiser, which is what makes it safe to assume.
    matches!(
        (fk.class.as_str(), fk.name.as_str()),
        ("java/lang/Boolean", "TRUE" | "FALSE" | "TYPE")
            | ("java/lang/Integer", "TYPE")
            | ("java/lang/Long", "TYPE")
            | ("java/lang/Double", "TYPE")
            | ("java/lang/Float", "TYPE")
            | ("java/lang/Byte", "TYPE")
            | ("java/lang/Short", "TYPE")
            | ("java/lang/Character", "TYPE")
            | ("java/util/Collections", "EMPTY_LIST" | "EMPTY_MAP" | "EMPTY_SET")
    )
}

impl IState {
    /// Compute the nullness of a reference-producing rvalue.
    pub fn eval_nullness(&self, rv: &Rvalue) -> Nullness {
        match rv {
            Rvalue::Use(Operand::Const(Const::Null)) => Nullness::Null,
            Rvalue::Use(Operand::Const(Const::Str(_) | Const::Class(_))) => Nullness::NonNull,
            Rvalue::Use(Operand::Var(v)) => self.get_nullness(*v),
            Rvalue::New(_) => Nullness::NonNull,
            Rvalue::NewArray { .. } => Nullness::NonNull,
            Rvalue::GetStatic(fk) if is_nonnull_static(fk) => Nullness::NonNull,
            // An erased call whose result the JDK documents as never null.
            // Exactly the same shape as `is_nonnull_static` one line above:
            // a specified guarantee, keyed on the full signature.
            //
            // This is why `Havoc` keeps the name of the call it replaced.
            // Without it the value is `Unknown` and every dereference of it
            // stays unproven, which is what left `Collections.singleton`
            // results -- and the whole securibench mock API built on them --
            // permanently open.
            Rvalue::Havoc(_, Some(m))
                if ajave_models::returns_nonnull(&m.class, &m.name, &m.desc) =>
            {
                Nullness::NonNull
            }
            // Flat field cells: an absent cell reads as Unknown, so this stays
            // sound when tracking is off or the cell has been invalidated.
            Rvalue::GetStatic(fk) => self.get_field_null(fk),
            Rvalue::GetField { field, .. } => self.get_field_null(field),
            // Call results, array loads, etc. are Unknown.
            _ => Nullness::Unknown,
        }
    }
}

impl Lattice for IState {
    fn leq(&self, other: &Self) -> bool {
        // Every variable known in `self` must be narrower-or-equal in
        // `other`; anything absent from `self` but present in `other` means
        // `self` (Top there) is not covered.
        for (v, iv) in &self.vars {
            if !iv.leq(other.vars.get(v).copied().unwrap_or_else(Interval::top)) {
                return false;
            }
        }
        for v in other.vars.keys() {
            if !self.vars.contains_key(v) {
                return false;
            }
        }
        // Float vars: same rule.
        for (v, fv) in &self.float_vars {
            if !fv.leq(other.float_vars.get(v).copied().unwrap_or_else(FloatInterval::top)) {
                return false;
            }
        }
        for v in other.float_vars.keys() {
            if !self.float_vars.contains_key(v) {
                return false;
            }
        }
        // Nullness: same rule — self must be narrower-or-equal.
        for (v, n) in &self.nullness {
            let other_n = other.nullness.get(v).copied().unwrap_or(Nullness::Unknown);
            if !n.leq(other_n) {
                return false;
            }
        }
        for v in other.nullness.keys() {
            if !self.nullness.contains_key(v) {
                return false;
            }
        }
        // Array lengths: same rule.
        for (v, iv) in &self.array_lens {
            if !iv.leq(other.get_array_len(*v)) {
                return false;
            }
        }
        for v in other.array_lens.keys() {
            if !self.array_lens.contains_key(v) {
                return false;
            }
        }
        // Field cells: same rule again.
        for (f, iv) in &self.fields {
            if !iv.leq(other.get_field(f)) {
                return false;
            }
        }
        for f in other.fields.keys() {
            if !self.fields.contains_key(f) {
                return false;
            }
        }
        for (f, n) in &self.field_null {
            if !n.leq(other.get_field_null(f)) {
                return false;
            }
        }
        for f in other.field_null.keys() {
            if !self.field_null.contains_key(f) {
                return false;
            }
        }
        true
    }
    fn join(&self, other: &Self) -> Self {
        let mut vars = BTreeMap::new();
        let keys: std::collections::BTreeSet<_> =
            self.vars.keys().chain(other.vars.keys()).copied().collect();
        for k in keys {
            let j = self.get(k).join(other.get(k));
            if j != Interval::top() {
                vars.insert(k, j);
            }
        }
        let mut float_vars = BTreeMap::new();
        let fkeys: std::collections::BTreeSet<_> =
            self.float_vars.keys().chain(other.float_vars.keys()).copied().collect();
        for k in fkeys {
            let j = self.get_float(k).join(other.get_float(k));
            if !j.is_top() {
                float_vars.insert(k, j);
            }
        }
        let mut nullness = BTreeMap::new();
        let nkeys: std::collections::BTreeSet<_> =
            self.nullness.keys().chain(other.nullness.keys()).copied().collect();
        for k in nkeys {
            let j = self.get_nullness(k).join(other.get_nullness(k));
            if j != Nullness::Unknown {
                nullness.insert(k, j);
            }
        }
        let mut array_lens = BTreeMap::new();
        let akeys: std::collections::BTreeSet<_> =
            self.array_lens.keys().chain(other.array_lens.keys()).copied().collect();
        for k in akeys {
            let j = self.get_array_len(k).join(other.get_array_len(k));
            if j != Interval::top() {
                array_lens.insert(k, j);
            }
        }
        let mut fields = BTreeMap::new();
        let fkeys2: std::collections::BTreeSet<_> =
            self.fields.keys().chain(other.fields.keys()).cloned().collect();
        for k in fkeys2 {
            let j = self.get_field(&k).join(other.get_field(&k));
            if j != Interval::top() {
                fields.insert(k, j);
            }
        }
        let mut field_null = BTreeMap::new();
        let nfkeys: std::collections::BTreeSet<_> =
            self.field_null.keys().chain(other.field_null.keys()).cloned().collect();
        for k in nfkeys {
            let j = self.get_field_null(&k).join(other.get_field_null(&k));
            if j != Nullness::Unknown {
                field_null.insert(k, j);
            }
        }
        IState {
            at: self.at.clone(),
            vars,
            float_vars,
            nullness,
            array_lens,
            fields,
            field_null,
        }
    }
    fn is_bottom(&self) -> bool {
        self.vars.values().any(|i| i.is_bottom())
            || self.float_vars.values().any(|f| f.is_bottom())
    }
}

impl HasLocation for IState {
    fn location(&self) -> &ProgramPoint {
        &self.at
    }
}

/// Count the number of local slots consumed by a method's parameters from its
/// JVM descriptor. For a static method `([Ljava/lang/String;)V` this returns 1.
/// For `(IJ)V` it returns 3 (int=1 slot, long=2 slots).
pub fn param_slot_count(desc: &str) -> usize {
    let inner = desc.trim_start_matches('(');
    let bytes = inner.as_bytes();
    let mut pos = 0;
    let mut slot = 0;
    while pos < bytes.len() && bytes[pos] != b')' {
        match bytes[pos] {
            b'J' | b'D' => { pos += 1; slot += 2; }
            b'L' => {
                while pos < bytes.len() && bytes[pos] != b';' { pos += 1; }
                pos += 1;
                slot += 1;
            }
            b'[' => {
                while pos < bytes.len() && bytes[pos] == b'[' { pos += 1; }
                if pos < bytes.len() && bytes[pos] == b'L' {
                    while pos < bytes.len() && bytes[pos] != b';' { pos += 1; }
                    pos += 1;
                } else if pos < bytes.len() {
                    pos += 1;
                }
                slot += 1;
            }
            _ => { pos += 1; slot += 1; }
        }
    }
    slot
}

/// Find the statement in `body`'s block that defines `v` as `Cmp(kind, a, b)`.
fn find_defining_cmp(body: &ajave_ir::Body, block: BlockId, v: VarId) -> Option<(CmpKind, &Operand, &Operand)> {
    for s in body.block(block).stmts.iter().rev() {
        if let Stmt::Assign(dv, Rvalue::Cmp(kind, a, b)) = s {
            if *dv == v {
                return Some((*kind, a, b));
            }
        }
    }
    None
}

/// Find the statement in `body`'s block that defines `v` as `Bin(op, a, b)`,
/// searching backward from the end of the block. This is how branch edges
/// Which field cells may be updated strongly, and what each call clobbers.
///
/// The flat field abstraction keeps one cell per `(class, name)`. Replacing a
/// cell outright (a *strong* update) is only sound when the write cannot have
/// been to a different instance that other reads still observe. Two cases
/// qualify:
///
/// * **Static fields.** There is exactly one cell in the JVM, so a write always
///   replaces it.
/// * **Instance fields of a class with a single allocation site**, where that
///   site is not inside a loop. Then at most one instance ever exists, and the
///   flat cell describes it exactly.
///
/// Everything else takes a weak update (join), which is sound but only ever
/// widens what we know.
#[derive(Default, Clone)]
pub struct FieldPrec {
    /// Classes proven to have at most one live instance.
    pub singleton_classes: std::collections::HashSet<String>,
    /// Per-method set of field cells that method, or anything it calls, writes.
    /// A call invalidates exactly these rather than the whole field map.
    pub writes: std::collections::HashMap<ajave_ir::MethodKey, std::collections::HashSet<FieldKey>>,
    /// Every field written anywhere — the fallback for an unresolved callee.
    pub all_written: std::collections::HashSet<FieldKey>,
    /// Empty set, returned for calls proven to write nothing.
    pub nothing: std::collections::HashSet<FieldKey>,
}

impl FieldPrec {
    fn may_update_strongly(&self, f: &FieldKey, is_static: bool) -> bool {
        is_static || self.singleton_classes.contains(&f.class)
    }

    /// Fields a call to `target` may write.
    ///
    /// A callee we have a write-summary for clobbers exactly that set. One we
    /// do not is assumed to write everything — unless its contract declares it
    /// pure, in which case it writes nothing and field knowledge survives the
    /// call.
    fn clobbered_by(&self, target: &ajave_ir::MethodKey) -> &std::collections::HashSet<FieldKey> {
        if let Some(w) = self.writes.get(target) {
            return w;
        }
        if let Some(ct) = ajave_models::contract_of(&target.class, &target.name, &target.desc) {
            if ct.effect == ajave_models::Effect::Pure {
                return &self.nothing;
            }
        }
        &self.all_written
    }
}

#[derive(Default, Clone)]
pub struct IntervalCpa {
    /// Field-abstraction precision. Empty by default, which disables field
    /// tracking entirely (every cell reads as Top) — always sound.
    pub field_prec: FieldPrec,
    /// Fields known to be non-null after constructor completes.
    /// When loading such a field from a NonNull object, the result is NonNull.
    pub nonnull_fields: std::collections::HashSet<ajave_ir::FieldKey>,
    /// Methods known to always return non-null.
    pub nonnull_returns: std::collections::HashSet<ajave_ir::MethodKey>,
}

impl Cpa for IntervalCpa {
    type State = IState;
    type Prec = ();

    fn initial(&self, prog: &Program, at: &ProgramPoint) -> IState {
        let mut nullness = BTreeMap::new();
        // Mark Ref-typed parameters as NonNull at method entry.
        // For instance methods, slot 0 = `this` (always non-null).
        // For static methods, slot 0 = first param (non-null from caller).
        // Use param_slot_count + 1 to cover both cases (instance `this` slot).
        if let Some(body) = prog.body(&at.method) {
            let max_param_slot = param_slot_count(&at.method.desc) + 1;
            for (idx, vi) in body.vars.iter().enumerate() {
                if vi.ty == ajave_ir::Ty::Ref {
                    if let ajave_ir::VarKind::Local(slot) = vi.kind {
                        if (slot as usize) < max_param_slot {
                            nullness.insert(VarId(idx as u32), Nullness::NonNull);
                        }
                    }
                }
            }
        }
        IState {
            at: at.clone(),
            vars: BTreeMap::new(),
            float_vars: BTreeMap::new(),
            nullness,
            array_lens: BTreeMap::new(),
            fields: BTreeMap::new(),
            field_null: BTreeMap::new(),
        }
    }

    fn transfer(
        &self,
        state: &IState,
        prog: &Program,
        edge: &Edge,
        to: &ProgramPoint,
        _prec: &(),
    ) -> Vec<IState> {
        let Some(body) = prog.body(&to.method) else {
            return vec![];
        };
        let mut next = state.clone();
        next.at = to.clone();

        match edge {
            Edge::Stmt(block, idx) => {
                match &body.block(*block).stmts[*idx] {
                    Stmt::Assign(v, rv) => {
                        // Float/double destinations are tracked in the float
                        // domain; everything else in the integer domain.
                        let is_float_var = body
                            .vars
                            .get(v.0 as usize)
                            .map(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
                            .unwrap_or(false);
                        // Whichever domain the destination belongs to, the other
                        // one must be invalidated. JVM locals are reused across
                        // types, so a slot that held an int earlier can be
                        // reassigned as a double; leaving the stale integer
                        // interval behind would let it narrow a value it no
                        // longer describes, and prove an assertion that does
                        // not hold. Removing the entry restores Top.
                        if is_float_var {
                            let fval = next.eval_rvalue_float(rv);
                            next.set_float(*v, fval);
                            next.vars.remove(v);
                        } else {
                            let val = next.eval_rvalue_typed(rv, &body.vars);
                            next.set(*v, val);
                            next.float_vars.remove(v);
                        }
                        // Track nullness for reference-producing rvalues.
                        let mut n = next.eval_nullness(rv);
                        // Field nullness: if loading from a NonNull object and
                        // the field is known-initialized in the constructor,
                        // the result is NonNull.
                        if n == Nullness::Unknown {
                            match rv {
                                Rvalue::GetField { obj: Operand::Var(ov), field } => {
                                    if next.get_nullness(*ov) == Nullness::NonNull
                                        && self.nonnull_fields.contains(field)
                                    {
                                        n = Nullness::NonNull;
                                    }
                                }
                                Rvalue::Call { target, .. } => {
                                    if self.nonnull_returns.contains(target) {
                                        n = Nullness::NonNull;
                                    }
                                }
                                _ => {}
                            }
                        }
                        next.set_nullness(*v, n);
                        // Track the length of the array this var now refers to.
                        // `NewArray` fixes it; a copy carries it along. Anything
                        // else leaves it Top, which is sound.
                        let len = match rv {
                            Rvalue::NewArray { len, .. } => {
                                // A negative length throws NegativeArraySizeException
                                // rather than producing an array, so on the paths
                                // that survive the length is non-negative.
                                next.eval_operand(len).meet(Interval { lo: 0, hi: i32::MAX as i64 })
                            }
                            Rvalue::Use(Operand::Var(src)) => next.get_array_len(*src),
                            _ => Interval::top(),
                        };
                        next.set_array_len(*v, len);

                        // A call may write fields, so anything it can reach has
                        // to drop back to Top before we continue.
                        if let Rvalue::Call { target, .. } = rv {
                            let clobbered = self.field_prec.clobbered_by(target).clone();
                            next.invalidate_fields(&clobbered);
                        }
                    }
                    Stmt::Assume(op) => {
                        let iv = next.eval_operand(op);
                        if iv.definitely_zero() {
                            return vec![]; // infeasible: assume(false) prunes the path.
                        }
                    }
                    Stmt::PutStatic(fk, val) => {
                        // Exactly one cell exists per static field, so this
                        // always replaces what was there.
                        let iv = next.eval_operand(val);
                        next.set_field(fk, iv, true);
                        let n = next.operand_nullness(val);
                        next.set_field_null(fk, n, true);
                    }
                    Stmt::PutField { field, val, .. } => {
                        let strong = self.field_prec.may_update_strongly(field, false);
                        let iv = next.eval_operand(val);
                        next.set_field(field, iv, strong);
                        let n = next.operand_nullness(val);
                        next.set_field_null(field, n, strong);
                    }
                    // ArrayStore: element values are not modelled (only lengths).
                    _ => {}
                }
                vec![next]
            }
            Edge::Term(block, taken, _) => {
                if let (
                    Some(is_then),
                    ajave_ir::Terminator::Branch {
                        cond: Operand::Var(cv),
                        ..
                    },
                ) = (taken, &body.block(*block).term)
                {
                    if let Some((op, a, b)) = find_defining_bin(body, *block, *cv) {
                        let eff_op = if *is_then { op } else { negate_binop(op) };
                        let (ia, ib) = (next.eval_operand(a), next.eval_operand(b));
                        if let Some((na, nb)) = Interval::narrow(eff_op, ia, ib) {
                            if let Operand::Var(av) = a {
                                next.set(*av, na);
                            }
                            if let Operand::Var(bv) = b {
                                next.set(*bv, nb);
                            }
                        }
                        // Nullness narrowing on null comparisons.
                        // `Ne(obj, null)` true → obj is NonNull, false → obj is Null
                        // `Eq(obj, null)` true → obj is Null, false → obj is NonNull
                        let is_null_cmp_a = matches!(b, Operand::Const(Const::Null));
                        let is_null_cmp_b = matches!(a, Operand::Const(Const::Null));
                        if is_null_cmp_a || is_null_cmp_b {
                            let ref_operand = if is_null_cmp_a { a } else { b };
                            if let Operand::Var(rv) = ref_operand {
                                let narrowed_null = match eff_op {
                                    BinOp::Ne => Nullness::NonNull,
                                    BinOp::Eq => Nullness::Null,
                                    _ => Nullness::Unknown,
                                };
                                if narrowed_null != Nullness::Unknown {
                                    next.set_nullness(*rv, narrowed_null);
                                }
                            }
                        }
                        // Float narrowing through the Cmp chain javac emits
                        // for float comparisons.
                        narrow_float_through_cmp(&mut next, body, *block, eff_op, a, b);
                    }
                }
                // Exceptional-edge narrowing: the handler is reachable only
                // when a Check in the source block *fails* (the exception is
                // thrown). Narrow by the join of each Check's failure state
                // (negate_binop(op) applied to its operands). If every failure
                // branch is infeasible the path is pruned entirely.
                //
                // Explicit Throw terminators are excluded: those are
                // programmer-initiated throws, not implicit Check failures,
                // so there is no condition here to negate.
                let is_exc = !matches!(body.block(*block).term, ajave_ir::Terminator::Throw(_))
                    && body
                        .block(*block)
                        .exceptional
                        .iter()
                        .any(|e| e.target == to.block);
                if is_exc {
                    let mut exc_state: Option<IState> = None;
                    for stmt in &body.block(*block).stmts {
                        if let Stmt::Check(oid) = stmt {
                            let ob = body.obligation(*oid);
                            if let Operand::Var(cv) = &ob.cond {
                                if let Some((op, a, b)) = find_defining_bin(body, *block, *cv) {
                                    let mut narrowed = next.clone();
                                    let (ia, ib) = (next.eval_operand(a), next.eval_operand(b));
                                    if let Some((na, nb)) = Interval::narrow(negate_binop(op), ia, ib) {
                                        if let Operand::Var(av) = a {
                                            narrowed.set(*av, na);
                                        }
                                        if let Operand::Var(bv) = b {
                                            narrowed.set(*bv, nb);
                                        }
                                    }
                                    exc_state = Some(match exc_state {
                                        None => narrowed,
                                        Some(s) => s.join(&narrowed),
                                    });
                                }
                            }
                        }
                    }
                    if let Some(s) = exc_state {
                        next = s;
                    }
                }
                if next.is_bottom() {
                    return vec![];
                }
                vec![next]
            }
            Edge::Exit(_) => vec![next],
        }
    }
}

// ── Widening interval CPA for float-loop bodies ────────────────────────────

/// An interval CPA that joins at loop headers with widening, enabling fixpoint
/// computation over unbounded float loops. Handles both int and float variables.
pub struct WideningIntervalCpa {
    /// Abstract transfer is identical to the non-widening CPA — including
    /// nullness and array-length tracking. Only `merge` differs, so we
    /// delegate rather than maintain a second copy that can drift.
    pub base: IntervalCpa,
    /// Blocks that are targets of back-edges (loop headers).
    pub loop_headers: HashSet<BlockId>,
    /// Float constants from comparisons in the body — used as widening thresholds.
    /// Instead of widening to ±∞, widen to the nearest threshold value.
    pub float_thresholds: Vec<f64>,
    /// Integer constants from comparisons — thresholds for int widening.
    pub int_thresholds: Vec<i64>,
    /// How many joins to perform before switching to widening.
    pub widen_delay: usize,
    /// Per-block join count.
    pub join_counts: std::cell::RefCell<std::collections::HashMap<BlockId, usize>>,
}

impl WideningIntervalCpa {
    /// Detect loop headers: any block targeted by a back-edge (target.0 <= source.0).
    /// Detect loop headers and extract widening thresholds from the body.
    pub fn from_body(body: &ajave_ir::Body) -> Self {
        Self::from_body_with(body, IntervalCpa::default())
    }

    /// Same, but carrying the interprocedural nullness facts the plain CPA uses.
    pub fn from_body_with(body: &ajave_ir::Body, base: IntervalCpa) -> Self {
        let mut headers = HashSet::new();
        for block in &body.blocks {
            let succs: Vec<BlockId> = match &block.term {
                ajave_ir::Terminator::Goto(t) => vec![*t],
                ajave_ir::Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
                ajave_ir::Terminator::Switch { cases, default, .. } => {
                    let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
                    v.push(*default);
                    v
                }
                _ => vec![],
            };
            for s in succs {
                if s.0 <= block.id.0 {
                    headers.insert(s);
                }
            }
        }
        // Extract constants from Cmp and Bin comparisons as thresholds.
        let mut float_thresholds: Vec<f64> = vec![0.0];
        let mut int_thresholds: Vec<i64> = vec![0];
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Stmt::Assign(_, rv) = stmt {
                    match rv {
                        Rvalue::Cmp(CmpKind::FloatL | CmpKind::FloatG, a, b) => {
                            for op in [a, b] {
                                match op {
                                    Operand::Const(Const::Float(f)) => {
                                        float_thresholds.push(*f as f64);
                                    }
                                    Operand::Const(Const::Double(d)) => {
                                        float_thresholds.push(*d);
                                    }
                                    _ => {}
                                }
                            }
                        }
                        Rvalue::Bin(op, a, b)
                            if matches!(
                                op,
                                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq
                            ) =>
                        {
                            for op in [a, b] {
                                match op {
                                    Operand::Const(Const::Int(n)) => {
                                        int_thresholds.push(*n as i64);
                                    }
                                    Operand::Const(Const::Float(f)) => {
                                        float_thresholds.push(*f as f64);
                                    }
                                    Operand::Const(Const::Double(d)) => {
                                        float_thresholds.push(*d);
                                    }
                                    _ => {}
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        // Also add constants from assignments (initial values).
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Stmt::Assign(_, Rvalue::Use(Operand::Const(c))) = stmt {
                    match c {
                        Const::Float(f) => float_thresholds.push(*f as f64),
                        Const::Double(d) => float_thresholds.push(*d),
                        Const::Int(n) => int_thresholds.push(*n as i64),
                        _ => {}
                    }
                }
            }
        }
        float_thresholds.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        float_thresholds.dedup();
        int_thresholds.sort();
        int_thresholds.dedup();

        WideningIntervalCpa {
            base,
            loop_headers: headers,
            float_thresholds,
            int_thresholds,
            widen_delay: 30,
            join_counts: std::cell::RefCell::new(std::collections::HashMap::new()),
        }
    }

    /// Widen an IState with thresholds: instead of jumping to ±∞, jump to the
    /// next threshold constant from the program.
    fn widen_state_thresholded(
        old: &IState,
        new: &IState,
        float_thresh: &[f64],
        int_thresh: &[i64],
    ) -> IState {
        let mut vars = BTreeMap::new();
        let keys: std::collections::BTreeSet<_> =
            old.vars.keys().chain(new.vars.keys()).copied().collect();
        for k in keys {
            let ov = old.get(k);
            let nv = new.get(k);
            let w = Interval::widen_thresholded(ov, nv, int_thresh);
            if w != Interval::top() {
                vars.insert(k, w);
            }
        }
        let mut float_vars = BTreeMap::new();
        let fkeys: std::collections::BTreeSet<_> =
            old.float_vars.keys().chain(new.float_vars.keys()).copied().collect();
        for k in fkeys {
            let ov = old.get_float(k);
            let nv = new.get_float(k);
            let w = FloatInterval::widen_thresholded(ov, nv, float_thresh);
            if !w.is_top() {
                float_vars.insert(k, w);
            }
        }
        let mut nullness = BTreeMap::new();
        let nkeys: std::collections::BTreeSet<_> =
            old.nullness.keys().chain(new.nullness.keys()).copied().collect();
        for k in nkeys {
            let j = old.get_nullness(k).join(new.get_nullness(k));
            if j != Nullness::Unknown {
                nullness.insert(k, j);
            }
        }
        // Array lengths are widened like any other interval: an allocation
        // inside a loop can have a length that grows each iteration, so join
        // alone would not be guaranteed to stabilise.
        let mut array_lens = BTreeMap::new();
        let akeys: std::collections::BTreeSet<_> =
            old.array_lens.keys().chain(new.array_lens.keys()).copied().collect();
        for k in akeys {
            let w = Interval::widen_thresholded(
                old.get_array_len(k), new.get_array_len(k), int_thresh,
            );
            if w != Interval::top() {
                array_lens.insert(k, w);
            }
        }
        let mut fields = BTreeMap::new();
        let ffk: std::collections::BTreeSet<_> =
            old.fields.keys().chain(new.fields.keys()).cloned().collect();
        for k in ffk {
            let w = Interval::widen_thresholded(old.get_field(&k), new.get_field(&k), int_thresh);
            if w != Interval::top() {
                fields.insert(k, w);
            }
        }
        let mut field_null = BTreeMap::new();
        let fnk: std::collections::BTreeSet<_> =
            old.field_null.keys().chain(new.field_null.keys()).cloned().collect();
        for k in fnk {
            let j = old.get_field_null(&k).join(new.get_field_null(&k));
            if j != Nullness::Unknown {
                field_null.insert(k, j);
            }
        }
        IState {
            at: old.at.clone(),
            vars,
            float_vars,
            nullness,
            array_lens,
            fields,
            field_null,
        }
    }

    /// Widen an IState: for each variable, apply the standard widening operator.
    #[allow(dead_code)]
    fn widen_state(old: &IState, new: &IState) -> IState {
        let mut vars = BTreeMap::new();
        let keys: std::collections::BTreeSet<_> =
            old.vars.keys().chain(new.vars.keys()).copied().collect();
        for k in keys {
            let ov = old.get(k);
            let nv = new.get(k);
            let w = Interval::widen(ov, nv);
            if w != Interval::top() {
                vars.insert(k, w);
            }
        }
        let mut float_vars = BTreeMap::new();
        let fkeys: std::collections::BTreeSet<_> =
            old.float_vars.keys().chain(new.float_vars.keys()).copied().collect();
        for k in fkeys {
            let ov = old.get_float(k);
            let nv = new.get_float(k);
            let w = FloatInterval::widen(ov, nv);
            if !w.is_top() {
                float_vars.insert(k, w);
            }
        }
        let mut nullness = BTreeMap::new();
        let nkeys: std::collections::BTreeSet<_> =
            old.nullness.keys().chain(new.nullness.keys()).copied().collect();
        for k in nkeys {
            let j = old.get_nullness(k).join(new.get_nullness(k));
            if j != Nullness::Unknown {
                nullness.insert(k, j);
            }
        }
        let mut array_lens = BTreeMap::new();
        let akeys: std::collections::BTreeSet<_> =
            old.array_lens.keys().chain(new.array_lens.keys()).copied().collect();
        for k in akeys {
            let w = Interval::widen(old.get_array_len(k), new.get_array_len(k));
            if w != Interval::top() {
                array_lens.insert(k, w);
            }
        }
        let mut fields = BTreeMap::new();
        let ffk: std::collections::BTreeSet<_> =
            old.fields.keys().chain(new.fields.keys()).cloned().collect();
        for k in ffk {
            let w = Interval::widen(old.get_field(&k), new.get_field(&k));
            if w != Interval::top() {
                fields.insert(k, w);
            }
        }
        let mut field_null = BTreeMap::new();
        let fnk: std::collections::BTreeSet<_> =
            old.field_null.keys().chain(new.field_null.keys()).cloned().collect();
        for k in fnk {
            let j = old.get_field_null(&k).join(new.get_field_null(&k));
            if j != Nullness::Unknown {
                field_null.insert(k, j);
            }
        }
        IState {
            at: old.at.clone(),
            vars,
            float_vars,
            nullness,
            array_lens,
            fields,
            field_null,
        }
    }
}

/// Integer widening operators.
impl Interval {
    pub fn widen_thresholded(old: Interval, new: Interval, thresholds: &[i64]) -> Interval {
        if new.is_bottom() {
            return old;
        }
        if old.is_bottom() {
            return new;
        }
        let lo = if new.lo < old.lo {
            thresholds
                .iter()
                .rev()
                .copied()
                .find(|&t| t <= new.lo)
                .unwrap_or(NEG_INF)
        } else {
            old.lo
        };
        let hi = if new.hi > old.hi {
            thresholds
                .iter()
                .copied()
                .find(|&t| t >= new.hi)
                .unwrap_or(POS_INF)
        } else {
            old.hi
        };
        Interval { lo, hi }
    }
    pub fn widen(old: Interval, new: Interval) -> Interval {
        if new.is_bottom() {
            return old;
        }
        if old.is_bottom() {
            return new;
        }
        Interval {
            lo: if new.lo < old.lo { NEG_INF } else { old.lo },
            hi: if new.hi > old.hi { POS_INF } else { old.hi },
        }
    }
}

/// Narrow float intervals through a CmpKind comparison chain.
///
/// The IR pattern for float branches is:
///   cmp_var = cmp(FloatL/FloatG, float_a, float_b)
///   bool_var = cmp_var OP 0       // e.g. < 0, <= 0, >= 0, == 0
///   if bool_var then ... else ...
///
/// From the effective `OP` on `cmp_var` we derive the effective float comparison:
///   cmp_var < 0  → float_a < float_b
///   cmp_var <= 0 → float_a <= float_b
///   cmp_var > 0  → float_a > float_b
///   cmp_var >= 0 → float_a >= float_b
///   cmp_var == 0 → float_a == float_b
///   cmp_var != 0 → float_a != float_b
fn narrow_float_through_cmp(
    state: &mut IState,
    body: &ajave_ir::Body,
    block: BlockId,
    eff_op: BinOp,
    cmp_operand: &Operand,
    zero_operand: &Operand,
) {
    // Only handle `cmp_var OP 0` pattern.
    let is_cmp_vs_zero = matches!(zero_operand, Operand::Const(Const::Int(0)));
    let cmp_var = match cmp_operand {
        Operand::Var(v) => *v,
        _ => return,
    };
    if !is_cmp_vs_zero {
        return;
    }
    // Find the Cmp that defines cmp_var.
    let Some((kind, float_a, float_b)) = find_defining_cmp(body, block, cmp_var) else {
        return;
    };
    if !matches!(kind, CmpKind::FloatL | CmpKind::FloatG) {
        return;
    }
    // The effective int comparison on cmp_var maps directly to a float comparison
    // on the original float operands.
    let fa = state.eval_operand_float(float_a);
    let fb = state.eval_operand_float(float_b);
    if let Some((na, nb)) = FloatInterval::narrow(eff_op, fa, fb) {
        if let Operand::Var(av) = float_a {
            state.set_float(*av, na);
        }
        if let Operand::Var(bv) = float_b {
            state.set_float(*bv, nb);
        }
    }
}

impl Cpa for WideningIntervalCpa {
    type State = IState;
    type Prec = ();

    fn initial(&self, prog: &Program, at: &ProgramPoint) -> IState {
        self.base.initial(prog, at)
    }

    fn transfer(
        &self,
        state: &IState,
        prog: &Program,
        edge: &Edge,
        to: &ProgramPoint,
        prec: &(),
    ) -> Vec<IState> {
        self.base.transfer(state, prog, edge, to, prec)
    }

    /// Join-then-widen at loop headers.
    ///
    /// Without this the CPA is purely path-sensitive and a loop whose trip
    /// count is not statically known never converges — it just exhausts the
    /// state cap and reports the analysis incomplete, which forfeits the
    /// proof. Joining at the header collapses the per-iteration states into
    /// one; widening after `widen_delay` joins forces that sequence to
    /// stabilise in finite time.
    ///
    /// Widening is applied only after a delay so that loops which do converge
    /// on their own keep their precise bounds; the delay costs iterations,
    /// never soundness, because both join and widen are upper bounds on the
    /// states they replace.
    fn merge(
        &self,
        new: &IState,
        reached: &IState,
        _prec: &(),
    ) -> MergeResult<IState> {
        if new.at != reached.at || !self.loop_headers.contains(&new.at.block) {
            return MergeResult::Sep;
        }

        let count = {
            let mut counts = self.join_counts.borrow_mut();
            let c = counts.entry(new.at.block).or_insert(0);
            *c += 1;
            *c
        };

        let combined = if count > self.widen_delay {
            Self::widen_state_thresholded(
                reached, new, &self.float_thresholds, &self.int_thresholds,
            )
        } else {
            reached.join(new)
        };

        // Returning `Joined` unconditionally would re-enqueue the state
        // forever, since the driver skips its `stop` check whenever a merge
        // fires. Report `Sep` once the result adds nothing to what we already
        // reached and let `stop` subsume it instead.
        if combined.leq(reached) {
            MergeResult::Sep
        } else {
            MergeResult::Joined(combined)
        }
    }
}
