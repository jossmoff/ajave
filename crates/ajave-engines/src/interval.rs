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
use ajave_core::fixpoint::{AbstractDomain, HasLocation, Lattice, MergePolicy, MergeResult};
use ajave_ir::{
    BinOp, BlockId, CmpKind, Const, Edge, FieldKey, Operand, Program, Rvalue, Stmt, Ty, VarId,
};

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
    /// The single value this interval admits, if it admits exactly one.
    ///
    /// `None` covers both "more than one value" and bottom. B3's element cells
    /// are keyed by a concrete index, so this is the test for whether an index
    /// expression can be used as a key at all.
    pub fn as_const(self) -> Option<i64> {
        if !self.is_bottom() && self.lo == self.hi {
            Some(self.lo)
        } else {
            None
        }
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
/// bounds).
///
/// # Why endpoint arithmetic is sound here
///
/// This comment used to claim "all arithmetic over-approximates: rounding goes
/// outward". That was false — there is no outward rounding in this file, and
/// `add` is a plain `f64` sum under round-to-nearest-even. The code is sound
/// for a different and stronger reason, and saying so matters because the
/// false version invited an audit to look for unsoundness that was not there,
/// and distracted from the one that was.
///
/// IEEE addition, subtraction and multiplication are **monotone** in each
/// operand. The extremum of `fl(x ⊕ y)` over a box is therefore attained at a
/// corner of that box, and `fl(lo ⊕ lo)` computed here is bit-identical to what
/// the JVM computes at that corner. For `double` the result is *exact*, not an
/// over-approximation.
///
/// # And why 32-bit `float` needed a rounding step
///
/// That argument only holds when this domain's arithmetic has the *same*
/// precision as the JVM's. It does not for `Ty::Float`: the JVMS specifies
/// `fadd`/`fmul` as binary32, and computing them in `f64` is **more** precise
/// — so the resulting interval could exclude the value the JVM produces.
///
/// `benchmarks/ajave/jvm-floats/FloatIsNotDouble` is the case:
/// `fadd(1.0f, 1.0e-8f)` is bit-identical to `1.0f`, because the increment is
/// below half the gap between consecutive floats at 1.0f, while
/// `dadd(1.0, 1.0e-8)` is `1.00000001`. The f64 model therefore proved
/// `sum > 1.0f`, which the JVM violates — a wrong TRUE, confirmed by
/// `Blackboard::contested()` firing against a replay-certified violation.
///
/// `narrow_to_f32` is applied at every assignment to a `Ty::Float`
/// destination. Monotonicity survives it (`as f32` is itself
/// round-to-nearest), so the endpoints stay exact — now for binary32.
#[derive(Clone, Copy, Debug)]
pub struct FloatInterval {
    pub lo: f64,
    pub hi: f64,
}

impl FloatInterval {
    /// Round both endpoints to the nearest `f32`, widening outward where the
    /// two directions disagree.
    ///
    /// `as f32` is round-to-nearest, so an endpoint can move *inward* by up to
    /// half an ulp. For a bound that must contain every binary32 result, the
    /// low end has to go down and the high end up, so each is nudged to the
    /// adjacent float when rounding moved it the wrong way.
    pub fn to_f32_precision(self) -> FloatInterval {
        if self.is_bottom() {
            return self;
        }
        let lo32 = self.lo as f32;
        let hi32 = self.hi as f32;
        let lo = if (lo32 as f64) > self.lo {
            // Rounded up: step down to keep the true infimum inside.
            next_f32_down(lo32) as f64
        } else {
            lo32 as f64
        };
        let hi = if (hi32 as f64) < self.hi {
            next_f32_up(hi32) as f64
        } else {
            hi32 as f64
        };
        FloatInterval { lo, hi }
    }
}

/// Next representable `f32` below `x`, saturating at negative infinity.
fn next_f32_down(x: f32) -> f32 {
    if x.is_nan() || x == f32::NEG_INFINITY {
        return x;
    }
    if x == 0.0 {
        return -f32::from_bits(1);
    }
    let bits = x.to_bits();
    f32::from_bits(if x > 0.0 { bits - 1 } else { bits + 1 })
}

/// Next representable `f32` above `x`, saturating at infinity.
fn next_f32_up(x: f32) -> f32 {
    if x.is_nan() || x == f32::INFINITY {
        return x;
    }
    if x == 0.0 {
        return f32::from_bits(1);
    }
    let bits = x.to_bits();
    f32::from_bits(if x > 0.0 { bits + 1 } else { bits - 1 })
}

impl PartialEq for FloatInterval {
    fn eq(&self, other: &Self) -> bool {
        (self.is_bottom() && other.is_bottom()) || (self.lo == other.lo && self.hi == other.hi)
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
    pub fn widen_thresholded(
        old: FloatInterval,
        new: FloatInterval,
        thresholds: &[f64],
    ) -> FloatInterval {
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
    fn narrow(
        op: BinOp,
        a: FloatInterval,
        b: FloatInterval,
    ) -> Option<(FloatInterval, FloatInterval)> {
        if a.is_bottom() || b.is_bottom() {
            return Some((FloatInterval::bottom(), FloatInterval::bottom()));
        }
        let na = match op {
            BinOp::Lt => FloatInterval {
                lo: a.lo,
                hi: a.hi.min(b.hi),
            },
            BinOp::Le => FloatInterval {
                lo: a.lo,
                hi: a.hi.min(b.hi),
            },
            BinOp::Gt => FloatInterval {
                lo: a.lo.max(b.lo),
                hi: a.hi,
            },
            BinOp::Ge => FloatInterval {
                lo: a.lo.max(b.lo),
                hi: a.hi,
            },
            BinOp::Eq => FloatInterval {
                lo: a.lo.max(b.lo),
                hi: a.hi.min(b.hi),
            },
            _ => a,
        };
        let nb = match op {
            BinOp::Lt => FloatInterval {
                lo: b.lo.max(a.lo),
                hi: b.hi,
            },
            BinOp::Le => FloatInterval {
                lo: b.lo.max(a.lo),
                hi: b.hi,
            },
            BinOp::Gt => FloatInterval {
                lo: b.lo,
                hi: b.hi.min(a.hi),
            },
            BinOp::Ge => FloatInterval {
                lo: b.lo,
                hi: b.hi.min(a.hi),
            },
            BinOp::Eq => FloatInterval {
                lo: b.lo.max(a.lo),
                hi: b.hi.min(a.hi),
            },
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
    // Named for the domain operation, not the std trait: these are
    // interval/term algebra, and `Interval::div` reads correctly.
    #[allow(clippy::should_implement_trait)]
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

    // Named for the domain operation, not the std trait: these are
    // interval/term algebra, and `Interval::div` reads correctly.
    #[allow(clippy::should_implement_trait)]
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
        BinOp::Ne => (
            a.hi < b.lo || b.hi < a.lo,
            a.lo == a.hi && b.lo == b.hi && a.lo == b.lo,
        ),
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
        if self == other {
            self
        } else {
            Nullness::Unknown
        }
    }
    fn leq(self, other: Self) -> bool {
        self == other || other == Nullness::Unknown
    }
    /// Greatest lower bound, with one caveat: this lattice has no bottom, so
    /// two *conflicting* definite answers fall back to `Unknown` rather than
    /// picking one. That only arises on an infeasible state — the flat cell and
    /// the site cell describe the same object — and `Unknown` is above both, so
    /// it is sound whether or not the state is reachable. Picking either side
    /// would not be.
    fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Nullness::Unknown, o) => o,
            (s, Nullness::Unknown) => s,
            (s, o) if s == o => s,
            _ => Nullness::Unknown,
        }
    }
}

/// Everything `IState::combine_heap` returns: the B2 field cells and their
/// nullness, the escaped-field set, and the B3 array element cells and
/// per-site defaults.
///
/// A struct rather than a tuple because `join` and both `widen`s all build it,
/// and a positional five-tuple is exactly how two of those three would come to
/// disagree about which half is which.
struct CombinedHeap {
    field_cells: BTreeMap<(ajave_ir::AllocSite, FieldKey), Interval>,
    field_cell_null: BTreeMap<(ajave_ir::AllocSite, FieldKey), Nullness>,
    escaped_fields: std::collections::BTreeSet<FieldKey>,
    array_cells: BTreeMap<(ajave_ir::AllocSite, i64), Interval>,
    array_default: BTreeMap<ajave_ir::AllocSite, Interval>,
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
    /// B2. A *refinement* of the flat cell, keyed by the allocation site of the
    /// receiver. Missing = Top, so this map only ever narrows a read.
    ///
    /// **Soundness.** The flat abstraction above is safe because it merges:
    /// every write to `Box.v` lands in one cell, so no read can be narrower
    /// than the truth. Site-indexing breaks that, and is recovered by one rule:
    /// a write whose receiver's site is *not* known marks the field escaped,
    /// after which its cells are void and every read falls back to the flat
    /// cell — exactly the pre-B2 behaviour. The effective value of `o.f` for a
    /// receiver at site `s` is therefore `flat(f)` meet `cell(s, f)` when `f`
    /// has not escaped, and `flat(f)` otherwise. Both conjuncts hold of the
    /// object, so their meet does too.
    ///
    /// `benchmarks/ajave/heap/UnknownReceiverReadsTheMergedCell` is the program
    /// named after that rule, and it is wrong-TRUE without it.
    ///
    /// Keyed by a bare `AllocSite`, which is **body-scoped**: an `IState`
    /// belongs to one `Body`'s fixpoint and never outlives it, and `interval`
    /// does not inline. `CLAUDE.md`'s rule about context-relative identifiers
    /// applies the moment either of those changes.
    pub field_cells: BTreeMap<(ajave_ir::AllocSite, FieldKey), Interval>,
    /// Nullness of the same site-indexed cells. Missing = Unknown.
    pub field_cell_null: BTreeMap<(ajave_ir::AllocSite, FieldKey), Nullness>,
    /// Fields written through a receiver whose allocation site is unknown.
    /// Their cells carry no information. Grows monotonically, which is what
    /// keeps the fixpoint terminating.
    pub escaped_fields: std::collections::BTreeSet<FieldKey>,
    /// B3. Element value per `(AllocSite, constant index)`. Missing is **not**
    /// Top here — see `array_default` — because an array's contents are known
    /// completely from its allocation.
    pub array_cells: BTreeMap<(ajave_ir::AllocSite, i64), Interval>,
    /// The value of every element of a site's array that `array_cells` does
    /// not name, for sites this state is tracking.
    ///
    /// This is what makes element tracking possible at all without a
    /// points-to analysis: `newarray` zero-fills (JVMS 6.5), so at the
    /// allocation *every* element is known to be 0 and the default starts at
    /// `[0,0]`. A store at an index the domain cannot evaluate joins into the
    /// default **and** weakens every named cell, because it might have
    /// targeted any of them — the soundness rule, and the direct analogue of
    /// `escaped_fields` one level down. See
    /// `benchmarks/ajave/heap/ArrayStoreAtUnknownIndexWeakensEveryElement`.
    ///
    /// A site absent from this map is *not* tracked: its array came from a
    /// parameter, a call, or a site the domain gave up on, and every element
    /// reads Top.
    pub array_default: BTreeMap<ajave_ir::AllocSite, Interval>,
}

impl IState {
    /// The state that knows nothing: every variable Top, no field cells, no
    /// field escaped. Every map is empty because absence *is* Top throughout
    /// this domain — the property `join_block_intervals` once read as "this
    /// state has no opinion to contribute".
    pub fn top_at(at: ProgramPoint) -> IState {
        IState {
            at,
            vars: BTreeMap::new(),
            float_vars: BTreeMap::new(),
            nullness: BTreeMap::new(),
            array_lens: BTreeMap::new(),
            fields: BTreeMap::new(),
            field_null: BTreeMap::new(),
            field_cells: BTreeMap::new(),
            field_cell_null: BTreeMap::new(),
            escaped_fields: std::collections::BTreeSet::new(),
            array_cells: BTreeMap::new(),
            array_default: BTreeMap::new(),
        }
    }

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
        self.array_lens
            .get(&v)
            .copied()
            .unwrap_or_else(Interval::top)
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
        let v = if strong {
            n
        } else {
            self.get_field_null(f).join(n)
        };
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
        if !self.field_cells.is_empty() || !self.field_cell_null.is_empty() {
            self.field_cells.retain(|(_, f), _| !fs.contains(f));
            self.field_cell_null.retain(|(_, f), _| !fs.contains(f));
        }
    }

    /// The value of `f` read through a receiver at `site`, or through an
    /// unknown receiver when `site` is `None`. See `field_cells` for why this
    /// is a meet and when the refinement is dropped.
    pub fn eff_field(&self, site: Option<ajave_ir::AllocSite>, f: &FieldKey) -> Interval {
        let flat = self.get_field(f);
        match site {
            Some(s) if !self.escaped_fields.contains(f) => {
                match self.field_cells.get(&(s, f.clone())) {
                    Some(c) => flat.meet(*c),
                    None => flat,
                }
            }
            _ => flat,
        }
    }

    /// Nullness counterpart of `eff_field`. `Nullness::meet` is the refinement.
    pub fn eff_field_null(&self, site: Option<ajave_ir::AllocSite>, f: &FieldKey) -> Nullness {
        let flat = self.get_field_null(f);
        match site {
            Some(s) if !self.escaped_fields.contains(f) => {
                match self.field_cell_null.get(&(s, f.clone())) {
                    Some(c) => flat.meet(*c),
                    None => flat,
                }
            }
            _ => flat,
        }
    }

    /// Write through a receiver at a known site, where that site denotes at
    /// most one object. Replaces the cell, and *joins* the flat cell, which
    /// stays a sound summary for every other reader.
    fn set_field_cell(
        &mut self,
        site: ajave_ir::AllocSite,
        f: &FieldKey,
        i: Interval,
        n: Nullness,
    ) {
        self.set_field(f, i, false);
        self.set_field_null(f, n, false);
        if self.escaped_fields.contains(f) {
            return;
        }
        if i == Interval::top() {
            self.field_cells.remove(&(site, f.clone()));
        } else {
            self.field_cells.insert((site, f.clone()), i);
        }
        if n == Nullness::Unknown {
            self.field_cell_null.remove(&(site, f.clone()));
        } else {
            self.field_cell_null.insert((site, f.clone()), n);
        }
    }

    /// Begin tracking a freshly allocated array. `newarray` zero-fills, so
    /// every element is `[0, 0]` and there are no exceptions to that yet.
    fn track_new_array(&mut self, site: ajave_ir::AllocSite) {
        self.array_cells.retain(|(s, _), _| *s != site);
        self.array_default.insert(site, Interval { lo: 0, hi: 0 });
    }

    /// The value of `arr[idx]` where `arr` is at `site`. `idx` is `None` when
    /// the index is not a constant.
    pub fn eff_elem(&self, site: Option<ajave_ir::AllocSite>, idx: Option<i64>) -> Interval {
        let Some(site) = site else {
            return Interval::top();
        };
        // Not tracking this site: we do not know its contents, so Top.
        let Some(&dflt) = self.array_default.get(&site) else {
            return Interval::top();
        };
        match idx {
            Some(i) => self.array_cells.get(&(site, i)).copied().unwrap_or(dflt),
            // An unevaluable index may land anywhere, so the answer is the
            // join of every element: the default plus each named cell.
            None => self
                .array_cells
                .range((site, i64::MIN)..=(site, i64::MAX))
                .fold(dflt, |acc, (_, v)| acc.join(*v)),
        }
    }

    /// `arr[idx] = v` where `arr` is at `site` and `idx` is a constant.
    fn set_elem(&mut self, site: ajave_ir::AllocSite, idx: i64, v: Interval, strong: bool) {
        if !self.array_default.contains_key(&site) {
            return; // not tracking: nothing to refine
        }
        let v = if strong {
            v
        } else {
            self.eff_elem(Some(site), Some(idx)).join(v)
        };
        self.array_cells.insert((site, idx), v);
    }

    /// `arr[?] = v` — a store at an index the domain cannot evaluate. It may
    /// have targeted any element, so the default **and** every named cell take
    /// the value. This is the rule B3's soundness is; weakening is the only
    /// safe response to not knowing where a write went.
    fn set_elem_unknown_index(&mut self, site: ajave_ir::AllocSite, v: Interval) {
        let Some(dflt) = self.array_default.get_mut(&site) else {
            return;
        };
        *dflt = dflt.join(v);
        let keys: Vec<_> = self
            .array_cells
            .range((site, i64::MIN)..=(site, i64::MAX))
            .map(|(k, _)| *k)
            .collect();
        for k in keys {
            if let Some(c) = self.array_cells.get_mut(&k) {
                *c = c.join(v);
            }
        }
    }

    /// Stop tracking a site's contents entirely. Used when a store goes to an
    /// array whose site is unknown — that write could have hit *any* array, so
    /// no site's contents survive it — and when a call may have written one.
    fn untrack_arrays(&mut self) {
        self.array_cells.clear();
        self.array_default.clear();
    }

    /// A write we cannot attribute to a site. Every cell for `f` becomes void
    /// and stays void: this is the rule the site abstraction's soundness is.
    fn escape_field(&mut self, f: &FieldKey) {
        if self.escaped_fields.insert(f.clone()) {
            self.field_cells.retain(|(_, k), _| k != f);
            self.field_cell_null.retain(|(_, k), _| k != f);
        }
    }
    /// Combine the B2 site cells of two states under `f`, which is `Interval::join`
    /// for a merge and `Interval::widen` for a widening step.
    ///
    /// Shared by `join` and both `widen` variants so the three cannot drift —
    /// the defect class `CLAUDE.md` records as producer and consumer
    /// disagreeing about an artifact, here between the three places that have
    /// to agree about one map.
    fn combine_heap(
        &self,
        other: &Self,
        f: impl Fn(Interval, Interval) -> Interval,
    ) -> CombinedHeap {
        // Escape is monotone: a field either side could not attribute to a site
        // has no usable cell in the result either. This is also what bounds the
        // fixpoint, since the set only grows and is finite.
        let escaped: std::collections::BTreeSet<FieldKey> = self
            .escaped_fields
            .union(&other.escaped_fields)
            .cloned()
            .collect();
        let mut cells = BTreeMap::new();
        if !self.field_cells.is_empty() || !other.field_cells.is_empty() {
            let keys: std::collections::BTreeSet<_> = self
                .field_cells
                .keys()
                .chain(other.field_cells.keys())
                .cloned()
                .collect();
            for (site, fk) in keys {
                if escaped.contains(&fk) {
                    continue;
                }
                let j = f(
                    self.eff_field(Some(site), &fk),
                    other.eff_field(Some(site), &fk),
                );
                // Only worth storing when it actually refines the flat cell;
                // otherwise the entry costs a key and says nothing.
                if j != Interval::top() {
                    cells.insert((site, fk), j);
                }
            }
        }
        let mut cell_null = BTreeMap::new();
        if !self.field_cell_null.is_empty() || !other.field_cell_null.is_empty() {
            let keys: std::collections::BTreeSet<_> = self
                .field_cell_null
                .keys()
                .chain(other.field_cell_null.keys())
                .cloned()
                .collect();
            for (site, fk) in keys {
                if escaped.contains(&fk) {
                    continue;
                }
                let j = self
                    .eff_field_null(Some(site), &fk)
                    .join(other.eff_field_null(Some(site), &fk));
                if j != Nullness::Unknown {
                    cell_null.insert((site, fk), j);
                }
            }
        }
        // ── B3 array elements ──────────────────────────────────────────
        // A site is tracked in the result only if **both** states track it: a
        // state that is not tracking a site says its elements are Top, and a
        // join cannot be narrower than either operand. That is also why
        // `untrack_arrays` is a safe response to not knowing where a store
        // went — the ignorance propagates through every subsequent merge.
        let mut array_default = BTreeMap::new();
        let mut array_cells = BTreeMap::new();
        if !self.array_default.is_empty() && !other.array_default.is_empty() {
            for (site, a) in &self.array_default {
                let Some(b) = other.array_default.get(site) else {
                    continue;
                };
                array_default.insert(*site, f(*a, *b));
            }
            let keys: std::collections::BTreeSet<_> = self
                .array_cells
                .keys()
                .chain(other.array_cells.keys())
                .copied()
                .collect();
            for (site, idx) in keys {
                if !array_default.contains_key(&site) {
                    continue;
                }
                // `eff_elem` falls back to each side's own default, which is
                // what makes an element named on one side and not the other
                // combine correctly instead of silently taking one side.
                let j = f(
                    self.eff_elem(Some(site), Some(idx)),
                    other.eff_elem(Some(site), Some(idx)),
                );
                // An entry equal to the default says nothing; dropping it keeps
                // the map to the elements that actually differ.
                if Some(&j) != array_default.get(&site) {
                    array_cells.insert((site, idx), j);
                }
            }
        }

        CombinedHeap {
            field_cells: cells,
            field_cell_null: cell_null,
            escaped_fields: escaped,
            array_cells,
            array_default,
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
                    Interval {
                        lo: 0,
                        hi: i32::MAX as i64,
                    }
                } else {
                    known
                }
            }
            Rvalue::ArrayLength(_) => Interval {
                lo: 0,
                hi: i32::MAX as i64,
            },
            // Flat field cells. Absent reads as Top, so this is sound even
            // when field tracking is disabled or the cell was invalidated.
            // The receiver-aware read lives in `transfer`, which has the
            // site map; this fallback is the flat cell, which is what every
            // other caller of `eval_rvalue` should see.
            Rvalue::GetField { field, .. } => self.get_field(field),
            Rvalue::GetStatic(fk) => self.get_field(fk),
            Rvalue::Cmp(kind, a, b) => match kind {
                CmpKind::FloatL | CmpKind::FloatG => {
                    let (fa, fb) = (self.eval_operand_float(a), self.eval_operand_float(b));
                    eval_float_cmp(fa, fb)
                }
                CmpKind::Long => Interval { lo: -1, hi: 1 },
            },
            Rvalue::Bin(op, a, b) => {
                // Check if operands are float-typed.
                let is_float_op = var_types.is_some()
                    && match a {
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
                if is_float_op
                    && matches!(
                        op,
                        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                    )
                {
                    let (fa, fb) = (self.eval_operand_float(a), self.eval_operand_float(b));
                    return eval_float_comparison(*op, fa, fb);
                }

                // Nullness-aware comparison: if one side is Null and the other
                // has known nullness, we can resolve the comparison precisely.
                if matches!(op, BinOp::Ne | BinOp::Eq) {
                    let na = self.operand_nullness(a);
                    let nb = self.operand_nullness(b);
                    let null_cmp = match (na, nb) {
                        (Nullness::NonNull, Nullness::Null)
                        | (Nullness::Null, Nullness::NonNull) => Some(matches!(op, BinOp::Ne)),
                        (Nullness::Null, Nullness::Null) => Some(matches!(op, BinOp::Eq)),
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
            Rvalue::Nondet(Ty::Float | Ty::Double, _)
            | Rvalue::Havoc(Ty::Float | Ty::Double, _) => FloatInterval::top(),
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
            // An int-to-float conversion should read the *integer* interval and
            // widen it, and there used to be an arm here that did. It matched
            // `Rvalue::Use(Operand::Var(_))`, which the `Rvalue::Use(o)` arm
            // above already covers, so it never ran -- and its comment said
            // "cast" while it matched a use, so reordering would not have
            // helped either. `Rvalue::Cast` is still unhandled and falls
            // through to top, which loses the bound. Tracked as #93 with a
            // benchmark owed before the fix; the dead code is removed rather
            // than left to look like the case is covered.
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
        BinOp::And => Interval {
            lo: 0,
            hi: a.hi.min(b.hi),
        },
        BinOp::Or | BinOp::Xor => {
            let m = a.hi.max(b.hi);
            // Smallest all-ones mask that covers `m`.
            let bound = if m <= 0 {
                0
            } else {
                let bits = 64 - (m as u64).leading_zeros();
                if bits >= 63 {
                    i64::MAX
                } else {
                    (1i64 << bits) - 1
                }
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
            | (
                "java/util/Collections",
                "EMPTY_LIST" | "EMPTY_MAP" | "EMPTY_SET"
            )
    )
}

impl IState {
    /// Compute the nullness of a reference-producing rvalue.
    pub fn eval_nullness(&self, rv: &Rvalue) -> Nullness {
        match rv {
            Rvalue::Use(Operand::Const(Const::Null)) => Nullness::Null,
            Rvalue::Use(Operand::Const(Const::Str(_) | Const::Class(_))) => Nullness::NonNull,
            Rvalue::Use(Operand::Var(v)) => self.get_nullness(*v),
            Rvalue::New { .. } => Nullness::NonNull,
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
            if !fv.leq(
                other
                    .float_vars
                    .get(v)
                    .copied()
                    .unwrap_or_else(FloatInterval::top),
            ) {
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
        // B2 site cells. Comparing the *effective* value — flat meet cell, with
        // the cell dropped once the field has escaped — is what makes this
        // consistent with `escaped_fields` growing: a state that has escaped a
        // field is simply not refined there, and the flat comparison above
        // already covers it. Comparing the raw cells instead would call a state
        // with a stale cell narrower than one that correctly discarded it.
        if !self.field_cells.is_empty()
            || !other.field_cells.is_empty()
            || !self.field_cell_null.is_empty()
            || !other.field_cell_null.is_empty()
        {
            let keys: std::collections::BTreeSet<_> = self
                .field_cells
                .keys()
                .chain(other.field_cells.keys())
                .cloned()
                .collect();
            for (site, f) in keys {
                if !self
                    .eff_field(Some(site), &f)
                    .leq(other.eff_field(Some(site), &f))
                {
                    return false;
                }
            }
            let nkeys: std::collections::BTreeSet<_> = self
                .field_cell_null
                .keys()
                .chain(other.field_cell_null.keys())
                .cloned()
                .collect();
            for (site, f) in nkeys {
                if !self
                    .eff_field_null(Some(site), &f)
                    .leq(other.eff_field_null(Some(site), &f))
                {
                    return false;
                }
            }
        }
        // B3 array elements, compared through `eff_elem`. The direction that
        // matters: a state *not* tracking a site claims Top for its elements,
        // so it sits above one that does, and tracking must never be required
        // of `other`.
        if !other.array_default.is_empty() {
            for (site, b_dflt) in &other.array_default {
                match self.array_default.get(site) {
                    Some(a_dflt) if a_dflt.leq(*b_dflt) => {}
                    // Either we do not track the site — we claim Top, which is
                    // not below a real bound — or our default is wider.
                    _ => return false,
                }
            }
            let keys: std::collections::BTreeSet<_> = self
                .array_cells
                .keys()
                .chain(other.array_cells.keys())
                .copied()
                .collect();
            for (site, idx) in keys {
                if !other.array_default.contains_key(&site) {
                    continue; // `other` claims Top for this whole site
                }
                if !self
                    .eff_elem(Some(site), Some(idx))
                    .leq(other.eff_elem(Some(site), Some(idx)))
                {
                    return false;
                }
            }
        }
        true
    }

    fn join(&self, other: &Self) -> Self {
        let h = self.combine_heap(other, Interval::join);
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
        let fkeys: std::collections::BTreeSet<_> = self
            .float_vars
            .keys()
            .chain(other.float_vars.keys())
            .copied()
            .collect();
        for k in fkeys {
            let j = self.get_float(k).join(other.get_float(k));
            if !j.is_top() {
                float_vars.insert(k, j);
            }
        }
        let mut nullness = BTreeMap::new();
        let nkeys: std::collections::BTreeSet<_> = self
            .nullness
            .keys()
            .chain(other.nullness.keys())
            .copied()
            .collect();
        for k in nkeys {
            let j = self.get_nullness(k).join(other.get_nullness(k));
            if j != Nullness::Unknown {
                nullness.insert(k, j);
            }
        }
        let mut array_lens = BTreeMap::new();
        let akeys: std::collections::BTreeSet<_> = self
            .array_lens
            .keys()
            .chain(other.array_lens.keys())
            .copied()
            .collect();
        for k in akeys {
            let j = self.get_array_len(k).join(other.get_array_len(k));
            if j != Interval::top() {
                array_lens.insert(k, j);
            }
        }
        let mut fields = BTreeMap::new();
        let fkeys2: std::collections::BTreeSet<_> = self
            .fields
            .keys()
            .chain(other.fields.keys())
            .cloned()
            .collect();
        for k in fkeys2 {
            let j = self.get_field(&k).join(other.get_field(&k));
            if j != Interval::top() {
                fields.insert(k, j);
            }
        }
        let mut field_null = BTreeMap::new();
        let nfkeys: std::collections::BTreeSet<_> = self
            .field_null
            .keys()
            .chain(other.field_null.keys())
            .cloned()
            .collect();
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
            field_cells: h.field_cells,
            field_cell_null: h.field_cell_null,
            escaped_fields: h.escaped_fields,
            array_cells: h.array_cells,
            array_default: h.array_default,
        }
    }
    fn is_bottom(&self) -> bool {
        self.vars.values().any(|i| i.is_bottom()) || self.float_vars.values().any(|f| f.is_bottom())
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
            b'J' | b'D' => {
                pos += 1;
                slot += 2;
            }
            b'L' => {
                while pos < bytes.len() && bytes[pos] != b';' {
                    pos += 1;
                }
                pos += 1;
                slot += 1;
            }
            b'[' => {
                while pos < bytes.len() && bytes[pos] == b'[' {
                    pos += 1;
                }
                if pos < bytes.len() && bytes[pos] == b'L' {
                    while pos < bytes.len() && bytes[pos] != b';' {
                        pos += 1;
                    }
                    pos += 1;
                } else if pos < bytes.len() {
                    pos += 1;
                }
                slot += 1;
            }
            _ => {
                pos += 1;
                slot += 1;
            }
        }
    }
    slot
}

/// Find the statement in `body`'s block that defines `v` as `Cmp(kind, a, b)`.
fn find_defining_cmp(
    body: &ajave_ir::Body,
    block: BlockId,
    v: VarId,
) -> Option<(CmpKind, &Operand, &Operand)> {
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
    /// B2. Per method: which variables provably hold which allocation site,
    /// and whether a site in that method denotes at most one object.
    ///
    /// Computed once in `analyze_field_precision` rather than per transfer:
    /// `transfer` runs once per edge per fixpoint iteration, and recomputing a
    /// whole-body scan there would make the refinement cost more than it buys.
    /// Lookup is a single hash probe; the inner map is a `BTreeMap` because the
    /// domain's `leq`/`join` walk it.
    pub sites: std::collections::HashMap<ajave_ir::MethodKey, SiteInfo>,
}

/// Where a method's allocations are, and whether they are unique.
#[derive(Default, Clone)]
pub struct SiteInfo {
    /// Which object each reference holds, **before each statement**.
    ///
    /// Per program point, not per variable. The per-variable version was dead
    /// code on every real program: the lifter always inserts copies between a
    /// `new` and the receiver it is used as, and javac reuses slots so one
    /// variable holds different objects at different points. See
    /// `body_analysis::ref_alloc_sites_at` and issue #104.
    pub at: BTreeMap<(ajave_ir::BlockId, u32), crate::body_analysis::RefSiteMap>,
    /// The sites that denote **at most one object**, which is what permits a
    /// strong update to a site's cell. A `new` inside a loop runs once per
    /// iteration and summarises all of them, so replacing its cell would
    /// forget every object but the last.
    ///
    /// Per site, not per body. The per-body version (`!body_has_loops`)
    /// disabled site reasoning for *every* allocation in a method containing
    /// any loop — including allocations outside it, which are perfectly
    /// unique. Since a program that needs the AI at all has a loop the BMC
    /// cannot unroll, that made B2's enabling condition and its usefulness
    /// condition very nearly disjoint. See #104.
    pub unique_sites: std::collections::BTreeSet<ajave_ir::AllocSite>,
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
    /// Static fields this *program* cannot have made null.
    ///
    /// Distinct from `is_nonnull_static`, which answers for any program at all
    /// and so may only list `static final` fields with non-null initialisers.
    /// `System.out` is not one of those -- `System.setOut(null)` is legal --
    /// but a program that never calls a stream setter cannot observe it null.
    /// See `ai::stable_stream_statics`.
    pub nonnull_statics: std::collections::HashSet<ajave_ir::FieldKey>,
}

impl AbstractDomain for IntervalCpa {
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
            field_cells: BTreeMap::new(),
            field_cell_null: BTreeMap::new(),
            escaped_fields: std::collections::BTreeSet::new(),
            array_cells: BTreeMap::new(),
            array_default: BTreeMap::new(),
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

        // B2. Resolve a receiver operand to the allocation site it provably
        // holds. `None` — a parameter, a field load, a merge of two `new`s, a
        // body with a loop, or site tracking switched off — means "unknown
        // receiver", which is what every caller must treat conservatively.
        let site_info = self.field_prec.sites.get(&to.method);
        // The point this edge's statement runs at, which is what the site map
        // is keyed by. A terminator edge has no statement index and resolves
        // nothing, which costs precision on branch conditions and is correct.
        let here: Option<(ajave_ir::BlockId, u32)> = match edge {
            Edge::Stmt(block, idx) => Some((*block, *idx as u32)),
            _ => None,
        };
        let site_of = |op: &Operand| -> Option<ajave_ir::AllocSite> {
            let si = site_info?;
            if !site_fields_enabled() {
                return None;
            }
            let m = si.at.get(&here?)?;
            let site = match op {
                Operand::Var(v) => m.get(v).copied()?,
                _ => return None,
            };
            // A site inside a loop summarises many objects; refining its cell
            // would forget all but the last. Reads through it fall back to the
            // flat abstraction, which merges and is sound.
            si.unique_sites.contains(&site).then_some(site)
        };

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
                            let mut fval = next.eval_rvalue_float(rv);
                            // A `float` destination means the JVM computed this
                            // in binary32. This domain works in `f64`, which is
                            // *more* precise, so without this step the interval
                            // can exclude the value the JVM actually produces —
                            // see `FloatInterval`'s doc and
                            // `benchmarks/ajave/jvm-floats/FloatIsNotDouble`.
                            let is_f32 = body
                                .vars
                                .get(v.0 as usize)
                                .map(|vi| matches!(vi.ty, Ty::Float))
                                .unwrap_or(false);
                            if is_f32 {
                                fval = fval.to_f32_precision();
                            }
                            next.set_float(*v, fval);
                            next.vars.remove(v);
                        } else {
                            let mut val = next.eval_rvalue_typed(rv, &body.vars);
                            // B2. `eval_rvalue` answers from the flat cell
                            // because it has no site map. Here we do, so a load
                            // through a pinned receiver may use the refinement.
                            if let Rvalue::GetField { obj, field } = rv {
                                if let Some(site) = site_of(obj) {
                                    val = val.meet(next.eff_field(Some(site), field));
                                }
                            }
                            // B3. An element read. `None` for the index means
                            // the index is not a constant, which `eff_elem`
                            // answers with the join of every element.
                            if let Rvalue::ArrayLoad { arr, idx } = rv {
                                let i = next.eval_operand(idx).as_const();
                                val = val.meet(next.eff_elem(site_of(arr), i));
                            }
                            next.set(*v, val);
                            next.float_vars.remove(v);
                        }
                        // Track nullness for reference-producing rvalues.
                        let mut n = next.eval_nullness(rv);
                        // Program-level static nullness, which `eval_nullness`
                        // cannot answer because it is a fact about this
                        // program rather than about the field.
                        if n == Nullness::Unknown {
                            if let Rvalue::GetStatic(fk) = rv {
                                if self.nonnull_statics.contains(fk) {
                                    n = Nullness::NonNull;
                                }
                            }
                        }
                        // Field nullness: if loading from a NonNull object and
                        // the field is known-initialized in the constructor,
                        // the result is NonNull.
                        if n == Nullness::Unknown {
                            match rv {
                                Rvalue::GetField {
                                    obj: obj @ Operand::Var(ov),
                                    field,
                                } => {
                                    if next.get_nullness(*ov) == Nullness::NonNull
                                        && self.nonnull_fields.contains(field)
                                    {
                                        n = Nullness::NonNull;
                                    }
                                    if n == Nullness::Unknown {
                                        if let Some(site) = site_of(obj) {
                                            n = next.eff_field_null(Some(site), field);
                                        }
                                    }
                                }
                                Rvalue::Call { target, .. }
                                    if self.nonnull_returns.contains(target) =>
                                {
                                    n = Nullness::NonNull;
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
                                next.eval_operand(len).meet(Interval {
                                    lo: 0,
                                    hi: i32::MAX as i64,
                                })
                            }
                            Rvalue::Use(Operand::Var(src)) => next.get_array_len(*src),
                            _ => Interval::top(),
                        };
                        next.set_array_len(*v, len);
                        // B3. A fresh array is zero-filled (JVMS 6.5), so this
                        // is the one point at which the contents are known
                        // completely — which is what makes element tracking
                        // possible without a points-to analysis.
                        if let Rvalue::NewArray { site, .. } = rv {
                            if site_fields_enabled() {
                                next.track_new_array(*site);
                            }
                        }

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
                    Stmt::PutField { obj, field, val } => {
                        let iv = next.eval_operand(val);
                        let n = next.operand_nullness(val);
                        match site_of(obj) {
                            // Receiver pinned to a site that denotes at most
                            // one object: refine that cell, and keep the flat
                            // cell a sound summary by joining into it.
                            Some(site) => next.set_field_cell(site, field, iv, n),
                            // Receiver unknown. This write may have landed on
                            // any object of the class, so every cell for the
                            // field is void from here on and reads fall back to
                            // the flat abstraction. The whole B2 soundness
                            // argument is this arm.
                            None => {
                                let strong = self.field_prec.may_update_strongly(field, false);
                                next.escape_field(field);
                                next.set_field(field, iv, strong);
                                next.set_field_null(field, n, strong);
                            }
                        }
                    }
                    Stmt::ArrayStore { arr, idx, val } => {
                        let v = next.eval_operand(val);
                        match site_of(arr) {
                            Some(site) => match next.eval_operand(idx).as_const() {
                                // A constant index into a site that denotes one
                                // array: replace exactly that element.
                                Some(i) => next.set_elem(site, i, v, true),
                                // An index we cannot evaluate may hit any
                                // element of *this* array, so every element of
                                // it takes the value. See
                                // `ArrayStoreAtUnknownIndexWeakensEveryElement`.
                                None => next.set_elem_unknown_index(site, v),
                            },
                            // A store through an array whose site is unknown
                            // could have hit any array at all, so no site's
                            // contents survive it. The array analogue of
                            // `escape_field`, except that there is no per-array
                            // key to escape — the receiver is the unknown.
                            None => next.untrack_arrays(),
                        }
                    }
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
                                    if let Some((na, nb)) =
                                        Interval::narrow(negate_binop(op), ia, ib)
                                    {
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
                // A handler is entered with the exception object on the stack,
                // and that object is never null.
                //
                // JVMS 6.5 `athrow`: throwing `null` raises a
                // `NullPointerException` *instead*, so the reference that
                // reaches a handler is always a real object; the implicitly
                // thrown exceptions (NPE, AIOOBE, ClassCast, ...) are
                // constructed by the JVM and non-null by the same argument.
                //
                // Without this, `catch (Exception e) { e.printStackTrace(); }`
                // leaves an undischargeable NullDeref on `e`. That single
                // obligation is the whole reason
                // `jbmc-regression/BufferedReaderReadLine` scores nothing.
                //
                // The lifter gives a handler block an entry stack of exactly
                // one `Ty::Ref` (see `lift.rs`, "Handler blocks are entered
                // with the exception object on the stack"), and `stack_slot`
                // keys stack variables by `(depth, ty)`, so the object is the
                // unique variable with kind `Stack(0)` and type `Ref`.
                if body
                    .block(*block)
                    .exceptional
                    .iter()
                    .any(|e| e.target == to.block)
                {
                    for (i, vi) in body.vars.iter().enumerate() {
                        if matches!(vi.kind, ajave_ir::VarKind::Stack(0)) && vi.ty == Ty::Ref {
                            next.set_nullness(VarId(i as u32), Nullness::NonNull);
                        }
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

// ── Widening merge policy for loop bodies ──────────────────────────────────

/// Joins at loop headers with widening, so a fixpoint exists over loops whose
/// trip count is not statically known. Handles both int and float variables.
///
/// This used to be a whole second `Cpa` implementation, `WideningIntervalCpa`,
/// whose `initial` and `transfer` delegated to the plain interval CPA verbatim
/// and whose only real content was `merge`. Separating the merge policy from
/// the abstract domain is what lets it be the one thing it always was: the
/// same domain, explored differently.
pub struct WidenAtLoopHeaders {
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

impl WidenAtLoopHeaders {
    /// Detect loop headers (any block targeted by a back-edge, i.e.
    /// `target.0 <= source.0`) and extract widening thresholds from the body.
    ///
    /// Takes no domain. The old `from_body_with` had to be handed an
    /// `IntervalCpa` purely so the struct could satisfy `Cpa::transfer`; a
    /// merge policy needs no domain at all, which is the point.
    // The guard states the condition the arm is about; folding it into the
    // pattern hides which operators this case covers.
    #[allow(clippy::redundant_guards)]
    pub fn from_body(body: &ajave_ir::Body) -> Self {
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

        log::debug!(
            "interval-ai: {} thresholds float={:?} int={:?} headers={:?}",
            body.key,
            float_thresholds,
            int_thresholds,
            headers.len()
        );
        WidenAtLoopHeaders {
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
        let h = old.combine_heap(new, |a, b| Interval::widen_thresholded(a, b, int_thresh));
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
        let fkeys: std::collections::BTreeSet<_> = old
            .float_vars
            .keys()
            .chain(new.float_vars.keys())
            .copied()
            .collect();
        for k in fkeys {
            let ov = old.get_float(k);
            let nv = new.get_float(k);
            let w = FloatInterval::widen_thresholded(ov, nv, float_thresh);
            if !w.is_top() {
                float_vars.insert(k, w);
            }
        }
        let mut nullness = BTreeMap::new();
        let nkeys: std::collections::BTreeSet<_> = old
            .nullness
            .keys()
            .chain(new.nullness.keys())
            .copied()
            .collect();
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
        let akeys: std::collections::BTreeSet<_> = old
            .array_lens
            .keys()
            .chain(new.array_lens.keys())
            .copied()
            .collect();
        for k in akeys {
            let w =
                Interval::widen_thresholded(old.get_array_len(k), new.get_array_len(k), int_thresh);
            if w != Interval::top() {
                array_lens.insert(k, w);
            }
        }
        let mut fields = BTreeMap::new();
        let ffk: std::collections::BTreeSet<_> = old
            .fields
            .keys()
            .chain(new.fields.keys())
            .cloned()
            .collect();
        for k in ffk {
            let w = Interval::widen_thresholded(old.get_field(&k), new.get_field(&k), int_thresh);
            if w != Interval::top() {
                fields.insert(k, w);
            }
        }
        let mut field_null = BTreeMap::new();
        let fnk: std::collections::BTreeSet<_> = old
            .field_null
            .keys()
            .chain(new.field_null.keys())
            .cloned()
            .collect();
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
            field_cells: h.field_cells,
            field_cell_null: h.field_cell_null,
            escaped_fields: h.escaped_fields,
            array_cells: h.array_cells,
            array_default: h.array_default,
        }
    }

    /// Widen an IState: for each variable, apply the standard widening operator.
    #[allow(dead_code)]
    fn widen_state(old: &IState, new: &IState) -> IState {
        let h = old.combine_heap(new, Interval::widen);
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
        let fkeys: std::collections::BTreeSet<_> = old
            .float_vars
            .keys()
            .chain(new.float_vars.keys())
            .copied()
            .collect();
        for k in fkeys {
            let ov = old.get_float(k);
            let nv = new.get_float(k);
            let w = FloatInterval::widen(ov, nv);
            if !w.is_top() {
                float_vars.insert(k, w);
            }
        }
        let mut nullness = BTreeMap::new();
        let nkeys: std::collections::BTreeSet<_> = old
            .nullness
            .keys()
            .chain(new.nullness.keys())
            .copied()
            .collect();
        for k in nkeys {
            let j = old.get_nullness(k).join(new.get_nullness(k));
            if j != Nullness::Unknown {
                nullness.insert(k, j);
            }
        }
        let mut array_lens = BTreeMap::new();
        let akeys: std::collections::BTreeSet<_> = old
            .array_lens
            .keys()
            .chain(new.array_lens.keys())
            .copied()
            .collect();
        for k in akeys {
            let w = Interval::widen(old.get_array_len(k), new.get_array_len(k));
            if w != Interval::top() {
                array_lens.insert(k, w);
            }
        }
        let mut fields = BTreeMap::new();
        let ffk: std::collections::BTreeSet<_> = old
            .fields
            .keys()
            .chain(new.fields.keys())
            .cloned()
            .collect();
        for k in ffk {
            let w = Interval::widen(old.get_field(&k), new.get_field(&k));
            if w != Interval::top() {
                fields.insert(k, w);
            }
        }
        let mut field_null = BTreeMap::new();
        let fnk: std::collections::BTreeSet<_> = old
            .field_null
            .keys()
            .chain(new.field_null.keys())
            .cloned()
            .collect();
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
            field_cells: h.field_cells,
            field_cell_null: h.field_cell_null,
            escaped_fields: h.escaped_fields,
            array_cells: h.array_cells,
            array_default: h.array_default,
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

impl MergePolicy<IntervalCpa> for WidenAtLoopHeaders {
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
    fn merge(&self, new: &IState, reached: &IState, _prec: &()) -> MergeResult<IState> {
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
                reached,
                new,
                &self.float_thresholds,
                &self.int_thresholds,
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

/// Whether the B2 site-indexed field refinement is active.
///
/// An ablation switch, not a tuning knob. `AJAVE_SITE_FIELDS=0` returns the
/// analysis to the flat abstraction exactly, which is how the refinement's
/// cost and gain are measured rather than argued — and how a regression in it
/// can be separated from a regression anywhere else in the interval domain.
pub fn site_fields_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_SITE_FIELDS").as_deref() != Ok("0"))
}

#[cfg(test)]
mod domain_law_tests {
    //! The laws the interval domain must satisfy, and the two clauses its
    //! merge policy must satisfy.
    //!
    //! This file had no tests at all until 2026-10-26, which is how the
    //! coverage subtlety recorded on `fixpoint::covered_by` became a false
    //! TRUE on `assert2`. The laws here are checked over hand-built states
    //! rather than benchmark outcomes, so they generalise.

    use super::*;
    use ajave_core::fixpoint::laws;
    use ajave_ir::{BlockId, MethodKey};

    fn pp(block: u32) -> ProgramPoint {
        ProgramPoint {
            method: MethodKey {
                class: "Main".into(),
                name: "main".into(),
                desc: "()V".into(),
            },
            block: BlockId(block),
            index: 0,
        }
    }

    fn empty(block: u32) -> IState {
        IState {
            at: pp(block),
            vars: BTreeMap::new(),
            float_vars: BTreeMap::new(),
            nullness: BTreeMap::new(),
            array_lens: BTreeMap::new(),
            fields: BTreeMap::new(),
            field_null: BTreeMap::new(),
            field_cells: BTreeMap::new(),
            field_cell_null: BTreeMap::new(),
            escaped_fields: std::collections::BTreeSet::new(),
            array_cells: BTreeMap::new(),
            array_default: BTreeMap::new(),
        }
    }

    /// Deliberately varied: Top, two incomparable narrowings, one strictly
    /// below both, plus a float var, a nullness fact and an array length —
    /// every map in the state, because a law can hold on one map and fail on
    /// another.
    fn samples() -> Vec<IState> {
        let mut out = vec![empty(0)];

        let mut a = empty(0);
        a.vars.insert(VarId(0), Interval { lo: 0, hi: 10 });
        out.push(a);

        let mut b = empty(0);
        b.vars.insert(VarId(0), Interval { lo: 5, hi: 20 });
        out.push(b);

        let mut c = empty(0);
        c.vars.insert(VarId(0), Interval { lo: 5, hi: 10 });
        c.vars.insert(VarId(1), Interval::point(7));
        out.push(c);

        let mut d = empty(0);
        d.float_vars
            .insert(VarId(2), FloatInterval { lo: -1.0, hi: 1.0 });
        out.push(d);

        let mut e = empty(0);
        e.nullness.insert(VarId(3), Nullness::NonNull);
        e.array_lens.insert(VarId(3), Interval::point(4));
        out.push(e);

        let mut f = empty(0);
        f.nullness.insert(VarId(3), Nullness::Null);
        out.push(f);

        out
    }

    #[test]
    fn the_interval_domain_satisfies_the_lattice_laws() {
        laws::check_lattice_laws(&samples());
    }

    #[test]
    fn the_separating_policy_satisfies_both_clauses() {
        laws::check_merge_policy::<IntervalCpa, _>(&ajave_core::fixpoint::Sep, &samples(), &());
    }

    /// A body with a back-edge, so block 1 is a loop header and the policy is
    /// not vacuous.
    fn looping_body() -> ajave_ir::Body {
        let mk = MethodKey {
            class: "Main".into(),
            name: "main".into(),
            desc: "()V".into(),
        };
        ajave_ir::Body {
            is_static: true,
            key: mk,
            entry: BlockId(0),
            vars: vec![ajave_ir::VarInfo {
                kind: ajave_ir::VarKind::Local(0),
                ty: Ty::Int,
            }],
            obligations: vec![],
            blocks: vec![
                ajave_ir::Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![],
                    term: ajave_ir::Terminator::Goto(BlockId(1)),
                    exceptional: vec![],
                },
                ajave_ir::Block {
                    id: BlockId(1),
                    bytecode_offset: 1,
                    stmts: vec![],
                    // Back-edge to itself: BlockId(1) is a loop header.
                    term: ajave_ir::Terminator::Branch {
                        cond: ajave_ir::Operand::Const(ajave_ir::Const::Int(1)),
                        then_: BlockId(1),
                        else_: BlockId(2),
                    },
                    exceptional: vec![],
                },
                ajave_ir::Block {
                    id: BlockId(2),
                    bytecode_offset: 2,
                    stmts: vec![],
                    term: ajave_ir::Terminator::Return(None),
                    exceptional: vec![],
                },
            ],
        }
    }

    /// The point of separating the domain from the policy: the *same* domain
    /// explored under two policies is two techniques. `Sep` keeps loop
    /// iterations apart and exhausts its state cap; the widening policy
    /// collapses them at the header and converges.
    ///
    /// This is what the deleted `WideningIntervalCpa` existed to express, and
    /// it needed a second `Cpa` implementation to say it.
    #[test]
    fn the_same_domain_under_two_policies_is_two_techniques() {
        let body = counting_loop_body();
        let mut prog = ajave_ir::Program::default();
        prog.bodies.insert(body.key.clone(), body.clone());
        prog.entry = Some(body.key.clone());
        let start = ProgramPoint {
            method: body.key.clone(),
            block: body.entry,
            index: 0,
        };

        let cpa = IntervalCpa::default();
        let (_, sep_complete) =
            ajave_core::fixpoint::explore(&cpa, &ajave_core::fixpoint::Sep, &prog, &start, (), 40);

        let mut policy = WidenAtLoopHeaders::from_body(&body);
        policy.widen_delay = 2;
        let (reached, widen_complete) =
            ajave_core::fixpoint::explore(&cpa, &policy, &prog, &start, (), 40);

        assert!(
            !sep_complete,
            "the path-sensitive policy should exhaust a 40-state cap on this loop"
        );
        assert!(
            widen_complete,
            "the widening policy should converge inside the same cap, reached {}",
            reached.len()
        );
    }

    /// `i = 0; while (i < 100) i++;` — a counted loop whose iterations the
    /// path-sensitive policy keeps apart.
    fn counting_loop_body() -> ajave_ir::Body {
        use ajave_ir::{BinOp, Const, Operand, Rvalue, Stmt, Terminator};
        let mk = MethodKey {
            class: "Main".into(),
            name: "count".into(),
            desc: "()V".into(),
        };
        let i = VarId(0);
        let c = VarId(1);
        ajave_ir::Body {
            is_static: true,
            key: mk,
            entry: BlockId(0),
            vars: vec![
                ajave_ir::VarInfo {
                    kind: ajave_ir::VarKind::Local(0),
                    ty: Ty::Int,
                },
                ajave_ir::VarInfo {
                    kind: ajave_ir::VarKind::Stack(0),
                    ty: Ty::Int,
                },
            ],
            obligations: vec![],
            blocks: vec![
                ajave_ir::Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![Stmt::Assign(i, Rvalue::Use(Operand::Const(Const::Int(0))))],
                    term: Terminator::Goto(BlockId(1)),
                    exceptional: vec![],
                },
                // Loop header: c := i < 100; branch on c.
                ajave_ir::Block {
                    id: BlockId(1),
                    bytecode_offset: 1,
                    stmts: vec![Stmt::Assign(
                        c,
                        Rvalue::Bin(BinOp::Lt, Operand::Var(i), Operand::Const(Const::Int(100))),
                    )],
                    term: Terminator::Branch {
                        cond: Operand::Var(c),
                        then_: BlockId(2),
                        else_: BlockId(3),
                    },
                    exceptional: vec![],
                },
                // Body: i := i + 1, back-edge to the header.
                ajave_ir::Block {
                    id: BlockId(2),
                    bytecode_offset: 2,
                    stmts: vec![Stmt::Assign(
                        i,
                        Rvalue::Bin(BinOp::Add, Operand::Var(i), Operand::Const(Const::Int(1))),
                    )],
                    term: Terminator::Goto(BlockId(1)),
                    exceptional: vec![],
                },
                ajave_ir::Block {
                    id: BlockId(3),
                    bytecode_offset: 3,
                    stmts: vec![],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                },
            ],
        }
    }

    #[test]
    fn the_widening_policy_finds_its_loop_header() {
        let policy = WidenAtLoopHeaders::from_body(&looping_body());
        assert!(
            policy.loop_headers.contains(&BlockId(1)),
            "a block targeted by a back-edge is a loop header"
        );
        assert!(!policy.loop_headers.contains(&BlockId(0)));
    }

    #[test]
    fn the_widening_policy_satisfies_both_clauses() {
        let policy = WidenAtLoopHeaders::from_body(&looping_body());
        // States must sit at the loop header for the policy to engage at all.
        let at_header: Vec<IState> = samples()
            .into_iter()
            .map(|mut s| {
                s.at = pp(1);
                s
            })
            .collect();
        laws::check_merge_policy::<IntervalCpa, _>(&policy, &at_header, &());
    }

    #[test]
    fn the_widening_policy_leaves_other_blocks_alone() {
        let policy = WidenAtLoopHeaders::from_body(&looping_body());
        let mut a = empty(0);
        a.vars.insert(VarId(0), Interval { lo: 0, hi: 1 });
        let mut b = empty(0);
        b.vars.insert(VarId(0), Interval { lo: 0, hi: 2 });
        assert!(
            matches!(
                MergePolicy::<IntervalCpa>::merge(&policy, &b, &a, &()),
                MergeResult::Sep
            ),
            "block 0 is not a loop header, so nothing is joined there"
        );
    }

    /// Widening is delayed so loops that converge on their own keep their
    /// precise bounds. `widen_delay` is a fitted constant, so the delay's
    /// *semantics* are pinned here even though the value is not.
    #[test]
    fn widening_is_delayed_and_then_fires() {
        let mut policy = WidenAtLoopHeaders::from_body(&looping_body());
        policy.widen_delay = 2;

        let state = |hi: i64| {
            let mut s = empty(1);
            s.vars.insert(VarId(0), Interval { lo: 0, hi });
            s
        };

        // Merges 1 and 2 are inside the delay, so they are plain joins:
        // [0,1] ⊔ [0,2] = [0,2], exactly the union, no jump to a threshold.
        let mut reached = state(1);
        for step in 1..=2 {
            match MergePolicy::<IntervalCpa>::merge(&policy, &state(step + 1), &reached, &()) {
                MergeResult::Joined(j) => {
                    assert_eq!(
                        j.get(VarId(0)),
                        Interval {
                            lo: 0,
                            hi: step + 1
                        },
                        "merge {step} should be a plain join"
                    );
                    reached = j;
                }
                MergeResult::Sep => panic!("merge {step} should have joined"),
            }
        }

        // The next one is past the delay, so it widens rather than unions.
        match MergePolicy::<IntervalCpa>::merge(&policy, &state(4), &reached, &()) {
            MergeResult::Joined(j) => {
                let w = j.get(VarId(0));
                assert!(
                    w.hi > 4,
                    "past the delay the bound must jump beyond the union, got {w:?}"
                );
            }
            MergeResult::Sep => panic!("the widening merge should have joined"),
        }
    }

    /// The termination law. Widening exists so that a loop whose trip count is
    /// not statically known still reaches a fixpoint; without it the states
    /// just exhaust the cap and the proof is forfeited. Nothing tested this.
    #[test]
    fn widening_reaches_a_fixpoint_in_bounded_steps() {
        let mut policy = WidenAtLoopHeaders::from_body(&looping_body());
        policy.widen_delay = 2;

        let mut reached = {
            let mut s = empty(1);
            s.vars.insert(VarId(0), Interval::point(0));
            s
        };

        // Feed an ever-growing interval, as an unbounded counting loop does.
        let mut settled_at = None;
        for step in 1..=16i64 {
            let mut next = empty(1);
            next.vars.insert(VarId(0), Interval { lo: 0, hi: step });
            match MergePolicy::<IntervalCpa>::merge(&policy, &next, &reached, &()) {
                MergeResult::Joined(j) => reached = j,
                MergeResult::Sep => {
                    // Clause 2 says Sep here means the new state added nothing,
                    // i.e. the sequence has stabilised.
                    settled_at = Some(step);
                    break;
                }
            }
        }

        let at = settled_at.expect(
            "the widened sequence never stabilised in 16 steps — \
             the analysis would exhaust its state cap instead of converging",
        );
        assert!(
            at <= policy.widen_delay as i64 + 4,
            "stabilised only after {at} steps, which is slower than the delay explains"
        );
    }
}

/// B2. The site-indexed field refinement, and the one rule it rests on.
///
/// These assert on `IState` directly rather than through the engine, because
/// the question is what the *domain* guarantees. A test that drove the whole
/// portfolio would also pass if some other engine happened to cover the case.
#[cfg(test)]
mod site_field_tests {
    use super::*;
    use ajave_ir::{AllocSite, BlockId, FieldKey, MethodKey};

    fn pp() -> ProgramPoint {
        ProgramPoint {
            method: MethodKey {
                class: "Main".into(),
                name: "main".into(),
                desc: "()V".into(),
            },
            block: BlockId(0),
            index: 0,
        }
    }

    fn fk() -> FieldKey {
        FieldKey {
            class: "Box".into(),
            name: "v".into(),
            desc: "I".into(),
        }
    }

    fn site(i: u32) -> AllocSite {
        AllocSite {
            block: BlockId(0),
            index: i,
        }
    }

    fn iv(lo: i64, hi: i64) -> Interval {
        Interval { lo, hi }
    }

    /// The capability. `benchmarks/ajave/heap/TwoObjectsDistinctFieldValues`.
    #[test]
    fn two_sites_hold_distinct_field_values() {
        let mut st = IState::top_at(pp());
        st.set_field_cell(site(0), &fk(), iv(1, 1), Nullness::Unknown);
        st.set_field_cell(site(1), &fk(), iv(2, 2), Nullness::Unknown);
        assert_eq!(st.eff_field(Some(site(0)), &fk()), iv(1, 1));
        assert_eq!(st.eff_field(Some(site(1)), &fk()), iv(2, 2));
        // The flat cell an unknown receiver reads is Top, and that is the
        // whole point of the refinement rather than a defect. A weak update
        // joins into the existing cell, an absent cell *is* Top, and Top joined
        // with anything is Top — so for a class with two allocation sites the
        // flat abstraction learns nothing at all. That is exactly the pre-B2
        // behaviour, and it is what the site cells above recover.
        assert_eq!(st.eff_field(None, &fk()), Interval::top());
    }

    /// **The soundness rule.** A write through a receiver whose site is not
    /// known may have landed on any object of the class, so every cell for the
    /// field becomes void and reads fall back to the flat abstraction.
    ///
    /// Named after
    /// `benchmarks/ajave/heap/UnknownReceiverReadsTheMergedCell`, which is a
    /// wrong TRUE without this.
    #[test]
    fn a_write_through_an_unknown_receiver_voids_every_cell_for_the_field() {
        let mut st = IState::top_at(pp());
        st.set_field_cell(site(0), &fk(), iv(1, 1), Nullness::Unknown);
        st.set_field_cell(site(1), &fk(), iv(2, 2), Nullness::Unknown);

        // `c.v = 7` where `c` may be either object.
        st.escape_field(&fk());
        st.set_field(&fk(), iv(7, 7), false);

        assert!(
            st.eff_field(Some(site(0)), &fk()).lo <= 7
                && st.eff_field(Some(site(0)), &fk()).hi >= 7,
            "site 0 must admit the value written through the unknown receiver, \
             got {:?}",
            st.eff_field(Some(site(0)), &fk())
        );
        assert!(
            st.field_cells.is_empty(),
            "the cells are void, not merely overridden"
        );
    }

    /// Escape must be sticky. A cell re-established after the field escaped
    /// would restore exactly the unsound read the rule above prevents.
    #[test]
    fn a_cell_written_after_escape_is_not_recorded() {
        let mut st = IState::top_at(pp());
        st.escape_field(&fk());
        st.set_field_cell(site(0), &fk(), iv(5, 5), Nullness::Unknown);
        assert!(st.field_cells.is_empty());
        assert_eq!(
            st.eff_field(Some(site(0)), &fk()),
            st.get_field(&fk()),
            "a read through a known site is the flat cell once the field escaped"
        );
    }

    /// Escape is monotone across a merge, which is both the soundness
    /// requirement (one branch could not attribute the write) and what bounds
    /// the fixpoint, since the set only grows over a finite field set.
    #[test]
    fn escape_survives_a_join_from_either_side() {
        let mut a = IState::top_at(pp());
        a.set_field_cell(site(0), &fk(), iv(1, 1), Nullness::Unknown);
        let mut b = IState::top_at(pp());
        b.escape_field(&fk());
        b.set_field(&fk(), iv(9, 9), false);

        for (l, r) in [(&a, &b), (&b, &a)] {
            let j = l.join(r);
            assert!(
                j.escaped_fields.contains(&fk()),
                "escape from either side must survive the join"
            );
            assert!(j.field_cells.is_empty(), "and void its cells");
        }
    }

    /// A join must be above both operands. Without this the refinement could
    /// make a merged state claim something neither branch did.
    #[test]
    fn a_join_of_two_site_states_is_above_both() {
        let mut a = IState::top_at(pp());
        a.set_field_cell(site(0), &fk(), iv(1, 1), Nullness::Unknown);
        let mut b = IState::top_at(pp());
        b.set_field_cell(site(0), &fk(), iv(4, 4), Nullness::Unknown);
        let j = a.join(&b);
        assert!(a.leq(&j), "left operand is below the join");
        assert!(b.leq(&j), "right operand is below the join");
        assert_eq!(j.eff_field(Some(site(0)), &fk()), iv(1, 4));
    }

    /// B3. The one point at which an array's contents are fully known: a
    /// fresh array is zero-filled (JVMS 6.5), so every element is `[0,0]` and
    /// an element nobody wrote still reads 0. Without modelling the zero-fill
    /// there is nothing to track *from*.
    #[test]
    fn a_fresh_array_reads_zero_at_every_index() {
        let mut st = IState::top_at(pp());
        st.track_new_array(site(0));
        for i in [0, 1, 7, 1_000_000] {
            assert_eq!(st.eff_elem(Some(site(0)), Some(i)), iv(0, 0));
        }
        assert_eq!(st.eff_elem(Some(site(0)), None), iv(0, 0));
    }

    /// The capability. Constant-index stores are exact, and an element nobody
    /// wrote keeps the default.
    #[test]
    fn constant_index_stores_are_exact_and_leave_other_elements_alone() {
        let mut st = IState::top_at(pp());
        st.track_new_array(site(0));
        st.set_elem(site(0), 0, iv(7, 7), true);
        st.set_elem(site(0), 1, iv(9, 9), true);
        assert_eq!(st.eff_elem(Some(site(0)), Some(0)), iv(7, 7));
        assert_eq!(st.eff_elem(Some(site(0)), Some(1)), iv(9, 9));
        assert_eq!(
            st.eff_elem(Some(site(0)), Some(2)),
            iv(0, 0),
            "an element nobody wrote keeps the zero-fill"
        );
    }

    /// **The soundness rule.** A store at an index the domain cannot evaluate
    /// may have hit any element, so every element must admit the value.
    ///
    /// Named after
    /// `benchmarks/ajave/heap/ArrayStoreAtUnknownIndexWeakensEveryElement`.
    #[test]
    fn a_store_at_an_unknown_index_weakens_every_element() {
        let mut st = IState::top_at(pp());
        st.track_new_array(site(0));
        st.set_elem(site(0), 0, iv(7, 7), true);
        st.set_elem_unknown_index(site(0), iv(99, 99));
        assert_eq!(
            st.eff_elem(Some(site(0)), Some(0)),
            iv(7, 99),
            "the named element must admit the value the unknown store may have written"
        );
        assert_eq!(
            st.eff_elem(Some(site(0)), Some(5)),
            iv(0, 99),
            "and so must every element covered by the default"
        );
    }

    /// A store through an array whose site is unknown could have hit *any*
    /// array, so no site's contents survive it. There is no per-array key to
    /// escape here — the receiver itself is the unknown.
    #[test]
    fn a_store_through_an_unknown_array_untracks_every_site() {
        let mut st = IState::top_at(pp());
        st.track_new_array(site(0));
        st.track_new_array(site(1));
        st.set_elem(site(0), 0, iv(7, 7), true);
        st.untrack_arrays();
        assert_eq!(st.eff_elem(Some(site(0)), Some(0)), Interval::top());
        assert_eq!(st.eff_elem(Some(site(1)), Some(0)), Interval::top());
    }

    /// An untracked site reads Top, which makes a state not tracking it sit
    /// *above* one that does — so a join keeps only the sites both track.
    #[test]
    fn a_join_keeps_only_the_sites_both_states_track() {
        let mut a = IState::top_at(pp());
        a.track_new_array(site(0));
        a.set_elem(site(0), 0, iv(1, 1), true);
        let b = IState::top_at(pp()); // tracks nothing: every element Top

        for (l, r) in [(&a, &b), (&b, &a)] {
            let j = l.join(r);
            assert_eq!(
                j.eff_elem(Some(site(0)), Some(0)),
                Interval::top(),
                "one side knows nothing, so the join knows nothing"
            );
            assert!(l.leq(&j) && r.leq(&j), "and is above both operands");
        }
    }

    /// Two states that both track a site join elementwise, including where one
    /// names an element the other leaves at its default.
    #[test]
    fn a_join_of_two_tracked_sites_combines_elementwise() {
        let mut a = IState::top_at(pp());
        a.track_new_array(site(0));
        a.set_elem(site(0), 0, iv(5, 5), true);
        let mut b = IState::top_at(pp());
        b.track_new_array(site(0));
        // b leaves element 0 at the zero-fill default.
        b.set_elem(site(0), 1, iv(3, 3), true);

        let j = a.join(&b);
        assert_eq!(j.eff_elem(Some(site(0)), Some(0)), iv(0, 5));
        assert_eq!(j.eff_elem(Some(site(0)), Some(1)), iv(0, 3));
        assert!(a.leq(&j) && b.leq(&j));
    }

    /// Dropping cells on a call is sound because an absent cell is Top, and a
    /// call may have written the field through a receiver we never saw.
    #[test]
    fn a_call_that_may_write_the_field_drops_its_cells() {
        let mut st = IState::top_at(pp());
        st.set_field_cell(site(0), &fk(), iv(1, 1), Nullness::Unknown);
        let mut clobbered = std::collections::HashSet::new();
        clobbered.insert(fk());
        st.invalidate_fields(&clobbered);
        assert_eq!(st.eff_field(Some(site(0)), &fk()), Interval::top());
    }
}
