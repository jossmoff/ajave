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

use std::collections::BTreeMap;
use std::ops::{Add, Mul, Neg, Sub};

use roast_core::artifact::ProgramPoint;
use roast_core::cpa::{Cpa, HasLocation, Lattice};
use roast_ir::{BinOp, Const, Edge, Operand, Program, Rvalue, Stmt, VarId};

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
    fn join(self, o: Interval) -> Interval {
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

/// `VarId -> Interval`. A variable missing from the map is implicitly Top:
/// this keeps the map small (only entries we've learned something about)
/// rather than pre-populating every variable in the body.
#[derive(Clone, Debug)]
pub struct IState {
    pub at: ProgramPoint,
    pub vars: BTreeMap<VarId, Interval>,
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
    /// Evaluate an rvalue. Anything outside plain integer arithmetic and
    /// comparisons is Top -- sound, just uninformative.
    pub fn eval_rvalue(&self, rv: &Rvalue) -> Interval {
        match rv {
            Rvalue::Use(o) => self.eval_operand(o),
            Rvalue::Neg(o) => self.eval_operand(o).neg(),
            Rvalue::Bin(op, a, b) => {
                let (ia, ib) = (self.eval_operand(a), self.eval_operand(b));
                match op {
                    BinOp::Add => ia.add(ib),
                    BinOp::Sub => ia.sub(ib),
                    BinOp::Mul => ia.mul(ib),
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        eval_comparison(*op, ia, ib)
                    }
                    // Bitwise/shift/div/rem/etc: not modelled, stay Top.
                    _ => Interval::top(),
                }
            }
            _ => Interval::top(),
        }
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
                return false; // self is Top where other is narrower: not leq.
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
        IState {
            at: self.at.clone(),
            vars,
        }
    }
    fn is_bottom(&self) -> bool {
        self.vars.values().any(|i| i.is_bottom())
    }
}

impl HasLocation for IState {
    fn location(&self) -> &ProgramPoint {
        &self.at
    }
}

/// Find the statement in `body`'s block that defines `v` as `Bin(op, a, b)`,
/// searching backward from the end of the block. This is how branch edges
pub struct IntervalCpa;

impl Cpa for IntervalCpa {
    type State = IState;
    type Prec = ();

    fn initial(&self, _prog: &Program, at: &ProgramPoint) -> IState {
        IState {
            at: at.clone(),
            vars: BTreeMap::new(),
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
                        let val = next.eval_rvalue(rv);
                        next.set(*v, val);
                    }
                    Stmt::Assume(op) => {
                        let iv = next.eval_operand(op);
                        if iv.definitely_zero() {
                            return vec![]; // infeasible: assume(false) prunes the path.
                        }
                    }
                    // PutStatic/PutField/ArrayStore: no locals affected, and we
                    // don't model heap state in this domain -- nothing to do.
                    _ => {}
                }
                vec![next]
            }
            Edge::Term(block, taken, _) => {
                if let (
                    Some(is_then),
                    roast_ir::Terminator::Branch {
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
                let is_exc = !matches!(body.block(*block).term, roast_ir::Terminator::Throw(_))
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
                if next.is_bottom() {
                    return vec![];
                }
                vec![next]
            }
            Edge::Exit(_) => vec![next],
        }
    }
}
