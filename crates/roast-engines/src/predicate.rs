//! Predicate abstraction CPA.
//!
//! Implements `Cpa` with a state that tracks truth values of predicates at
//! each program point. The precision (set of predicates) grows during CEGAR
//! refinement.
//!
//! Transfer computes strongest postcondition: for each predicate in the
//! precision, evaluate whether it is definitely true, definitely false, or
//! unknown after the edge.
//!
//! Original papers:
//! - Predicate abstraction: Graf & Saidi, CAV 1997.
//! - CEGAR: Clarke et al., CAV 2000 / JACM 2003.
//! - Lazy abstraction: Henzinger et al., POPL 2002.

use std::collections::BTreeMap;

use roast_core::artifact::ProgramPoint;
use roast_core::cpa::{Cpa, HasLocation, Lattice, MergeResult};
use roast_ir::*;

use crate::body_analysis::{find_defining_bin, negate_binop};

/// A predicate is a comparison between a variable and a constant or two variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Predicate {
    pub lhs: PredicateOperand,
    pub op: CompOp,
    pub rhs: PredicateOperand,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PredicateOperand {
    Var(VarId),
    Const(i64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CompOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl CompOp {
    fn negate(self) -> CompOp {
        match self {
            CompOp::Lt => CompOp::Ge,
            CompOp::Le => CompOp::Gt,
            CompOp::Gt => CompOp::Le,
            CompOp::Ge => CompOp::Lt,
            CompOp::Eq => CompOp::Ne,
            CompOp::Ne => CompOp::Eq,
        }
    }

    pub fn from_binop(op: BinOp) -> Option<CompOp> {
        match op {
            BinOp::Lt => Some(CompOp::Lt),
            BinOp::Le => Some(CompOp::Le),
            BinOp::Gt => Some(CompOp::Gt),
            BinOp::Ge => Some(CompOp::Ge),
            BinOp::Eq => Some(CompOp::Eq),
            BinOp::Ne => Some(CompOp::Ne),
            _ => None,
        }
    }
}

impl Predicate {
    /// Evaluate this predicate given concrete variable values.
    /// Returns Some(true/false) if decidable, None if unknown.
    pub fn evaluate(&self, var_vals: &BTreeMap<VarId, (i64, i64)>) -> Option<bool> {
        let lhs = match &self.lhs {
            PredicateOperand::Var(v) => var_vals.get(v).map(|&(lo, hi)| (lo, hi))?,
            PredicateOperand::Const(c) => (*c, *c),
        };
        let rhs = match &self.rhs {
            PredicateOperand::Var(v) => var_vals.get(v).map(|&(lo, hi)| (lo, hi))?,
            PredicateOperand::Const(c) => (*c, *c),
        };

        // Check if the predicate is definitely true or definitely false
        // given the ranges.
        match self.op {
            CompOp::Lt => {
                if lhs.1 < rhs.0 {
                    Some(true)
                } else if lhs.0 >= rhs.1 {
                    Some(false)
                } else {
                    None
                }
            }
            CompOp::Le => {
                if lhs.1 <= rhs.0 {
                    Some(true)
                } else if lhs.0 > rhs.1 {
                    Some(false)
                } else {
                    None
                }
            }
            CompOp::Gt => {
                if lhs.0 > rhs.1 {
                    Some(true)
                } else if lhs.1 <= rhs.0 {
                    Some(false)
                } else {
                    None
                }
            }
            CompOp::Ge => {
                if lhs.0 >= rhs.1 {
                    Some(true)
                } else if lhs.1 < rhs.0 {
                    Some(false)
                } else {
                    None
                }
            }
            CompOp::Eq => {
                if lhs.0 == lhs.1 && rhs.0 == rhs.1 && lhs.0 == rhs.0 {
                    Some(true)
                } else if lhs.1 < rhs.0 || rhs.1 < lhs.0 {
                    Some(false)
                } else {
                    None
                }
            }
            CompOp::Ne => {
                if lhs.1 < rhs.0 || rhs.1 < lhs.0 {
                    Some(true)
                } else if lhs.0 == lhs.1 && rhs.0 == rhs.1 && lhs.0 == rhs.0 {
                    Some(false)
                } else {
                    None
                }
            }
        }
    }

    /// Check if this predicate mentions a variable.
    pub fn mentions(&self, v: VarId) -> bool {
        matches!(&self.lhs, PredicateOperand::Var(x) if *x == v)
            || matches!(&self.rhs, PredicateOperand::Var(x) if *x == v)
    }

    /// Format as an SMT-LIB2 expression.
    pub fn to_smt2(&self) -> String {
        let lhs = match &self.lhs {
            PredicateOperand::Var(v) => format!("v{}", v.0),
            PredicateOperand::Const(c) => {
                if *c < 0 {
                    format!("(- {})", -c)
                } else {
                    c.to_string()
                }
            }
        };
        let rhs = match &self.rhs {
            PredicateOperand::Var(v) => format!("v{}", v.0),
            PredicateOperand::Const(c) => {
                if *c < 0 {
                    format!("(- {})", -c)
                } else {
                    c.to_string()
                }
            }
        };
        let op = match self.op {
            CompOp::Lt => "<",
            CompOp::Le => "<=",
            CompOp::Gt => ">",
            CompOp::Ge => ">=",
            CompOp::Eq => "=",
            CompOp::Ne => "distinct",
        };
        format!("({} {} {})", op, lhs, rhs)
    }
}

/// The precision: a set of predicates to track.
#[derive(Clone, Debug, Default)]
pub struct PredPrec {
    pub predicates: Vec<Predicate>,
}

/// The abstract state: truth value of each predicate (by index into PredPrec).
/// `None` = unknown, `Some(true)` = definitely true, `Some(false)` = definitely false.
#[derive(Clone, Debug)]
pub struct PredState {
    pub at: ProgramPoint,
    /// Truth values indexed by predicate position in PredPrec.
    pub values: Vec<Option<bool>>,
}

impl PredState {
    /// Create a state with all predicates unknown.
    pub fn top(at: ProgramPoint, n_predicates: usize) -> Self {
        PredState {
            at,
            values: vec![None; n_predicates],
        }
    }

    /// Check if this state is consistent (no contradictions).
    /// An inconsistent state is bottom.
    pub fn is_consistent(&self) -> bool {
        // A state with explicit contradictions is bottom.
        // For now we don't track contradictions explicitly.
        true
    }
}

impl Lattice for PredState {
    fn leq(&self, other: &Self) -> bool {
        // self ≤ other iff every predicate known in self is also known (same value) in other,
        // OR other has it unknown (Top).
        // i.e., self has MORE information than other, so other covers self.
        for (sv, ov) in self.values.iter().zip(other.values.iter()) {
            match (sv, ov) {
                (Some(a), Some(b)) if a != b => return false, // contradicts
                (Some(_), None) => {}                         // self knows more, that's fine for ≤
                (None, Some(_)) => return false, // other knows more, self doesn't cover
                _ => {}
            }
        }
        true
    }

    fn join(&self, other: &Self) -> Self {
        // Join: keep only predicates that agree.
        let values = self
            .values
            .iter()
            .zip(other.values.iter())
            .map(|(a, b)| match (a, b) {
                (Some(x), Some(y)) if x == y => Some(*x),
                _ => None,
            })
            .collect();
        PredState {
            at: self.at.clone(),
            values,
        }
    }

    fn is_bottom(&self) -> bool {
        // Bottom is when we know both true and false for the same predicate.
        // Since our join doesn't produce that, bottom is not representable
        // in this encoding. We use a separate flag.
        false
    }
}

impl HasLocation for PredState {
    fn location(&self) -> &ProgramPoint {
        &self.at
    }
}

pub struct PredicateCpa;

impl Cpa for PredicateCpa {
    type State = PredState;
    type Prec = PredPrec;

    fn initial(&self, _prog: &Program, at: &ProgramPoint) -> PredState {
        PredState {
            at: at.clone(),
            values: Vec::new(), // Will be sized by prec
        }
    }

    fn transfer(
        &self,
        state: &PredState,
        prog: &Program,
        edge: &Edge,
        to: &ProgramPoint,
        prec: &PredPrec,
    ) -> Vec<PredState> {
        let Some(body) = prog.body(&to.method) else {
            return vec![];
        };

        let mut next = state.clone();
        next.at = to.clone();

        // Ensure values vector matches precision size.
        while next.values.len() < prec.predicates.len() {
            next.values.push(None);
        }

        match edge {
            Edge::Stmt(block, idx) => {
                match &body.block(*block).stmts[*idx] {
                    Stmt::Assign(v, rv) => {
                        // Invalidate all predicates that mention the assigned variable.
                        for (i, pred) in prec.predicates.iter().enumerate() {
                            if pred.mentions(*v) {
                                // Try to re-evaluate if the rvalue is simple.
                                next.values[i] =
                                    evaluate_predicate_after_assign(pred, *v, rv, state, prec);
                            }
                        }
                    }
                    // assume(false) prunes the path outright. Anything else
                    // needs a predicate to say something about it, which the
                    // precision may or may not carry.
                    Stmt::Assume(Operand::Const(Const::Int(0))) => return vec![],
                    _ => {}
                }
                vec![next]
            }
            Edge::Term(block, taken, _) => {
                // On branch edges, try to learn predicate values from the condition.
                if let (
                    Some(is_then),
                    Terminator::Branch {
                        cond: Operand::Var(cv),
                        ..
                    },
                ) = (taken, &body.block(*block).term)
                {
                    // Find the defining comparison for cv.
                    if let Some((op, a, b)) = find_defining_bin(body, *block, *cv) {
                        let eff_op = if *is_then { op } else { negate_binop(op) };
                        if let Some(comp) = CompOp::from_binop(eff_op) {
                            // Check if any predicate matches this comparison.
                            for (i, pred) in prec.predicates.iter().enumerate() {
                                if predicate_matches_comparison(pred, comp, a, b) {
                                    next.values[i] = Some(true);
                                } else if predicate_matches_comparison(pred, comp.negate(), a, b) {
                                    next.values[i] = Some(false);
                                }
                            }
                        }
                    }
                }
                vec![next]
            }
            Edge::Exit(_) => vec![next],
        }
    }

    fn merge(
        &self,
        new: &PredState,
        reached: &PredState,
        _prec: &PredPrec,
    ) -> MergeResult<PredState> {
        // merge_join: join states at the same location.
        if new.at == reached.at {
            let joined = new.join(reached);
            if joined.values != reached.values {
                MergeResult::Joined(joined)
            } else {
                MergeResult::Sep
            }
        } else {
            MergeResult::Sep
        }
    }
}

/// Try to evaluate a predicate after an assignment v := rv.
fn evaluate_predicate_after_assign(
    pred: &Predicate,
    v: VarId,
    rv: &Rvalue,
    state: &PredState,
    prec: &PredPrec,
) -> Option<bool> {
    // Simple case: v := const
    if let Rvalue::Use(Operand::Const(Const::Int(n))) = rv {
        let n = *n as i64;
        // Substitute the constant for v in the predicate and evaluate.
        let lhs_val = match &pred.lhs {
            PredicateOperand::Var(x) if *x == v => Some(n),
            PredicateOperand::Var(x) => get_known_value(prec, state, *x),
            PredicateOperand::Const(c) => Some(*c),
        };
        let rhs_val = match &pred.rhs {
            PredicateOperand::Var(x) if *x == v => Some(n),
            PredicateOperand::Var(x) => get_known_value(prec, state, *x),
            PredicateOperand::Const(c) => Some(*c),
        };
        if let (Some(l), Some(r)) = (lhs_val, rhs_val) {
            return Some(eval_comp(pred.op, l, r));
        }
    }
    None // Unknown
}

fn eval_comp(op: CompOp, a: i64, b: i64) -> bool {
    match op {
        CompOp::Lt => a < b,
        CompOp::Le => a <= b,
        CompOp::Gt => a > b,
        CompOp::Ge => a >= b,
        CompOp::Eq => a == b,
        CompOp::Ne => a != b,
    }
}

/// Get the known constant value of a variable from the predicate state.
fn get_known_value(prec: &PredPrec, state: &PredState, v: VarId) -> Option<i64> {
    for (i, pred) in prec.predicates.iter().enumerate() {
        if state.values.get(i) == Some(&Some(true)) && pred.op == CompOp::Eq {
            if let (PredicateOperand::Var(x), PredicateOperand::Const(c)) = (&pred.lhs, &pred.rhs) {
                if *x == v {
                    return Some(*c);
                }
            }
        }
    }
    None
}

fn predicate_matches_comparison(pred: &Predicate, comp: CompOp, a: &Operand, b: &Operand) -> bool {
    let lhs_matches = match (&pred.lhs, a) {
        (PredicateOperand::Var(pv), Operand::Var(ov)) => *pv == *ov,
        (PredicateOperand::Const(pc), Operand::Const(Const::Int(oc))) => *pc == *oc as i64,
        _ => false,
    };
    let rhs_matches = match (&pred.rhs, b) {
        (PredicateOperand::Var(pv), Operand::Var(ov)) => *pv == *ov,
        (PredicateOperand::Const(pc), Operand::Const(Const::Int(oc))) => *pc == *oc as i64,
        _ => false,
    };
    pred.op == comp && lhs_matches && rhs_matches
}

/// Extract predicates from interpolant formulas for CEGAR refinement.
/// Parses comparison atoms from the interpolant string.
pub fn predicates_from_interpolant(itp: &str) -> Vec<Predicate> {
    let atoms = crate::interpolation::extract_predicates_from_interpolant(itp);
    let mut preds = Vec::new();
    for atom in &atoms {
        if let Some(pred) = parse_predicate_atom(atom) {
            preds.push(pred);
        }
    }
    preds
}

/// Parse an SMT-LIB2 atom like `(< v0 5)` into a Predicate.
fn parse_predicate_atom(atom: &str) -> Option<Predicate> {
    let atom = atom.trim();
    if !atom.starts_with('(') || !atom.ends_with(')') {
        return None;
    }
    let inner = &atom[1..atom.len() - 1];
    let parts: Vec<&str> = inner.split_whitespace().collect();
    if parts.len() != 3 {
        return None;
    }

    let op = match parts[0] {
        "<" => CompOp::Lt,
        "<=" => CompOp::Le,
        ">" => CompOp::Gt,
        ">=" => CompOp::Ge,
        "=" => CompOp::Eq,
        "distinct" => CompOp::Ne,
        _ => return None,
    };

    let lhs = parse_predicate_operand(parts[1])?;
    let rhs = parse_predicate_operand(parts[2])?;

    Some(Predicate { lhs, op, rhs })
}

fn parse_predicate_operand(s: &str) -> Option<PredicateOperand> {
    if let Some(rest) = s.strip_prefix('v') {
        let num: u32 = rest.parse().ok()?;
        Some(PredicateOperand::Var(VarId(num)))
    } else if let Ok(n) = s.parse::<i64>() {
        Some(PredicateOperand::Const(n))
    } else {
        None
    }
}
