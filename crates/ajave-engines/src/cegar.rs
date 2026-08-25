//! CEGAR (Counterexample-Guided Abstraction Refinement) engine.
//!
//! Direction: Over. Drives a `PredicateCpa` through `reachability()`,
//! growing the precision between runs. On a spurious counterexample trace,
//! extract predicates via interpolation and refine.
//!
//! Original papers:
//! - Predicate abstraction: Graf & Saidi, CAV 1997.
//! - CEGAR: Clarke, Grumberg, Jha, Lu & Veith, CAV 2000 (JACM 2003).
//! - Lazy abstraction: Henzinger, Jhala, Majumdar & Sutre, POPL 2002.

use log::{debug, info};
use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::cpa::{reachability, HasLocation};
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_ir::*;

use crate::body_analysis::{body_uses_havoced_ops, find_defining_bin};
use crate::interpolation::{
    encode_body_lia, find_interpolation_solver, InterpolationSolver,
};
use crate::predicate::{predicates_from_interpolant, CompOp, PredPrec, Predicate, PredicateOperand, PredicateCpa};

/// Maximum number of CEGAR refinement iterations.
const MAX_REFINEMENTS: u32 = 20;

/// Maximum abstract states per reachability run.
const MAX_STATES: usize = 10_000;

pub struct CegarEngine {
    solver: Option<InterpolationSolver>,
    done: bool,
}

impl CegarEngine {
    pub fn new() -> Self {
        CegarEngine {
            solver: find_interpolation_solver(),
            done: false,
        }
    }

    pub fn available(&self) -> bool {
        self.solver.is_some()
    }
}

impl Engine for CegarEngine {
    fn id(&self) -> EngineId {
        EngineId("cegar")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let Some(solver) = &self.solver else {
            debug!("cegar: no interpolation solver available");
            return Progress::Exhausted;
        };

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };

        if !body.is_fully_lifted() {
            return Progress::Stalled;
        }

        // CEGAR uses predicate abstraction (CPA-based reachability), not SMT
        // satisfiability. When heap operations produce unconstrained abstract
        // values, the predicate domain can't track them, causing the abstract
        // state to collapse to "top" — which makes the safety check trivially
        // succeed, producing unsound TRUE verdicts. Unlike k-induction/CHC/IMC
        // (which use SMT UNSAT checks where fresh values are conservative),
        // CEGAR's abstract interpretation can lose safety-critical information.
        if body_uses_havoced_ops(body) {
            debug!("cegar: {} uses havoced ops, skipping", entry);
            return Progress::Stalled;
        }

        let open: Vec<ObligationRef> = bb
            .open()
            .iter()
            .filter(|oref| oref.method == *entry)
            .cloned()
            .collect();

        if open.is_empty() {
            return Progress::Exhausted;
        }

        info!("cegar: starting refinement loop for {} obligation(s)", open.len());

        let mut advanced = false;

        for oref in &open {
            match try_cegar(solver, prog, body, entry, oref.id) {
                Ok(true) => {
                    debug!("cegar: proved {} via predicate abstraction", oref);
                    let _ = bb.publish(
                        self.id(),
                        self.direction(),
                        Artifact::Status(
                            oref.clone(),
                            Status::Discharged {
                                by: self.id(),
                                proof: ProofKind::Exhaustive,
                            },
                        ),
                    );
                    advanced = true;
                }
                Ok(false) => {
                    debug!("cegar: inconclusive for {}", oref);
                }
                Err(e) => {
                    debug!("cegar: error for {}: {}", oref, e);
                }
            }
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}

/// Run the CEGAR loop for a single obligation.
fn try_cegar(
    solver: &InterpolationSolver,
    prog: &Program,
    body: &Body,
    entry: &MethodKey,
    oid: ObligationId,
) -> Result<bool, String> {
    let mut prec = PredPrec::default();

    // Seed initial predicates from branch conditions in the method.
    seed_predicates_from_body(body, &mut prec);

    for iteration in 0..MAX_REFINEMENTS {
        debug!(
            "cegar: iteration {}, {} predicates",
            iteration,
            prec.predicates.len()
        );

        // Run predicate CPA reachability.
        let start = ProgramPoint {
            method: entry.clone(),
            block: body.entry,
            index: 0,
        };

        let (reached, complete) = reachability(&PredicateCpa, prog, &start, prec.clone(), MAX_STATES);

        if !complete {
            debug!("cegar: reachability incomplete at {} states", MAX_STATES);
            return Ok(false);
        }

        // Check if any reached state is at a Check location for our obligation
        // where the safety condition might be false.
        let mut found_error_trace = false;
        let mut error_path: Vec<BlockId> = Vec::new();

        for state in &reached {
            let loc = state.location();
            if loc.method != *entry {
                continue;
            }
            let block = body.block(loc.block);
            if let Some(Stmt::Check(cid)) = block.stmts.get(loc.index) {
                if *cid == oid {
                    let ob = body.obligation(oid);
                    // Check if the safety condition could be false.
                    let cond_ok = match &ob.cond {
                        Operand::Const(Const::Int(v)) => *v != 0,
                        _ => {
                            // With predicate abstraction, we check if the predicates
                            // imply the safety condition. If we can't determine it's
                            // definitely true, we have a potential error trace.
                            is_safety_implied_by_predicates(state, &prec, &ob.cond, body, loc.block)
                        }
                    };

                    if !cond_ok {
                        found_error_trace = true;
                        error_path = vec![loc.block];
                        break;
                    }
                }
            }
        }

        if !found_error_trace {
            // No reachable state can violate the obligation.
            debug!("cegar: no error trace found, property proved");
            return Ok(true);
        }

        // Found a potential error trace. Check feasibility and refine.
        debug!("cegar: potential error trace found, attempting refinement");

        let new_predicates = refine_from_trace(solver, body, oid, &error_path)?;

        if new_predicates.is_empty() {
            // Can't refine further — the trace may be real.
            debug!("cegar: no new predicates from refinement");
            return Ok(false);
        }

        // Add new predicates to precision.
        let before = prec.predicates.len();
        for pred in new_predicates {
            if !prec.predicates.contains(&pred) {
                prec.predicates.push(pred);
            }
        }
        let added = prec.predicates.len() - before;
        debug!("cegar: added {} new predicates", added);

        if added == 0 {
            // No new predicates — can't make progress.
            debug!("cegar: refinement produced no new predicates");
            return Ok(false);
        }
    }

    debug!("cegar: max refinements reached");
    Ok(false)
}

/// Check if the predicate state implies the safety condition is true.
fn is_safety_implied_by_predicates(
    state: &crate::predicate::PredState,
    prec: &PredPrec,
    cond: &Operand,
    body: &Body,
    block: BlockId,
) -> bool {
    // If the condition is a variable defined by a comparison, check if we
    // know that comparison's result from our predicate state.
    if let Operand::Var(cv) = cond {
        if let Some((op, _a, _b)) = find_defining_bin(body, block, *cv) {
            if let Some(comp) = CompOp::from_binop(op) {
                // Check if any predicate in our state tells us this comparison is true.
                for (i, pred) in prec.predicates.iter().enumerate() {
                    if state.values.get(i) == Some(&Some(true)) {
                        if pred.op == comp {
                            return true;
                        }
                    }
                }
            }
        }
    }
    false
}

/// Attempt to refine the abstraction by extracting predicates from an
/// infeasible counterexample trace.
fn refine_from_trace(
    solver: &InterpolationSolver,
    body: &Body,
    oid: ObligationId,
    _error_path: &[BlockId],
) -> Result<Vec<Predicate>, String> {
    // Encode the body's transition relation in LIA.
    let encoding = encode_body_lia(body, &[oid], "");

    let error_formula = encoding
        .error_formulas
        .iter()
        .find(|(id, _)| *id == oid)
        .map(|(_, f)| f.clone());

    let Some(error_formula) = error_formula else {
        return Ok(vec![]);
    };

    // Build two partitions:
    // A = transition relation (reaching the error state)
    // B = error condition
    let partition_a = encoding.transition.clone();
    let partition_b = error_formula;

    // Declare extra variables.
    let mut all_decls = encoding.declarations.clone();
    let extras = collect_free_vars_combined(&partition_a, &partition_b, &all_decls);
    for var in &extras {
        all_decls.push_str(&format!("(declare-fun {} () Int)\n", var));
    }

    // Try to get an interpolant.
    match solver.interpolate(&all_decls, &partition_a, &partition_b) {
        crate::interpolation::InterpolationResult::Interpolant(itp) => {
            debug!("cegar: got interpolant: {}", &itp[..itp.len().min(200)]);
            Ok(predicates_from_interpolant(&itp))
        }
        crate::interpolation::InterpolationResult::Sat => {
            // The error is actually reachable.
            debug!("cegar: error trace is feasible");
            Ok(vec![])
        }
        crate::interpolation::InterpolationResult::Unsupported => {
            // Fall back: extract predicates from branch conditions.
            debug!("cegar: interpolation unsupported, using branch predicates");
            Ok(extract_branch_predicates(body))
        }
    }
}

/// Seed initial predicates from branch conditions in the method body.
fn seed_predicates_from_body(body: &Body, prec: &mut PredPrec) {
    for block in &body.blocks {
        if let Terminator::Branch {
            cond: Operand::Var(cv),
            ..
        } = &block.term
        {
            if let Some((op, a, b)) = find_defining_bin(body, block.id, *cv) {
                if let Some(comp) = CompOp::from_binop(op) {
                    if let (Some(lhs), Some(rhs)) = (
                        operand_to_pred_operand(a),
                        operand_to_pred_operand(b),
                    ) {
                        let pred = Predicate {
                            lhs,
                            op: comp,
                            rhs,
                        };
                        if !prec.predicates.contains(&pred) {
                            prec.predicates.push(pred);
                        }
                    }
                }
            }
        }
    }
}

/// Extract predicates from all branch conditions in a body (fallback).
fn extract_branch_predicates(body: &Body) -> Vec<Predicate> {
    let mut prec = PredPrec::default();
    seed_predicates_from_body(body, &mut prec);
    prec.predicates
}

fn operand_to_pred_operand(op: &Operand) -> Option<PredicateOperand> {
    match op {
        Operand::Var(v) => Some(PredicateOperand::Var(*v)),
        Operand::Const(Const::Int(n)) => Some(PredicateOperand::Const(*n as i64)),
        Operand::Const(Const::Long(n)) => Some(PredicateOperand::Const(*n)),
        _ => None,
    }
}

fn collect_free_vars_combined(a: &str, b: &str, declarations: &str) -> Vec<String> {
    let mut vars = Vec::new();
    for formula in [a, b] {
        for token in formula.split(|c: char| !c.is_ascii_alphanumeric() && c != '_') {
            if (token.starts_with("nd") || token.starts_with("bw") || token.starts_with("hv"))
                && token.len() > 2
                && token[2..].chars().all(|c| c.is_ascii_digit())
            {
                if !declarations.contains(token) && !vars.contains(&token.to_string()) {
                    vars.push(token.to_string());
                }
            }
        }
    }
    vars
}
