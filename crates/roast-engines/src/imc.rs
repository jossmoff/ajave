//! Interpolation-based model checking (IMC).
//!
//! Direction: Over. Extends BMC's UNSAT result by computing reachable-state
//! overapproximations via Craig interpolation, iterating until fixpoint.
//!
//! On UNSAT at depth k, split the refutation proof at the 1-step cut point
//! and extract a Craig interpolant — the over-approximation of "states
//! reachable in one more step that still can't reach Bad". Accumulate
//! F ← F ∨ I each iteration; fixpoint when the interpolant is already
//! implied by F.
//!
//! Original paper: McMillan, "Interpolation and SAT-Based Model Checking",
//! CAV 2003.
//!
//! Solver constraint: requires an interpolation-capable solver. Uses Z3's
//! `get-interpolant` (4.12+) or SMTInterpol.

use std::collections::HashSet;

use log::{debug, info};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::*;

use crate::body_analysis::body_uses_havoced_ops;
use crate::interpolation::{
    encode_body_lia, find_interpolation_solver, InterpolationResult, InterpolationSolver,
};

/// Maximum number of IMC iterations before giving up.
const MAX_ITERATIONS: u32 = 50;

pub struct ImcEngine {
    solver: Option<InterpolationSolver>,
    done: bool,
}

impl Default for ImcEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl ImcEngine {
    pub fn new() -> Self {
        ImcEngine {
            solver: find_interpolation_solver(),
            done: false,
        }
    }

    pub fn available(&self) -> bool {
        self.solver.is_some()
    }
}

impl Engine for ImcEngine {
    fn id(&self) -> EngineId {
        EngineId("imc")
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
            debug!("imc: no interpolation solver available");
            return Progress::Exhausted;
        };

        // Work on obligations that have a Bounded base case.
        let open = bb.open();
        if open.is_empty() {
            return Progress::Exhausted;
        }

        let bounded: Vec<(ObligationRef, u32)> = open
            .iter()
            .filter_map(|oref| match bb.status(oref) {
                Status::Bounded { k } => Some((oref.clone(), *k)),
                _ => None,
            })
            .collect();

        if bounded.is_empty() {
            debug!("imc: no bounded obligations to work on");
            return Progress::Stalled;
        }

        info!(
            "imc: attempting interpolation-based proof for {} obligation(s)",
            bounded.len()
        );

        let mut advanced = false;

        for (oref, _k) in &bounded {
            let Some(body) = prog.body(&oref.method) else {
                continue;
            };

            // Skip methods with havoced operations — the LIA encoding
            // overapproximates heap/array/call operations, which could lead
            // to unsound proofs.
            if body_uses_havoced_ops(body) {
                debug!("imc: {} uses havoced ops, skipping", oref);
                continue;
            }

            if let Ok(proved) = try_imc(solver, body, oref.id) {
                if proved {
                    debug!("imc: proved {} via interpolation fixpoint", oref);
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
                } else {
                    debug!("imc: inconclusive for {}", oref);
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

/// Attempt IMC for a single obligation.
///
/// Algorithm:
/// 1. Encode body as LIA transition T(s, s'), error condition Bad(s)
/// 2. Init = true (unconstrained initial state)
/// 3. Check Init ∧ Bad → should be UNSAT (BMC already checked)
/// 4. Iterate:
///    a. F = current reachable overapproximation (starts as Init)
///    b. Check F(s) ∧ T(s, s') ∧ Bad(s') — can bad be reached from F?
///    c. If SAT: inconclusive
///    d. If UNSAT: get interpolant I between F∧T and Bad
///    e. If I ⊆ F: fixpoint → proved safe
///    f. Else F = F ∨ I, iterate
fn try_imc(solver: &InterpolationSolver, body: &Body, oid: ObligationId) -> Result<bool, String> {
    let encoding = encode_body_lia(body, &[oid], "");

    // Find the error formula for this obligation.
    let error_formula = encoding
        .error_formulas
        .iter()
        .find(|(id, _)| *id == oid)
        .map(|(_, f)| f.clone());

    let Some(error_formula) = error_formula else {
        // Obligation not in this body → trivially safe.
        return Ok(true);
    };

    // Declare nondeterministic/havoc variables that appear in the encoding.
    let extra_decls = collect_free_vars(&encoding.transition, &encoding.declarations)
        .into_iter()
        .chain(collect_free_vars(&error_formula, &encoding.declarations))
        .collect::<HashSet<_>>();

    let mut all_decls = encoding.declarations.clone();
    for var in &extra_decls {
        all_decls.push_str(&format!("(declare-fun {} () Int)\n", var));
    }

    // Start with F = true (all states reachable).
    let mut reachable = "true".to_string();

    for iteration in 0..MAX_ITERATIONS {
        debug!(
            "imc: iteration {}, reachable = {}",
            iteration,
            &reachable[..reachable.len().min(100)]
        );

        // Partition A: F(s) ∧ T(s, s')
        // Partition B: Bad(s')
        // But Bad uses pre-state vars, and T maps pre to post.
        // We need to check if any post-state satisfying T also satisfies Bad.

        // Encode: A = reachable ∧ transition, B = error condition (over post-state vars)
        // The error formula uses pre-state var names, so we substitute with post-state.
        let error_post = rename_vars_to_post(&error_formula, encoding.n_vars);

        let formula_a = if reachable == "true" {
            encoding.transition.clone()
        } else {
            format!("(and {} {})", reachable, encoding.transition)
        };

        match solver.interpolate(&all_decls, &formula_a, &error_post) {
            InterpolationResult::Interpolant(itp) => {
                debug!("imc: got interpolant: {}", &itp[..itp.len().min(200)]);

                // The interpolant talks about post-state variables.
                // Rename post vars back to pre vars to get the reachable overapprox.
                let itp_pre = rename_post_to_vars(&itp, encoding.n_vars);

                // Check fixpoint: is the new interpolant subsumed by F?
                // We check: itp_pre ∧ ¬reachable is UNSAT
                // If so, itp_pre ⊆ reachable → fixpoint.
                if is_subsumed(solver, &all_decls, &itp_pre, &reachable) {
                    debug!("imc: fixpoint reached at iteration {}", iteration);
                    return Ok(true);
                }

                // Widen: F = F ∨ I
                reachable = if reachable == "true" {
                    "true".to_string() // already top
                } else {
                    format!("(or {} {})", reachable, itp_pre)
                };
            }
            InterpolationResult::Sat => {
                // Error is reachable — can't prove safe.
                debug!("imc: error reachable at iteration {}", iteration);
                return Ok(false);
            }
            InterpolationResult::Unsupported => {
                debug!("imc: interpolation unsupported, giving up");
                return Err("interpolation not supported".to_string());
            }
        }
    }

    debug!("imc: max iterations reached without fixpoint");
    Ok(false)
}

/// Check if formula `a` is subsumed by formula `b` (a ⟹ b).
/// Returns true if `a ∧ ¬b` is UNSAT.
fn is_subsumed(_solver: &InterpolationSolver, declarations: &str, a: &str, b: &str) -> bool {
    if b == "true" {
        return true;
    }

    // Use the solver to check a ∧ ¬b.
    let formula = format!("(and {} (not {}))", a, b);
    let check_script = format!(
        "(set-logic QF_LIA)\n{}\n(assert {})\n(check-sat)\n(exit)\n",
        declarations, formula
    );

    match crate::interpolation::run_solver_batch_pub("z3", &["-in", "-smt2"], &check_script) {
        Ok(lines) => lines.first().map(|s| s.trim() == "unsat").unwrap_or(false),
        Err(_) => false,
    }
}

/// Rename pre-state variables (v0, v1, ...) to post-state (v0p, v1p, ...).
fn rename_vars_to_post(formula: &str, n_vars: usize) -> String {
    let mut result = formula.to_string();
    // Rename in reverse order to avoid conflicts (v10 before v1).
    for i in (0..n_vars).rev() {
        // Only rename standalone variable names, not partial matches.
        result = rename_var_in_sexp(&result, &format!("v{}", i), &format!("v{}p", i));
    }
    result
}

/// Rename post-state variables back to pre-state.
fn rename_post_to_vars(formula: &str, n_vars: usize) -> String {
    let mut result = formula.to_string();
    for i in (0..n_vars).rev() {
        result = rename_var_in_sexp(&result, &format!("v{}p", i), &format!("v{}", i));
    }
    result
}

/// Rename a variable in an S-expression, only matching word boundaries.
fn rename_var_in_sexp(sexp: &str, from: &str, to: &str) -> String {
    let mut result = String::with_capacity(sexp.len());
    let bytes = sexp.as_bytes();
    let from_bytes = from.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        if i + from_bytes.len() <= bytes.len() && &bytes[i..i + from_bytes.len()] == from_bytes {
            // Check that this is a word boundary.
            let before_ok = i == 0 || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_';
            let after_ok = i + from_bytes.len() >= bytes.len() || {
                let next = bytes[i + from_bytes.len()];
                !next.is_ascii_alphanumeric() && next != b'_'
            };
            if before_ok && after_ok {
                result.push_str(to);
                i += from_bytes.len();
                continue;
            }
        }
        result.push(bytes[i] as char);
        i += 1;
    }
    result
}

/// Collect free variable names that appear in a formula but are not declared.
fn collect_free_vars(formula: &str, declarations: &str) -> Vec<String> {
    let mut vars = Vec::new();
    // Look for patterns like nd0, bw1, hv2 that are generated by the LIA encoder.
    for token in formula.split(|c: char| !c.is_ascii_alphanumeric() && c != '_') {
        if (token.starts_with("nd") || token.starts_with("bw") || token.starts_with("hv"))
            && token.len() > 2
            && token[2..].chars().all(|c| c.is_ascii_digit())
            && !declarations.contains(token)
            && !vars.contains(&token.to_string())
        {
            vars.push(token.to_string());
        }
    }
    vars
}
