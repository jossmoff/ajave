//! CHC (Constrained Horn Clauses) engine.
//!
//! Translates the program to a set of Horn clauses in SMT-LIB2 CHC format
//! and shells out to a solver (Z3 in CHC mode, or Eldarica/Golem).
//! Direction: Over.
//!
//! One relation per block: `block_N(v0, v1, ..., vK)` where vi are all
//! int-typed variables in the method. One clause per CFG edge encodes the
//! transfer semantics. The safety property becomes a query: is the error
//! state reachable?
//!
//! Original papers:
//! - Grebenshchikov et al., "Synthesizing Software Verifiers from Proof
//!   Rules", PLDI 2012
//! - Bjørner et al., "Horn Clause Solvers for Program Verification", 2015

use std::collections::HashMap;
use std::io::Write as IoWrite;
use std::process::{Command, Stdio};

use log::{debug, info, warn};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::*;

use crate::body_analysis::body_uses_havoced_ops;
use crate::smt_text::{self, BitvectorTheory, SmtTheory};

pub struct ChcEngine {
    solver_binary: String,
    done: bool,
}

impl ChcEngine {
    pub fn new() -> Self {
        // Try to find z3 on PATH.
        let binary = std::env::var("ROAST_CHC_SOLVER").unwrap_or_else(|_| "z3".to_string());
        ChcEngine {
            solver_binary: binary,
            done: false,
        }
    }

    /// Check if the CHC solver binary is available.
    pub fn available(&self) -> bool {
        Command::new(&self.solver_binary)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok()
    }
}

impl Engine for ChcEngine {
    fn id(&self) -> EngineId {
        EngineId("chc")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let open = bb.open();
        if open.is_empty() {
            return Progress::Exhausted;
        }

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };

        if !body.is_fully_lifted() {
            return Progress::Stalled;
        }

        // Skip methods with heap/array/call operations — the CHC encoding
        // havoces these, so an "unsat" result would be unsound.
        if body_uses_havoced_ops(body) {
            debug!("chc: {} uses havoced ops, skipping", entry);
            return Progress::Stalled;
        }

        // Collect obligations we want to check.
        let obs: Vec<ObligationId> = open
            .iter()
            .filter(|oref| oref.method == *entry)
            .map(|oref| oref.id)
            .collect();

        if obs.is_empty() {
            return Progress::Exhausted;
        }

        info!("chc: encoding {} obligation(s) for {:?}", obs.len(), entry);

        // Generate CHC encoding.
        let smt2 = encode_chc(body, &obs);
        debug!("chc: generated {} bytes of CHC encoding", smt2.len());

        // Run solver.
        let mut advanced = false;
        match run_chc_solver(&self.solver_binary, &smt2, &obs) {
            Ok(results) => {
                for (oid, safe) in results {
                    if safe {
                        let oref = ObligationRef {
                            method: entry.clone(),
                            id: oid,
                        };
                        debug!("chc: discharged {}", oref);
                        let _ = bb.publish(
                            self.id(),
                            self.direction(),
                            Artifact::Status(
                                oref,
                                Status::Discharged {
                                    by: self.id(),
                                    proof: ProofKind::Exhaustive,
                                },
                            ),
                        );
                        advanced = true;
                    }
                }
            }
            Err(e) => {
                warn!("chc: solver failed: {}", e);
            }
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}

/// Width of a type in bits.
fn width_of(ty: &Ty) -> u32 {
    match ty {
        Ty::Long | Ty::Double => 64,
        _ => 32,
    }
}

/// Encode a method body as CHC in SMT-LIB2 format.
fn encode_chc(body: &Body, obligations: &[ObligationId]) -> String {
    let mut out = String::new();
    out.push_str("(set-logic HORN)\n");

    // Collect all integer-typed variables as the relation's signature.
    let var_indices: Vec<(usize, u32)> = body
        .vars
        .iter()
        .enumerate()
        .map(|(i, vi)| (i, width_of(&vi.ty)))
        .collect();

    let n_vars = var_indices.len();

    // Declare a relation for each block.
    for block in &body.blocks {
        let sig: String = var_indices
            .iter()
            .map(|(_, w)| format!("(_ BitVec {})", w))
            .collect::<Vec<_>>()
            .join(" ");
        out.push_str(&format!(
            "(declare-fun block_{} ({}) Bool)\n",
            block.id.0, sig
        ));
    }

    // Error relation (no arguments).
    out.push_str("(declare-fun error () Bool)\n");

    // Helper: variable names for source and destination.
    let src_vars: Vec<String> = (0..n_vars).map(|i| format!("v{}", i)).collect();
    let dst_vars: Vec<String> = (0..n_vars).map(|i| format!("v{}'", i)).collect();

    // Quantifier prefix for source variables.
    let forall_src: String = var_indices
        .iter()
        .enumerate()
        .map(|(i, (_, w))| format!("(v{} (_ BitVec {}))", i, w))
        .collect::<Vec<_>>()
        .join(" ");
    let forall_both: String = {
        let src = var_indices
            .iter()
            .enumerate()
            .map(|(i, (_, w))| format!("(v{} (_ BitVec {}))", i, w));
        let dst = var_indices
            .iter()
            .enumerate()
            .map(|(i, (_, w))| format!("(v{}' (_ BitVec {}))", i, w));
        src.chain(dst).collect::<Vec<_>>().join(" ")
    };

    // Block application with source vars.
    let block_app = |bid: u32| -> String {
        let args = src_vars.join(" ");
        format!("(block_{} {})", bid, args)
    };
    let block_app_dst = |bid: u32| -> String {
        let args = dst_vars.join(" ");
        format!("(block_{} {})", bid, args)
    };

    // Entry rule: initial state enters the entry block.
    // All variables are unconstrained (forall-quantified).
    out.push_str(&format!(
        "(assert (forall ({}) {}))\n",
        forall_src,
        block_app(body.entry.0)
    ));

    // For each block, encode its statements as constraints and emit
    // transition rules to successor blocks.
    for block in &body.blocks {
        // Build constraint list from statements.
        let mut constraints: Vec<String> = Vec::new();
        let mut var_map: HashMap<usize, String> = HashMap::new();

        // Initially, dst vars equal src vars.
        for i in 0..n_vars {
            var_map.insert(i, format!("v{}", i));
        }

        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(vid, rv) => {
                    let expr = smt_text::encode_rvalue(&BitvectorTheory, rv, &var_map);
                    var_map.insert(vid.0 as usize, expr);
                }
                Stmt::Assume(op) => {
                    let expr = smt_text::encode_operand(&BitvectorTheory, op, &var_map);
                    constraints.push(BitvectorTheory.encode_nonzero(&expr));
                }
                Stmt::Check(oid) => {
                    if obligations.contains(oid) {
                        // Emit error rule: if this block is reachable and
                        // the safety condition is zero, error is reachable.
                        let ob = body.obligation(*oid);
                        let cond_expr = smt_text::encode_operand(&BitvectorTheory, &ob.cond, &var_map);
                        let mut error_conds = constraints.clone();
                        error_conds.push(BitvectorTheory.encode_is_zero(&cond_expr));
                        error_conds.push(block_app(block.id.0));

                        let body_expr = if error_conds.len() == 1 {
                            error_conds[0].clone()
                        } else {
                            format!("(and {})", error_conds.join(" "))
                        };

                        out.push_str(&format!(
                            "(assert (forall ({}) (=> {} error)))\n",
                            forall_src, body_expr
                        ));
                    }
                }
                _ => {}
            }
        }

        // Successor edges: dst vars get the final values from the block.
        let mut assign_constraints: Vec<String> = Vec::new();
        for i in 0..n_vars {
            let val = var_map.get(&i).unwrap();
            if *val != format!("v{}'", i) {
                assign_constraints.push(format!("(= v{}' {})", i, val));
            }
        }

        let mk_trans = |target_bid: u32, extra_conds: &[String]| -> String {
            let mut all_conds = constraints.clone();
            all_conds.extend_from_slice(extra_conds);
            all_conds.extend(assign_constraints.iter().cloned());
            all_conds.push(block_app(block.id.0));

            let body_expr = if all_conds.is_empty() {
                block_app(block.id.0)
            } else {
                format!("(and {})", all_conds.join(" "))
            };

            format!(
                "(assert (forall ({}) (=> {} {})))\n",
                forall_both, body_expr, block_app_dst(target_bid)
            )
        };

        match &block.term {
            Terminator::Goto(t) => {
                out.push_str(&mk_trans(t.0, &[]));
            }
            Terminator::Branch { cond, then_, else_ } => {
                let cond_expr = smt_text::encode_operand(&BitvectorTheory, cond, &var_map);
                let nz = BitvectorTheory.encode_nonzero(&cond_expr);
                let z = BitvectorTheory.encode_is_zero(&cond_expr);
                out.push_str(&mk_trans(then_.0, &[nz]));
                out.push_str(&mk_trans(else_.0, &[z]));
            }
            Terminator::Switch { value, cases, default } => {
                let val_expr = smt_text::encode_operand(&BitvectorTheory, value, &var_map);
                let mut neg_cases = Vec::new();
                for (cv, target) in cases {
                    let cv_encoded = BitvectorTheory.encode_int(*cv);
                    let eq = format!("(= {} {})", val_expr, cv_encoded);
                    out.push_str(&mk_trans(target.0, &[eq.clone()]));
                    neg_cases.push(format!("(not {})", eq));
                }
                out.push_str(&mk_trans(default.0, &neg_cases));
            }
            _ => {}
        }
    }

    // Query: is error reachable?
    out.push_str("(assert (not error))\n");
    out.push_str("(check-sat)\n");

    out
}


/// Run the CHC solver and parse results.
fn run_chc_solver(
    binary: &str,
    smt2: &str,
    obligations: &[ObligationId],
) -> Result<Vec<(ObligationId, bool)>, String> {
    let mut child = Command::new(binary)
        .args(["-in", "-smt2"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| format!("failed to spawn {}: {}", binary, e))?;

    {
        let stdin = child.stdin.as_mut().ok_or("no stdin")?;
        stdin
            .write_all(smt2.as_bytes())
            .map_err(|e| format!("write failed: {}", e))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("wait failed: {}", e))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let result_line = stdout.trim();

    debug!("chc: solver returned: {}", result_line);

    // "unsat" means error is unreachable → all obligations are safe.
    // "sat" means a counterexample exists (but we don't extract witnesses here).
    match result_line {
        "unsat" => {
            // All obligations are safe (single error relation covers all).
            Ok(obligations.iter().map(|oid| (*oid, true)).collect())
        }
        _ => Ok(vec![]),
    }
}
