//! Interpolation support for IMC and CEGAR.
//!
//! Shells out to an interpolation-capable solver (Z3 or SMTInterpol) in batch
//! mode and returns Craig interpolants for partitioned formulas. Uses QF_LIA
//! (linear integer arithmetic) since bitvector interpolation is not widely
//! supported.
//!
//! Both IMC and CEGAR depend on this module.

use std::io::Write as IoWrite;
use std::process::{Command, Stdio};

use log::{debug, trace};

use crate::smt_text::{self, LiaTheory, SmtTheory};

/// Result of an interpolation query.
#[derive(Debug)]
pub enum InterpolationResult {
    /// The conjunction is UNSAT and an interpolant was computed.
    Interpolant(String),
    /// The conjunction is SAT (no interpolant).
    Sat,
    /// The solver doesn't support interpolation or returned an error.
    Unsupported,
}

/// Find an interpolation-capable solver binary.
/// Prefers SMTInterpol (java -jar) if available, falls back to Z3.
pub fn find_interpolation_solver() -> Option<InterpolationSolver> {
    // Try Z3 first (more likely to be installed).
    if let Ok(status) = Command::new("z3")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
    {
        if status.success() {
            return Some(InterpolationSolver::Z3("z3".to_string()));
        }
    }
    None
}

#[derive(Clone, Debug)]
pub enum InterpolationSolver {
    Z3(String),
    SmtInterpol(String), // path to JAR
}

impl InterpolationSolver {
    /// Compute a Craig interpolant for two partitions A and B.
    ///
    /// Given that A ∧ B is UNSAT, returns I such that A ⟹ I and I ∧ B is UNSAT.
    /// All formulas use QF_LIA (integer arithmetic).
    pub fn interpolate(
        &self,
        declarations: &str,
        formula_a: &str,
        formula_b: &str,
    ) -> InterpolationResult {
        match self {
            InterpolationSolver::Z3(binary) => {
                interpolate_z3(binary, declarations, formula_a, formula_b)
            }
            InterpolationSolver::SmtInterpol(jar) => {
                interpolate_smtinterpol(jar, declarations, formula_a, formula_b)
            }
        }
    }

    /// Compute a sequence of interpolants for a path formula.
    ///
    /// Given partitions [P0, P1, ..., Pn] such that their conjunction is UNSAT,
    /// returns [I1, ..., In] where:
    ///   P0 ⟹ I1
    ///   I_k ∧ P_k ⟹ I_{k+1}
    ///   I_n ∧ P_n is UNSAT
    pub fn sequence_interpolants(
        &self,
        declarations: &str,
        partitions: &[String],
    ) -> Result<Vec<String>, String> {
        if partitions.len() < 2 {
            return Ok(vec![]);
        }

        let mut interpolants = Vec::new();
        for k in 1..partitions.len() {
            let prefix = if k == 1 {
                partitions[0].clone()
            } else {
                format!("(and {})", partitions[..k].join(" "))
            };
            let suffix = if k == partitions.len() - 1 {
                partitions[k].clone()
            } else {
                format!("(and {})", partitions[k..].join(" "))
            };

            match self.interpolate(declarations, &prefix, &suffix) {
                InterpolationResult::Interpolant(itp) => interpolants.push(itp),
                InterpolationResult::Sat => {
                    return Err("path formula is SAT at cut point".to_string())
                }
                InterpolationResult::Unsupported => {
                    return Err("interpolation not supported by solver".to_string())
                }
            }
        }
        Ok(interpolants)
    }
}

fn interpolate_z3(
    binary: &str,
    declarations: &str,
    formula_a: &str,
    formula_b: &str,
) -> InterpolationResult {
    // Z3 4.12+ supports (get-interpolant <name> <formula>).
    // The formula specifies what goes in partition A; everything else is B.
    let script = format!(
        "(set-logic QF_LIA)\n\
         {declarations}\n\
         (assert (! {formula_a} :named partA))\n\
         (assert (! {formula_b} :named partB))\n\
         (check-sat)\n\
         (get-interpolant itp partA)\n\
         (exit)\n"
    );

    trace!("interpolation script:\n{}", script);

    match run_solver_batch(binary, &["-in", "-smt2"], &script) {
        Ok(lines) => parse_interpolant_response(&lines),
        Err(e) => {
            debug!("z3 interpolation failed: {}", e);
            InterpolationResult::Unsupported
        }
    }
}

fn interpolate_smtinterpol(
    jar_path: &str,
    declarations: &str,
    formula_a: &str,
    formula_b: &str,
) -> InterpolationResult {
    let script = format!(
        "(set-option :produce-interpolants true)\n\
         (set-logic QF_LIA)\n\
         {declarations}\n\
         (assert (! {formula_a} :named partA))\n\
         (assert (! {formula_b} :named partB))\n\
         (check-sat)\n\
         (get-interpolants partA partB)\n\
         (exit)\n"
    );

    match run_solver_batch("java", &["-jar", jar_path], &script) {
        Ok(lines) => parse_interpolant_response(&lines),
        Err(e) => {
            debug!("smtinterpol interpolation failed: {}", e);
            InterpolationResult::Unsupported
        }
    }
}

/// Public wrapper for running a solver script in batch mode.
pub fn run_solver_batch_pub(
    binary: &str,
    args: &[&str],
    script: &str,
) -> Result<Vec<String>, String> {
    run_solver_batch(binary, args, script)
}

fn run_solver_batch(binary: &str, args: &[&str], script: &str) -> Result<Vec<String>, String> {
    let mut child = Command::new(binary)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn {}: {}", binary, e))?;

    {
        let stdin = child.stdin.as_mut().ok_or("no stdin")?;
        stdin
            .write_all(script.as_bytes())
            .map_err(|e| format!("write failed: {}", e))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("wait failed: {}", e))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    Ok(stdout.lines().map(|s| s.trim().to_string()).collect())
}

fn parse_interpolant_response(lines: &[String]) -> InterpolationResult {
    if lines.is_empty() {
        return InterpolationResult::Unsupported;
    }

    match lines[0].as_str() {
        "sat" => InterpolationResult::Sat,
        "unsat" => {
            // Look for the interpolant in subsequent lines.
            // Skip "unsat", any empty lines, and error/unsupported messages.
            for line in &lines[1..] {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    continue;
                }
                if trimmed == "unsupported"
                    || trimmed.starts_with("(error")
                    || trimmed.starts_with(";")
                {
                    debug!("interpolation unsupported: {}", trimmed);
                    return InterpolationResult::Unsupported;
                }
                // The interpolant is an S-expression (possibly multi-line).
                // For now handle single-line interpolants.
                return InterpolationResult::Interpolant(trimmed.to_string());
            }
            InterpolationResult::Unsupported
        }
        _ => {
            debug!("unexpected interpolation response: {}", lines[0]);
            InterpolationResult::Unsupported
        }
    }
}

/// Encode a method body's transition relation in QF_LIA format.
///
/// Returns (declarations, transition_formula, init_formula, error_formulas).
/// Variables are encoded as integers (not bitvectors) since interpolation
/// requires LIA.
pub fn encode_body_lia(
    body: &roast_ir::Body,
    obligations: &[roast_ir::ObligationId],
    prefix: &str,
) -> LiaEncoding {
    use roast_ir::*;

    let theory = LiaTheory::new(prefix);
    let n_vars = body.vars.len();

    // Variable declarations: pre-state and post-state.
    let mut decls = String::new();
    for i in 0..n_vars {
        decls.push_str(&format!("(declare-fun {prefix}v{i} () Int)\n"));
        decls.push_str(&format!("(declare-fun {prefix}v{i}p () Int)\n"));
    }

    // Build per-block transition clauses.
    let mut block_clauses: Vec<String> = Vec::new();
    let mut error_clauses: Vec<(ObligationId, String)> = Vec::new();

    for block in &body.blocks {
        let mut var_exprs: Vec<String> = (0..n_vars).map(|i| format!("{prefix}v{i}")).collect();
        let mut path_conds: Vec<String> = Vec::new();

        // Track whether this block is the entry block.
        let _is_entry = block.id == body.entry;

        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(vid, rv) => {
                    let expr = smt_text::encode_rvalue(&theory, rv, &var_exprs);
                    var_exprs[vid.0 as usize] = expr;
                }
                Stmt::Assume(op) => {
                    let expr = smt_text::encode_operand(&theory, op, &var_exprs);
                    path_conds.push(theory.encode_nonzero(&expr));
                }
                Stmt::Check(oid) => {
                    if obligations.contains(oid) {
                        let ob = body.obligation(*oid);
                        let cond_expr = smt_text::encode_operand(&theory, &ob.cond, &var_exprs);
                        let mut econds = path_conds.clone();
                        econds.push(theory.encode_is_zero(&cond_expr));
                        let error_cond = if econds.is_empty() {
                            "true".to_string()
                        } else if econds.len() == 1 {
                            econds[0].clone()
                        } else {
                            format!("(and {})", econds.join(" "))
                        };
                        error_clauses.push((*oid, error_cond));
                    }
                }
                _ => {}
            }
        }

        // Build successor transition clauses.
        let mk_assign = |var_exprs: &[String]| -> Vec<String> {
            var_exprs
                .iter()
                .enumerate()
                .filter_map(|(i, e)| {
                    let post = format!("{prefix}v{i}p");
                    if *e != post {
                        Some(format!("(= {} {})", post, e))
                    } else {
                        None
                    }
                })
                .collect()
        };

        match &block.term {
            Terminator::Goto(_) | Terminator::Return(_) | Terminator::Halt => {
                let mut conds = path_conds.clone();
                conds.extend(mk_assign(&var_exprs));
                if !conds.is_empty() {
                    let clause = if conds.len() == 1 {
                        conds[0].clone()
                    } else {
                        format!("(and {})", conds.join(" "))
                    };
                    block_clauses.push(clause);
                }
            }
            Terminator::Branch { cond, .. } => {
                let cond_expr = smt_text::encode_operand(&theory, cond, &var_exprs);
                let assigns = mk_assign(&var_exprs);

                // Then branch: condition is nonzero.
                let mut then_conds = path_conds.clone();
                then_conds.push(theory.encode_nonzero(&cond_expr));
                then_conds.extend(assigns.iter().cloned());
                if !then_conds.is_empty() {
                    block_clauses.push(format!("(and {})", then_conds.join(" ")));
                }

                // Else branch: condition is zero.
                let mut else_conds = path_conds.clone();
                else_conds.push(theory.encode_is_zero(&cond_expr));
                else_conds.extend(assigns);
                if !else_conds.is_empty() {
                    block_clauses.push(format!("(and {})", else_conds.join(" ")));
                }
            }
            Terminator::Switch {
                value,
                cases,
                default: _,
            } => {
                let val_expr = smt_text::encode_operand(&theory, value, &var_exprs);
                let assigns = mk_assign(&var_exprs);
                let mut neg_cases = Vec::new();

                for (cv, _) in cases {
                    let mut case_conds = path_conds.clone();
                    case_conds.push(format!("(= {} {})", val_expr, cv));
                    case_conds.extend(assigns.iter().cloned());
                    block_clauses.push(format!("(and {})", case_conds.join(" ")));
                    neg_cases.push(format!("(not (= {} {}))", val_expr, cv));
                }

                // Default case.
                let mut def_conds = path_conds.clone();
                def_conds.extend(neg_cases);
                def_conds.extend(assigns);
                if !def_conds.is_empty() {
                    block_clauses.push(format!("(and {})", def_conds.join(" ")));
                }
            }
            _ => {}
        }
    }

    // The transition relation is the disjunction of all block clauses.
    let transition = if block_clauses.is_empty() {
        "true".to_string()
    } else if block_clauses.len() == 1 {
        block_clauses[0].clone()
    } else {
        format!("(or {})", block_clauses.join(" "))
    };

    // Error formula: disjunction of all error clauses.
    let error_formulas: Vec<(ObligationId, String)> = error_clauses;

    LiaEncoding {
        declarations: decls,
        transition,
        error_formulas,
        n_vars,
    }
}

pub struct LiaEncoding {
    pub declarations: String,
    pub transition: String,
    pub error_formulas: Vec<(roast_ir::ObligationId, String)>,
    pub n_vars: usize,
}

/// Extract predicate atoms from an interpolant formula string.
///
/// Parses simple S-expression interpolants and extracts atomic comparisons
/// like `(< v0 5)`, `(= v1 v2)` etc. Used by CEGAR for predicate refinement.
pub fn extract_predicates_from_interpolant(itp: &str) -> Vec<String> {
    let mut predicates = Vec::new();
    extract_atoms(itp, &mut predicates);
    predicates
}

fn extract_atoms(expr: &str, out: &mut Vec<String>) {
    let expr = expr.trim();
    if expr.is_empty() {
        return;
    }

    // Check if this is an atomic comparison.
    if expr.starts_with('(') {
        let inner = &expr[1..expr.len().saturating_sub(1)];
        let op = inner.split_whitespace().next().unwrap_or("");
        match op {
            "<" | "<=" | ">" | ">=" | "=" => {
                out.push(expr.to_string());
                return;
            }
            "and" | "or" | "not" => {
                // Recurse into sub-expressions.
                let args = split_sexp_args(&inner[op.len()..]);
                for arg in args {
                    extract_atoms(&arg, out);
                }
                return;
            }
            _ => {}
        }
    }
    // Not a recognized form; treat the whole thing as a predicate if non-trivial.
    if expr != "true" && expr != "false" {
        out.push(expr.to_string());
    }
}

/// Split an S-expression argument list into individual sub-expressions.
fn split_sexp_args(s: &str) -> Vec<String> {
    let s = s.trim();
    let mut args = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    let bytes = s.as_bytes();

    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b' ' | b'\n' | b'\t' if depth == 0 => {
                let arg = s[start..i].trim();
                if !arg.is_empty() {
                    args.push(arg.to_string());
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    let arg = s[start..].trim();
    if !arg.is_empty() {
        args.push(arg.to_string());
    }
    args
}
