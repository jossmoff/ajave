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

use crate::smt_text::{self, LiaTheory};

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
        self.interpolate_profiled(declarations, formula_a, formula_b, None)
    }

    /// As `interpolate`, recording encoding size and solver time under
    /// `profile_as` when `--profile` is on.
    pub fn interpolate_profiled(
        &self,
        declarations: &str,
        formula_a: &str,
        formula_b: &str,
        profile_as: Option<(&str, &roast_core::smt_profile::ProfileHandle)>,
    ) -> InterpolationResult {
        let started = std::time::Instant::now();
        let result = match self {
            InterpolationSolver::Z3(binary) => {
                interpolate_z3(binary, declarations, formula_a, formula_b)
            }
            InterpolationSolver::SmtInterpol(jar) => {
                interpolate_smtinterpol(jar, declarations, formula_a, formula_b)
            }
        };
        if let Some((engine, handle)) = profile_as {
            let binary = match self {
                InterpolationSolver::Z3(b) => b.as_str(),
                InterpolationSolver::SmtInterpol(j) => j.as_str(),
            };
            // The partitions are what actually goes to the solver, so their
            // combined size is this query's encoding size.
            let approx_script = declarations.len() + formula_a.len() + formula_b.len();
            let script = " ".repeat(approx_script);
            roast_core::smt_profile::record_batch(
                &Some(handle.clone()),
                engine,
                binary,
                &script,
                std::time::Duration::ZERO,
                started.elapsed(),
                match result {
                    InterpolationResult::Sat => "sat",
                    InterpolationResult::Interpolant(_) => "unsat",
                    InterpolationResult::Unsupported => "unknown",
                },
            );
        }
        result
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

/// Run a whole SMT script through a fresh solver process.
///
/// The single choke point for every batch (non-incremental) solver call in the
/// interpolation-based engines, and therefore where `--profile` measures them.
/// `profile_as` names the engine the cost belongs to; `None` disables recording.
pub fn run_solver_batch_profiled(
    binary: &str,
    args: &[&str],
    script: &str,
    profile_as: Option<(&str, &roast_core::smt_profile::ProfileHandle)>,
) -> Result<Vec<String>, String> {
    let started = std::time::Instant::now();
    let result = run_solver_batch(binary, args, script);
    if let Some((engine, handle)) = profile_as {
        let response = match &result {
            Ok(lines) => lines.first().map(String::as_str).unwrap_or("unknown"),
            Err(_) => "unknown",
        };
        roast_core::smt_profile::record_batch(
            &Some(handle.clone()),
            engine,
            binary,
            script,
            // The caller built the script before calling; attributing encode
            // time here would double-count, so only solver time is recorded.
            std::time::Duration::ZERO,
            started.elapsed(),
            response,
        );
    }
    result
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

/// Turns the shared walk's edges into LIA transition disjuncts.
struct LiaSink {
    prefix: String,
    /// One disjunct per outgoing edge; their disjunction is the transition
    /// relation.
    clauses: Vec<String>,
    errors: Vec<(roast_ir::ObligationId, String)>,
}

impl smt_text::ClauseSink for LiaSink {
    fn transition(&mut self, t: smt_text::Transition<'_>) {
        let mut conds: Vec<String> = t.bindings.to_vec();
        conds.extend_from_slice(t.conds);
        for (i, e) in t.var_exprs.iter().enumerate() {
            let post = format!("{}v{i}p", self.prefix);
            if *e != post {
                conds.push(format!("(= {post} {e})"));
            }
        }
        if !conds.is_empty() {
            self.clauses.push(smt_text::conjoin(&conds));
        }
    }

    fn error(&mut self, e: smt_text::ErrorSite<'_>) {
        let mut conds: Vec<String> = e.bindings.to_vec();
        conds.extend_from_slice(e.conds);
        self.errors.push((e.obligation, smt_text::conjoin(&conds)));
    }
}

/// Encode a method body's transition relation in QF_LIA format.
///
/// Returns declarations, the transition relation, and one error formula per
/// obligation. Variables are integers rather than bitvectors because
/// interpolation support is far better developed for LIA -- which also means
/// Java's wraparound on overflow is not modelled here. See
/// `docs/strategies/imc.md`.
pub fn encode_body_lia(
    body: &roast_ir::Body,
    obligations: &[roast_ir::ObligationId],
    prefix: &str,
) -> LiaEncoding {
    use roast_ir::*;

    let theory = LiaTheory::new(prefix);
    let n_vars = body.vars.len();

    // Pre- and post-state declarations.
    let mut decls = String::new();
    for i in 0..n_vars {
        decls.push_str(&format!("(declare-fun {prefix}v{i} () Int)\n"));
        decls.push_str(&format!("(declare-fun {prefix}v{i}p () Int)\n"));
    }

    let obs: std::collections::HashSet<ObligationId> = obligations.iter().copied().collect();
    let mut fresh = smt_text::FreshPool::new(prefix);
    let mut sink = LiaSink {
        prefix: prefix.to_string(),
        clauses: Vec::new(),
        errors: Vec::new(),
    };
    smt_text::walk_body(body, &theory, &obs, &mut fresh, &mut sink);

    // Everything the walk minted has to be declared, or the script references
    // symbols the solver has never heard of and it answers by discarding the
    // clauses that mention them.
    for (name, _) in fresh.issued() {
        decls.push_str(&format!("(declare-fun {name} () Int)\n"));
    }

    let transition = if sink.clauses.is_empty() {
        "true".to_string()
    } else if sink.clauses.len() == 1 {
        sink.clauses[0].clone()
    } else {
        format!("(or {})", sink.clauses.join(" "))
    };

    LiaEncoding {
        declarations: decls,
        transition,
        error_formulas: sink.errors,
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
