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

use std::collections::HashSet;
use std::io::Write as IoWrite;
use std::process::{Command, Stdio};

use log::{debug, info, warn};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::*;

use crate::body_analysis::body_uses_havoced_ops;
use crate::smt_text::{self, BitvectorTheory};

pub struct ChcEngine {
    solver_binary: String,
    done: bool,
}

impl Default for ChcEngine {
    fn default() -> Self {
        Self::new()
    }
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

/// Turns the shared walk's edges into Horn clauses.
struct HornSink<'a> {
    out: &'a mut String,
    /// `(v0 (_ BitVec 32)) (v1 ...)` for the pre-state.
    forall_src: &'a str,
    /// The same, plus the primed post-state.
    forall_both: &'a str,
    src_args: &'a str,
    dst_args: &'a str,
}

impl HornSink<'_> {
    /// A clause's quantifier prefix must bind the fresh symbols that clause
    /// mentions. Missing them is what produced scripts z3 answers by dropping
    /// the offending clause -- see `parse_chc_answer`.
    fn prefix(base: &str, fresh: &[(String, u32)]) -> String {
        if fresh.is_empty() {
            return base.to_string();
        }
        let extra: Vec<String> = fresh
            .iter()
            .map(|(name, w)| format!("({name} (_ BitVec {w}))"))
            .collect();
        format!("{base} {}", extra.join(" "))
    }
}

impl smt_text::ClauseSink for HornSink<'_> {
    fn transition(&mut self, t: smt_text::Transition<'_>) {
        // A terminator that leaves the body has no successor relation to imply.
        let Some(to) = t.to else { return };

        let mut conds: Vec<String> = t.bindings.to_vec();
        conds.extend_from_slice(t.conds);
        for (i, e) in t.var_exprs.iter().enumerate() {
            let post = format!("v{i}'");
            if *e != post {
                conds.push(format!("(= {post} {e})"));
            }
        }
        conds.push(format!("(block_{} {})", t.from.0, self.src_args));

        self.out.push_str(&format!(
            "(assert (forall ({}) (=> {} (block_{} {}))))\n",
            Self::prefix(self.forall_both, t.fresh),
            smt_text::conjoin(&conds),
            to.0,
            self.dst_args
        ));
    }

    fn error(&mut self, e: smt_text::ErrorSite<'_>) {
        let mut conds: Vec<String> = e.bindings.to_vec();
        conds.extend_from_slice(e.conds);
        conds.push(format!("(block_{} {})", e.block.0, self.src_args));

        self.out.push_str(&format!(
            "(assert (forall ({}) (=> {} error)))\n",
            Self::prefix(self.forall_src, e.fresh),
            smt_text::conjoin(&conds)
        ));
    }
}

/// Encode a method body as CHC in SMT-LIB2 format.
fn encode_chc(body: &Body, obligations: &[ObligationId]) -> String {
    let mut out = String::new();
    out.push_str("(set-logic HORN)\n");

    let widths: Vec<u32> = body.vars.iter().map(|vi| width_of(&vi.ty)).collect();
    let n_vars = widths.len();

    // One relation per block, over every variable in the method.
    let sig: String = widths
        .iter()
        .map(|w| format!("(_ BitVec {w})"))
        .collect::<Vec<_>>()
        .join(" ");
    for block in &body.blocks {
        out.push_str(&format!(
            "(declare-fun block_{} ({}) Bool)\n",
            block.id.0, sig
        ));
    }
    out.push_str("(declare-fun error () Bool)\n");

    let src_args: String = (0..n_vars)
        .map(|i| format!("v{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    let dst_args: String = (0..n_vars)
        .map(|i| format!("v{i}'"))
        .collect::<Vec<_>>()
        .join(" ");
    let forall_src: String = widths
        .iter()
        .enumerate()
        .map(|(i, w)| format!("(v{i} (_ BitVec {w}))"))
        .collect::<Vec<_>>()
        .join(" ");
    let forall_both: String = {
        let src = widths
            .iter()
            .enumerate()
            .map(|(i, w)| format!("(v{i} (_ BitVec {w}))"));
        let dst = widths
            .iter()
            .enumerate()
            .map(|(i, w)| format!("(v{i}' (_ BitVec {w}))"));
        src.chain(dst).collect::<Vec<_>>().join(" ")
    };

    // Entry rule: every variable is unconstrained on entry.
    out.push_str(&format!(
        "(assert (forall ({forall_src}) (block_{} {src_args})))\n",
        body.entry.0
    ));

    let obs: HashSet<ObligationId> = obligations.iter().copied().collect();
    let mut fresh = smt_text::FreshPool::new("chc_");
    {
        let mut sink = HornSink {
            out: &mut out,
            forall_src: &forall_src,
            forall_both: &forall_both,
            src_args: &src_args,
            dst_args: &dst_args,
        };
        smt_text::walk_body(body, &BitvectorTheory, &obs, &mut fresh, &mut sink);
    }

    // Query: is error reachable? See `parse_chc_answer` for what the answer
    // means -- the polarity is the opposite of the `(query ...)` idiom.
    out.push_str("(assert (not error))\n");
    out.push_str("(check-sat)\n");

    out
}

/// What a Horn solver told us about the query.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ChcAnswer {
    /// An interpretation of the block relations satisfying every clause with
    /// `error` false exists: the error state is unreachable, the program is
    /// safe.
    Safe,
    /// No such interpretation: `error` is derivable, so the error state is
    /// reachable. This engine is `Over` and may not publish a violation, so
    /// this is "not a proof", not "a bug".
    Unsafe,
    /// Timeout, `unknown`, a malformed script, or anything we do not recognise.
    NoAnswer,
}

/// Interpret a Horn solver's output.
///
/// **The polarity here is the opposite of the `(query ...)` idiom**, and this
/// function previously had it backwards -- it treated `unsat` as "safe" and
/// discharged on it. Under the encoding roast actually emits (SMT-LIB2 rules
/// plus `(assert (not error))` and `(check-sat)`) the solver is being asked
/// whether an interpretation of the block relations exists that satisfies every
/// clause while keeping `error` false:
///
/// * `sat` -- such an interpretation exists. It *is* the inductive invariant.
///   The program is safe.
/// * `unsat` -- no interpretation exists, so `error` is derivable from the
///   clauses. The program is unsafe.
///
/// The `(query error)` dialect of Z3's fixedpoint engine reports the reverse
/// (`sat` = reachable), which is where the confusion came from. Discharging on
/// `unsat` meant discharging exactly when the error was reachable: a false
/// TRUE, the single most expensive thing this tool can do.
///
/// Any `(error ...)` line voids the answer. A solver that rejects part of a
/// script carries on with the clauses it did parse and still prints a verdict
/// -- and a *dropped* clause is a dropped constraint, which makes the system
/// easier to satisfy and pushes the answer toward `sat`. Believing that would
/// turn a broken encoding into a proof.
pub(crate) fn parse_chc_answer(stdout: &str) -> ChcAnswer {
    if stdout.contains("(error") {
        warn!("chc: solver reported an error, refusing to draw a conclusion");
        return ChcAnswer::NoAnswer;
    }
    match stdout.lines().map(str::trim).rfind(|l| !l.is_empty()) {
        Some("sat") => ChcAnswer::Safe,
        Some("unsat") => ChcAnswer::Unsafe,
        _ => ChcAnswer::NoAnswer,
    }
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
        // Kept piped rather than nulled: solvers differ on which stream an
        // `(error ...)` line goes to, and `parse_chc_answer` has to see it.
        .stderr(Stdio::piped())
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
    let combined = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    debug!("chc: solver returned: {}", combined.trim());

    match parse_chc_answer(&combined) {
        ChcAnswer::Safe => {
            // One error relation covers every obligation in the body, so a
            // safe answer discharges all of them together.
            Ok(obligations.iter().map(|oid| (*oid, true)).collect())
        }
        ChcAnswer::Unsafe | ChcAnswer::NoAnswer => Ok(vec![]),
    }
}

#[cfg(test)]
mod tests {
    use super::{parse_chc_answer, ChcAnswer};

    #[test]
    fn sat_means_safe_and_unsat_means_unsafe() {
        // Verified against z3 5.1.0 with the exact script shape `encode_chc`
        // emits: a safe program answers `sat`, an unsafe one answers `unsat`.
        assert_eq!(parse_chc_answer("sat\n"), ChcAnswer::Safe);
        assert_eq!(parse_chc_answer("unsat\n"), ChcAnswer::Unsafe);
    }

    #[test]
    fn an_error_line_voids_the_answer() {
        // z3 does not abort on an unknown constant: it drops the offending
        // clause and prints a verdict anyway. A dropped clause is a dropped
        // constraint, which biases the answer toward `sat` -- i.e. toward a
        // spurious proof.
        let out = "(error \"line 6 column 73: unknown constant bv_fresh0\")\nsat\n";
        assert_eq!(parse_chc_answer(out), ChcAnswer::NoAnswer);
    }

    #[test]
    fn unknown_and_junk_are_not_answers() {
        assert_eq!(parse_chc_answer("unknown\n"), ChcAnswer::NoAnswer);
        assert_eq!(parse_chc_answer(""), ChcAnswer::NoAnswer);
        assert_eq!(parse_chc_answer("timeout\n"), ChcAnswer::NoAnswer);
    }

    #[test]
    fn trailing_blank_lines_do_not_hide_the_verdict() {
        assert_eq!(parse_chc_answer("sat\n\n  \n"), ChcAnswer::Safe);
    }
}
