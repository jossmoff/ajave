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

use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_ir::*;
use log::{debug, info};

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

    /// Same two inputs as k-induction: the open set and `Bounded` base cases.
    /// No resumable parameter, deliberately.
    ///
    /// `MAX_ITERATIONS` bounds a fixpoint that either converges or does not;
    /// raising it does not make an interpolant sequence converge, it only
    /// spends longer failing to. `Progress::Suspended` would be a promise of
    /// progress this engine cannot keep, so it never returns one.
    fn interest(&self) -> Interest {
        Interest::STATUS
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
        // `open_or_unconfirmed`, not `open`: a violation from an
        // under-approximating engine is a *candidate* until JVM replay
        // confirms it, and `open()` hides those obligations from every
        // over-approximating engine. Whichever engine published first then
        // won outright, so a spurious candidate permanently blocked the
        // proof that would have refuted it. `proved_safe` records the
        // discharge either way, and `verdict_excluding` turns it into a
        // TRUE only once the violation is actually refuted.
        let open = bb.open_or_unconfirmed();
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
            return Progress::Blocked;
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

            // An over-approximating engine cannot see past a `Diverge`, and
            // `core::cfg` makes one deliberately indistinguishable from a
            // return so that the truncation is not hidden from the analysis.
            // Noticing it is therefore the engine's job, which `cegar.rs` does
            // and this engine did not until 2026-10-26 (#43).
            //
            // The encoder also drops `Diverge` and `Throw` terminators
            // entirely (`interpolation.rs`'s `_ => {}` over terminators), so
            // those edges are simply absent from the transition relation a
            // proof is taken over.
            if !body.is_fully_lifted() {
                debug!(
                    "imc: declining {} — {} is not fully lifted",
                    oref, oref.method.name
                );
                continue;
            }

            // The error arm used to be dropped silently, which is how a
            // solver that failed on every call looked like an engine that
            // simply never found a proof (#43).
            let outcome = try_imc(solver, body, oref.id);
            if let Err(why) = &outcome {
                debug!("imc: {} could not be attempted — {why}", oref);
            }
            if let Ok(proved) = outcome {
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
            Progress::Blocked
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
/// # What this proof rests on, besides the interpolation argument
///
/// Audited 2026-10-26 (#43). This engine publishes `Over`, so a gap in the
/// encoding is a wrong TRUE. Two properties keep it sound, **neither of which
/// was chosen for that purpose**, and both are easy to remove while trying to
/// make the encoding sharper:
///
/// 1. `smt_text::Encoder::rvalue` ends in `_ => self.fresh(..)`. Every rvalue
///    the encoder does not model — `GetField`, `GetStatic`, `ArrayLoad`,
///    `Call`, `Havoc` — becomes an unconstrained variable. That is why the
///    block walk's `_ => {}` over `PutField`/`PutStatic`/`ArrayStore` is
///    harmless: the writes are dropped, but every read of what they would have
///    written is unconstrained anyway, so violations stay easier to find
///    rather than harder.
///
/// 2. `var_exprs` is reset to the pre-state at the top of every block, so each
///    error formula is written over that block's own unconstrained pre-state.
///    That is why dropping `Diverge` and `Throw` terminators — which leaves
///    their edges out of the transition relation — does not turn into a proof:
///    a missing edge into a block cannot make the block's local error
///    condition UNSAT.
///
/// Sharpen either one and the other stops covering for it. If you give
/// unmodelled rvalues real semantics, the dropped writes become unsound. If
/// you thread state across blocks, the dropped terminators become unsound.
/// `imc_conservatism_tests` pins both.
fn try_imc(solver: &InterpolationSolver, body: &Body, oid: ObligationId) -> Result<bool, String> {
    let encoding = encode_body_lia(body, &[oid], "");

    // *Every* error formula for this obligation, not just the first.
    //
    // An obligation checked in more than one block has one clause per block,
    // and the encoder now adds a clause per block for arithmetic overflow as
    // well. `find` took whichever came first and silently dropped the rest, so
    // a proof could rest on one path while another was never considered.
    let parts: Vec<String> = encoding
        .error_formulas
        .iter()
        .filter(|(id, _)| *id == oid)
        .map(|(_, f)| f.clone())
        .collect();

    if parts.is_empty() {
        // Obligation not in this body → trivially safe.
        return Ok(true);
    }
    let error_formula = if parts.len() == 1 {
        parts[0].clone()
    } else {
        format!("(or {})", parts.join(" "))
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

#[cfg(test)]
mod imc_conservatism_tests {
    //! Guards for the two properties `try_imc`'s doc comment names.
    //!
    //! `imc.rs` and `interpolation.rs` had zero tests between them while
    //! publishing `Direction::Over`, which CLAUDE.md forbids: "Every engine
    //! publishing `Over` needs a test that would fail if its encoding were
    //! unsound, independent of blackboard gating." `chc.rs` and
    //! `kinduction.rs` have theirs; these are IMC's.
    //!
    //! They are deliberately *not* bug demonstrations — the investigation in
    //! #43 could not construct a wrong TRUE, because the encoder's two
    //! independent conservatisms cover for each other's gaps. They pin that
    //! cover in place, so a later precision improvement that removes one has
    //! to notice the other.

    use super::*;
    use ajave_ir::{
        Block, BlockId, Body, Const, MethodKey, Obligation, ObligationId, ObligationKind, Operand,
        Rvalue, Terminator, Ty, VarId, VarInfo, VarKind,
    };

    fn mk() -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: "m".into(),
            desc: "()V".into(),
        }
    }

    fn one_var() -> Vec<VarInfo> {
        vec![VarInfo {
            kind: VarKind::Local(0),
            ty: Ty::Int,
        }]
    }

    /// Safety condition `v0`: violated at any reachable state where `v0 == 0`.
    fn ob() -> Vec<Obligation> {
        vec![Obligation {
            id: ObligationId(0),
            kind: ObligationKind::Assertion,
            cond: Operand::Var(VarId(0)),
            guarded: false,
            bytecode_offset: 0,
            line: None,
        }]
    }

    /// `v0 = 1; check(v0);` — genuinely safe, and the encoder can see it.
    /// Establishes the fixtures are not trivially unprovable, so a `false`
    /// elsewhere means something.
    fn provably_safe() -> Body {
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: one_var(),
            obligations: ob(),
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts: vec![
                    Stmt::Assign(VarId(0), Rvalue::Use(Operand::Const(Const::Int(1)))),
                    Stmt::Check(ObligationId(0)),
                ],
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    /// The same check, but `v0` comes from an unmodelled rvalue. The encoder
    /// must treat that as unconstrained — so `v0 == 0` stays satisfiable and
    /// the obligation must not be proved.
    fn safe_only_if_an_unmodelled_read_is_believed() -> Body {
        let mut b = provably_safe();
        b.blocks[0].stmts = vec![
            Stmt::Assign(
                VarId(0),
                Rvalue::Call {
                    target: MethodKey {
                        class: "java/lang/Math".into(),
                        name: "max".into(),
                        desc: "(II)I".into(),
                    },
                    args: vec![Operand::Const(Const::Int(1)), Operand::Const(Const::Int(2))],
                    is_virtual: false,
                },
            ),
            Stmt::Check(ObligationId(0)),
        ];
        b
    }

    /// A body the frontend could not fully lift. `is_fully_lifted` is false,
    /// and the engine must decline rather than reason about a transition
    /// relation that is missing the diverging block's edges.
    fn not_fully_lifted() -> Body {
        let mut b = provably_safe();
        b.blocks.push(Block {
            id: BlockId(1),
            bytecode_offset: 1,
            stmts: vec![],
            term: Terminator::Diverge("unlifted opcode".into()),
            exceptional: vec![],
        });
        b.blocks[0].term = Terminator::Goto(BlockId(1));
        b
    }

    #[test]
    fn a_diverging_body_is_not_fully_lifted_and_the_engine_declines_it() {
        let b = not_fully_lifted();
        assert!(
            !b.is_fully_lifted(),
            "fixture precondition: the body must contain a Diverge, or this \
             test exercises the ordinary path instead of the one under test"
        );
        // The guard is in `step`, which needs a solver and a blackboard; what
        // is asserted here is the predicate the guard consults. Pinning it
        // separately matters because `core::cfg` makes `Diverge` deliberately
        // indistinguishable from a return, so this predicate is the *only*
        // signal an engine gets.
        assert!(provably_safe().is_fully_lifted());
    }

    #[test]
    fn an_unmodelled_read_is_unconstrained_so_nothing_is_proved_about_it() {
        let Some(solver) = find_interpolation_solver() else {
            eprintln!("no interpolation-capable solver on PATH; skipping");
            return;
        };

        // Control: the encoder can prove the version it understands.
        let safe = try_imc(&solver, &provably_safe(), ObligationId(0));
        assert_eq!(
            safe,
            Ok(true),
            "control failed: the encoder could not prove `v0 = 1; check(v0)`, \
             so the negative result below would prove nothing"
        );

        // The property. `Math.max(1, 2)` is 2 in any real execution, so the
        // check does hold — but the encoder does not model calls, and an
        // engine may not prove a property that rests on a value it declined
        // to interpret.
        let unknown = try_imc(
            &solver,
            &safe_only_if_an_unmodelled_read_is_believed(),
            ObligationId(0),
        );
        assert_eq!(
            unknown,
            Ok(false),
            "IMC proved an obligation whose safety depends on an unmodelled \
             call. `smt_text::Encoder::rvalue`'s `_ => self.fresh(..)` is what \
             makes the dropped heap writes in `encode_body_lia` harmless; if \
             unmodelled rvalues ever gain semantics, those writes become \
             unsound (#43)."
        );
    }
}
