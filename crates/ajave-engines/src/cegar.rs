//! CEGAR (Counterexample-Guided Abstraction Refinement) engine.
//!
//! Direction: Over. Drives a `PredicateCpa` through `explore()` under the
//! `Join` merge policy,
//! growing the precision between runs. On a spurious counterexample trace,
//! extract predicates via interpolation and refine.
//!
//! Original papers:
//! - Predicate abstraction: Graf & Saidi, CAV 1997.
//! - CEGAR: Clarke, Grumberg, Jha, Lu & Veith, CAV 2000 (JACM 2003).
//! - Lazy abstraction: Henzinger, Jhala, Majumdar & Sutre, POPL 2002.

use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_core::fixpoint::{explore, HasLocation, Join};
use ajave_ir::*;
use log::{debug, info};

use ajave_core::term::{Expr, Op};

use crate::body_analysis::{
    all_methods_scoping_enabled, ask_on_decline_enabled, body_uses_havoced_ops, find_defining_bin,
};
use crate::interpolation::{encode_body_lia, find_interpolation_solver, InterpolationSolver};
use crate::predicate::{
    predicates_from_interpolant, CompOp, PredPrec, Predicate, PredicateCpa, PredicateOperand,
};

/// Maximum number of CEGAR refinement iterations.
const MAX_REFINEMENTS: u32 = 20;

/// Maximum abstract states per reachability run.
const MAX_STATES: usize = 10_000;

pub struct CegarEngine {
    solver: Option<InterpolationSolver>,
    done: bool,
}

impl Default for CegarEngine {
    fn default() -> Self {
        Self::new()
    }
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

    /// The open set decides the abstraction's target.
    /// No resumable parameter, deliberately. Refinement here is driven by
    /// spurious counterexamples, not by a bound that can be raised — when it
    /// declines, it is because the body's shape defeats the predicate
    /// abstraction, and more time does not change a shape.
    fn interest(&self) -> Interest {
        Interest::STATUS
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
        // Confirms the entry is loadable; each candidate method fetches its
        // own body in the loop below.
        if prog.body(entry).is_none() {
            return Progress::Exhausted;
        }

        // Which methods to attempt.
        //
        // This engine used to filter `oref.method == *entry`, so an obligation
        // in a helper was not declined — it was never considered. The BMC
        // routinely inlines four deep, so a corpus where assertions live
        // outside `main` was invisible to predicate abstraction entirely.
        //
        // A per-method proof is a proof under *unconstrained parameters*, which
        // is strictly more conservative than one under the caller's actual
        // arguments, so a discharge stays sound. The risk is the opposite: it
        // will often fail and cost time, which is what the gate is for.
        let candidates: Vec<MethodKey> = if all_methods_scoping_enabled() {
            let mut v: Vec<MethodKey> = bb
                .open_or_unconfirmed()
                .iter()
                .map(|o| o.method.clone())
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            // Entry first: it is the method most likely to carry the property,
            // and a proof there can close the task on its own.
            v.sort_by_key(|mk| (mk != entry, mk.clone()));
            v
        } else {
            vec![entry.clone()]
        };

        let mut advanced = false;
        let mut attempted = 0usize;
        let mut asked = 0usize;

        for mk in &candidates {
            let Some(body) = prog.body(mk) else { continue };

            if !body.is_fully_lifted() {
                continue;
            }

            // CEGAR uses predicate abstraction (CPA-based reachability), not SMT
            // satisfiability. When heap operations produce unconstrained abstract
            // values, the predicate domain can't track them, causing the abstract
            // state to collapse to "top" — which makes the safety check trivially
            // succeed, producing unsound TRUE verdicts. Unlike k-induction/CHC/IMC
            // (which use SMT UNSAT checks where fresh values are conservative),
            // CEGAR's abstract interpretation can lose safety-critical information.
            //
            // **This guard is soundness, not capability, and it is per body.**
            // The three-levers experiment deliberately does not relax it: the
            // architecture review called it out as "not a cheap unlock", and
            // opening it needs the collapse mechanism understood plus a test
            // that fails when the abstraction goes to top. Analysing more
            // methods means more bodies each checked by this guard, which is
            // the safe way to widen reach.
            if body_uses_havoced_ops(body) {
                debug!("cegar: {} uses havoced ops, skipping", mk);
                // A decline is a question, not a surrender.
                //
                // Returning `Blocked` tells the scheduler "nothing more to do
                // here" and nothing else. But this engine knows precisely what
                // defeated it: a value it cannot track. Saying so costs nothing
                // and commits to nothing — a `Query` is not a claim — and any
                // later answerer can supply a bound that makes the predicate
                // domain viable.
                //
                // That is what turns an *alternative* engine into also a
                // *resource*, without touching its analysis: only its failure
                // mode changes. The scheduler re-enters it when an answer lands
                // because `Interest::LEMMA` and the delta cursor already exist.
                if ask_on_decline_enabled() {
                    asked += ask_about_untracked(bb, self.id(), mk, body);
                }
                continue;
            }

            let open: Vec<ObligationRef> = bb
                .open_or_unconfirmed()
                .iter()
                .filter(|oref| oref.method == *mk)
                .cloned()
                .collect();

            if open.is_empty() {
                continue;
            }
            attempted += open.len();

            info!(
                "cegar: starting refinement loop for {} obligation(s) in {}",
                open.len(),
                mk
            );

            for oref in &open {
                match try_cegar(solver, prog, body, mk, oref.id) {
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
        }

        if attempted == 0 {
            debug!(
                "cegar: no analysable body among {} candidate method(s), asked {} question(s)",
                candidates.len(),
                asked
            );
            // Having asked, do not retire: `Interest::LEMMA` brings this engine
            // back if anybody answers. Retiring would throw the answer away.
            return if asked > 0 {
                Progress::Blocked
            } else {
                Progress::Exhausted
            };
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Blocked
        }
    }
}

/// Ask about the values that defeated the predicate abstraction.
///
/// One `Bounds` question per variable assigned from an operation this engine
/// cannot track. A bound would let the predicate domain represent the value
/// instead of collapsing to top, which is the specific thing that makes this
/// body unanalysable.
///
/// `Want::Bounds` is a universal question, so only an `Over` or `Exact`
/// answerer may reply — enforced at publish, not here. Capped, because an
/// engine that posts a hundred questions nobody can answer has converted a
/// cheap decline into an expensive one.
fn ask_about_untracked(bb: &mut Blackboard, me: EngineId, mk: &MethodKey, body: &Body) -> usize {
    const MAX_QUESTIONS: usize = 8;
    let mut n = 0;
    for block in &body.blocks {
        for (idx, stmt) in block.stmts.iter().enumerate() {
            if n >= MAX_QUESTIONS {
                return n;
            }
            let Stmt::Assign(vid, rv) = stmt else {
                continue;
            };
            if !crate::body_analysis::stmt_is_havoced_op(stmt) {
                continue;
            }
            // Only int-typed destinations: a bound on a reference means
            // nothing to the predicate domain, and asking would be noise.
            if !body
                .vars
                .get(vid.0 as usize)
                .is_some_and(|vi| matches!(vi.ty, Ty::Int | Ty::Long))
            {
                continue;
            }
            // What the question is *about*, and what the asker already knows.
            // `given` carries the binding so an answerer can recognise the
            // shape — a library call whose range is specified, for instance.
            let about = Expr::Var(*vid);
            let given = match rv {
                Rvalue::Call { target, args, .. } => {
                    let arg_exprs: Vec<Expr> = args
                        .iter()
                        .filter_map(|a| match a {
                            Operand::Var(v) => Some(Expr::Var(*v)),
                            Operand::Const(Const::Int(i)) => Some(Expr::Int(*i as i64)),
                            _ => None,
                        })
                        .collect();
                    if arg_exprs.len() != args.len() {
                        continue;
                    }
                    vec![Expr::bin(
                        Op::Eq,
                        about.clone(),
                        Expr::call(&target.class, &target.name, &target.desc, arg_exprs),
                    )]
                }
                // Not a call: nothing to describe it with, so the question is
                // bare. An answerer with a whole-program fact can still reply.
                _ => Vec::new(),
            };
            bb.ask(
                me,
                ProgramPoint {
                    method: mk.clone(),
                    block: block.id,
                    index: idx,
                },
                about,
                Want::Bounds,
                given,
            );
            n += 1;
        }
    }
    n
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

        let (reached, complete) =
            explore(&PredicateCpa, &Join, prog, &start, prec.clone(), MAX_STATES);

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
                    if state.values.get(i) == Some(&Some(true)) && pred.op == comp {
                        return true;
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
                    if let (Some(lhs), Some(rhs)) =
                        (operand_to_pred_operand(a), operand_to_pred_operand(b))
                    {
                        let pred = Predicate { lhs, op: comp, rhs };
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
                && !declarations.contains(token)
                && !vars.contains(&token.to_string())
            {
                vars.push(token.to_string());
            }
        }
    }
    vars
}

/// The L2 lever: a decline becomes a question.
///
/// `ask_about_untracked` is what turns this engine from an *alternative* into
/// also a *resource*. Its analysis is unchanged; only its failure mode is. So
/// the tests are about the questions: that they are asked at all, that they are
/// about the right terms, that they are bounded, and that asking does not
/// retire the engine before an answer can arrive.
#[cfg(test)]
mod ask_on_decline_tests {
    use super::*;
    use ajave_core::artifact::Want;

    fn key(name: &str) -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: name.into(),
            desc: "()V".into(),
        }
    }

    fn var(slot: u16, ty: Ty) -> VarInfo {
        VarInfo {
            kind: VarKind::Local(slot),
            ty,
        }
    }

    /// One block: an int from an unresolved call, a ref from a `New`, and a
    /// plain copy. Only the first is worth asking about.
    fn mixed_body() -> (Program, MethodKey) {
        let mk = key("main");
        let lib = MethodKey {
            class: "java/lang/Math".into(),
            name: "sin".into(),
            desc: "(D)D".into(),
        };
        let mut prog = Program::default();
        prog.bodies.insert(
            mk.clone(),
            Body {
                is_static: true,
                key: mk.clone(),
                entry: BlockId(0),
                vars: vec![
                    var(0, Ty::Int),
                    var(1, Ty::Ref),
                    var(2, Ty::Int),
                    var(3, Ty::Int),
                ],
                obligations: vec![],
                blocks: vec![Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![
                        // Untracked, int-typed: ask.
                        Stmt::Assign(
                            VarId(0),
                            Rvalue::Call {
                                target: lib.clone(),
                                args: vec![Operand::int(1)],
                                is_virtual: false,
                            },
                        ),
                        // Untracked but a reference: a bound means nothing to
                        // the predicate domain, so do not ask.
                        Stmt::Assign(VarId(1), Rvalue::New("java/lang/Object".into())),
                        // Tracked: not a decline cause at all.
                        Stmt::Assign(VarId(2), Rvalue::Use(Operand::int(7))),
                    ],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                }],
            },
        );
        prog.entry = Some(mk.clone());
        (prog, mk)
    }

    /// Asks about the untracked integer, and about nothing else.
    ///
    /// A reference is excluded deliberately: `Want::Bounds` on a pointer is a
    /// question no answerer can usefully reply to, and an engine that posts
    /// unanswerable questions has converted a cheap decline into an expensive
    /// one.
    #[test]
    fn it_asks_about_untracked_integers_and_not_references() {
        let (prog, mk) = mixed_body();
        let body = prog.body(&mk).unwrap();
        let mut bb = Blackboard::new();
        let n = ask_about_untracked(&mut bb, EngineId("cegar"), &mk, body);
        assert_eq!(n, 1, "one int from an untracked op, so one question");

        let qs = bb.unanswered();
        assert_eq!(qs.len(), 1);
        assert_eq!(
            qs[0].want,
            Want::Bounds,
            "a bound is what unblocks the domain"
        );
        assert_eq!(
            qs[0].about,
            ajave_core::term::Expr::Var(VarId(0)),
            "the question is about the destination of the untracked call"
        );
        assert_eq!(
            qs[0].at.method, mk,
            "a VarId indexes one Body, so the point must name the method"
        );
    }

    /// The question carries the call that produced the value, so an answerer
    /// can recognise a signature whose range is specified.
    ///
    /// Without `given`, `ranges` sees "bound v0" with no way to know v0 came
    /// from `Math.sin` — which is exactly the lemma it holds.
    #[test]
    fn the_question_carries_the_call_that_produced_the_value() {
        let (prog, mk) = mixed_body();
        let body = prog.body(&mk).unwrap();
        let mut bb = Blackboard::new();
        ask_about_untracked(&mut bb, EngineId("cegar"), &mk, body);
        let qs = bb.unanswered();
        let given = format!("{:?}", qs[0].given);
        assert!(
            given.contains("sin"),
            "the binding must name the callee; given was {given}"
        );
    }

    /// Bounded. A body with many untracked assignments must not post one
    /// question per statement — the cap is what keeps a decline cheap.
    #[test]
    fn the_number_of_questions_is_capped() {
        let mk = key("main");
        let lib = MethodKey {
            class: "com/example/Unknown".into(),
            name: "f".into(),
            desc: "(I)I".into(),
        };
        let mut prog = Program::default();
        let n_stmts = 40usize;
        prog.bodies.insert(
            mk.clone(),
            Body {
                is_static: true,
                key: mk.clone(),
                entry: BlockId(0),
                vars: (0..n_stmts as u16).map(|i| var(i, Ty::Int)).collect(),
                obligations: vec![],
                blocks: vec![Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: (0..n_stmts)
                        .map(|i| {
                            Stmt::Assign(
                                VarId(i as u32),
                                Rvalue::Call {
                                    target: lib.clone(),
                                    args: vec![Operand::int(1)],
                                    is_virtual: false,
                                },
                            )
                        })
                        .collect(),
                    term: Terminator::Return(None),
                    exceptional: vec![],
                }],
            },
        );
        prog.entry = Some(mk.clone());
        let body = prog.body(&mk).unwrap();
        let mut bb = Blackboard::new();
        let n = ask_about_untracked(&mut bb, EngineId("cegar"), &mk, body);
        assert!(n <= 8, "asked {n} questions; the cap is 8");
        assert!(n > 0, "it must still ask something");
    }

    /// Identical questions are one question.
    ///
    /// `Blackboard::ask` deduplicates, and this pins that the asker benefits:
    /// two declines over the same body must not double the queue.
    #[test]
    fn asking_twice_about_the_same_body_does_not_duplicate() {
        let (prog, mk) = mixed_body();
        let body = prog.body(&mk).unwrap();
        let mut bb = Blackboard::new();
        ask_about_untracked(&mut bb, EngineId("cegar"), &mk, body);
        ask_about_untracked(&mut bb, EngineId("cegar"), &mk, body);
        assert_eq!(bb.unanswered().len(), 1);
    }
}
