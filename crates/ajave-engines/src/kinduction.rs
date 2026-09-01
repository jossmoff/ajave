//! k-induction engine.
//!
//! Proves safety by combining bounded model checking (base case) with an
//! inductive step case. Direction: Over.
//!
//! Base case: consumes `Status::Bounded { k }` artifacts published by the
//! SMT BMC engine — "no violation reachable in ≤k steps."
//!
//! Step case: for k *generic* symbolic consecutive states connected by the
//! transition relation, if the property holds at each of the first k states,
//! does it hold at state k+1?  If UNSAT, the property is inductive and
//! discharged as `ProofKind::KInduction { k }`.
//!
//! For loop-free methods, k=0 suffices: the base case already covers all
//! reachable states (there are no cycles to unroll further).
//!
//! Original paper: Sheeran, Singh & Stålmarck, "Checking Safety Properties
//! Using Induction and a SAT-Solver", CHARME 2000.

use log::{debug, info};
use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_core::smt::{SatResult, SolverFactory};
use ajave_ir::*;

use std::collections::BTreeSet;

use crate::body_analysis::body_has_loops;
use crate::smt_encode;

pub struct KInduction {
    factory: Box<dyn SolverFactory>,
    done: bool,
}

impl KInduction {
    pub fn new(factory: Box<dyn SolverFactory>) -> Self {
        KInduction {
            factory,
            done: false,
        }
    }
}

impl Engine for KInduction {
    fn id(&self) -> EngineId {
        EngineId("k-induction")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        // Collect open obligations that have a Bounded base case.
        let open = bb.open();
        if open.is_empty() {
            return Progress::Exhausted;
        }

        // Obligations whose loop this engine can induct over. Since the base
        // case is established here rather than taken from `Status::Bounded`,
        // there is no reason to wait for that artifact — and good reason not
        // to: it is published only when a run finds no violation anywhere, so
        // requiring it starved the engine on exactly the programs with loops.
        // Its `k` was never usable either, being a bound on path length rather
        // than on iterations (#76).
        let inductive: Vec<ObligationRef> = open
            .iter()
            .filter(|oref| {
                prog.body(&oref.method)
                    .is_some_and(|b| smt_encode::k_induction_applicable(b, oref.id))
            })
            .cloned()
            .collect();

        // Obligations the BMC exhausted to a depth, which the loop-free path
        // below can discharge outright.
        let bounded: Vec<(ObligationRef, u32)> = open
            .iter()
            .filter_map(|oref| match bb.status(oref) {
                Status::Bounded { k } => Some((oref.clone(), *k)),
                _ => None,
            })
            .collect();

        if bounded.is_empty() && inductive.is_empty() {
            debug!("k-induction: nothing to work on");
            return Progress::Stalled;
        }

        info!(
            "k-induction: {} obligation(s) with a bounded base case, {} inside \
             a loop this can induct over",
            bounded.len(),
            inductive.len()
        );

        let mut advanced = false;

        for oref in &inductive {
            let Some(body) = prog.body(&oref.method) else { continue };
            match self.try_k_induction(body, oref.id) {
                Ok(Some(proved_k)) => {
                    debug!("k-induction: proved {oref} by induction at k={proved_k}");
                    let _ = bb.publish(
                        self.id(),
                        self.direction(),
                        Artifact::Status(
                            oref.clone(),
                            Status::Discharged {
                                by: self.id(),
                                proof: ProofKind::KInduction { k: proved_k },
                            },
                        ),
                    );
                    advanced = true;
                }
                Ok(None) => {}
                Err(e) => debug!("k-induction: solver error on {oref}: {e}"),
            }
        }

        for (oref, k) in &bounded {
            let Some(body) = prog.body(&oref.method) else {
                continue;
            };

            // Loop-freeness has to cover everything the method can call, not
            // just its own CFG. `Bounded` is published exactly when the BMC
            // could NOT discharge the obligation, and one reason for that is a
            // loop in a *callee* that hit MAX_LOOP_UNROLL. Judging the entry
            // body alone would take that incomplete search for an exhaustive
            // one (#76).
            let has_loops = reachable_has_loops(prog, &oref.method);

            if !has_loops {
                // Nothing the method can reach has a back-edge, so the BMC's
                // bounded search covered every path. Discharge directly.
                debug!(
                    "k-induction: {} is loop-free, discharging at k={}",
                    oref, k
                );
                let _ = bb.publish(
                    self.id(),
                    self.direction(),
                    Artifact::Status(
                        oref.clone(),
                        Status::Discharged {
                            by: self.id(),
                            proof: ProofKind::KInduction { k: *k },
                        },
                    ),
                );
                advanced = true;
                continue;
            }

            // Induction was already attempted above for anything shaped for
            // it. What is left is a whole-body encoding, which can conclude
            // something only when it covers every path.
            // Encode the body as an SMT formula and check if the property
            // is inductive (holds after one more step given it held before).
            if let Ok(result) = self.try_step_case(body, oref.id) {
                if result {
                    debug!("k-induction: step case proved for {}", oref);
                    let _ = bb.publish(
                        self.id(),
                        self.direction(),
                        Artifact::Status(
                            oref.clone(),
                            Status::Discharged {
                                by: self.id(),
                                proof: ProofKind::KInduction { k: *k },
                            },
                        ),
                    );
                    advanced = true;
                } else {
                    debug!("k-induction: step case inconclusive for {}", oref);
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

/// Whether `entry` or anything reachable from it by a direct call has a loop.
///
/// `body_has_loops` treats an edge to a lower-numbered block as a back-edge,
/// which over-reports for a forward jump to an earlier block. Over-reporting
/// is the safe direction here: it only makes the engine decline.
///
/// A call whose target has no body — an unmodelled library method — is treated
/// as looping. We cannot see whether it terminates, and assuming it does not
/// loop is the assumption that has to be justified.
fn reachable_has_loops(prog: &Program, entry: &MethodKey) -> bool {
    let mut seen: BTreeSet<MethodKey> = BTreeSet::new();
    let mut work = vec![entry.clone()];
    while let Some(key) = work.pop() {
        if !seen.insert(key.clone()) {
            continue;
        }
        let Some(body) = prog.body(&key) else {
            // No body to inspect. Only a method the BMC itself models can be
            // assumed loop-free, and we cannot tell that from here.
            return true;
        };
        if body_has_loops(body) {
            return true;
        }
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Stmt::Assign(_, Rvalue::Call { target, .. }) = stmt {
                    work.push(target.clone());
                }
            }
        }
    }
    false
}

/// Depths attempted, in order. Each is a separate pair of solver queries, so
/// this is a cost as well as a reach: past 3 the encodings get large and the
/// programs that need a deeper induction usually need an invariant instead.
const K_SCHEDULE: [u32; 3] = [1, 2, 3];

/// Largest encoding this engine will attempt, in the rough term count
/// `smt_encode::k_induction_cost` reports.
///
/// k-induction runs after the BMC and can only decide what the BMC left open,
/// so spending the task budget here loses answers the earlier engines had
/// already found. `argv-tasks/ActiveCheck` demonstrated it: once the engine
/// stopped requiring `Status::Bounded` it began attempting a ~20,900-term
/// encoding whose base-case query z3 did not answer in over six minutes,
/// turning an UNKNOWN into a TIMEOUT.
///
/// This is a fitted constant and is recorded as one. The two measured points
/// are far apart -- successful proofs encode at ~10^3 terms
/// (`LoopInvariantNeedsInduction` is 1,026) and the pathological case is
/// ~2x10^4 -- so any cap between them behaves identically, and the exact
/// value is not load-bearing. A solver query timeout is set as well, but did
/// not prevent that hang on its own, so this does not rely on one.
const MAX_ENCODING_COST: usize = 8_000;

impl KInduction {
    /// Prove an obligation inside a loop by induction on the iteration count.
    ///
    /// Both queries must come back UNSAT. Checking only the step case would
    /// prove nothing — a property that never holds is trivially preserved —
    /// and checking only the base case is the bounded check this engine used
    /// to publish as a proof (#76).
    fn try_k_induction(&self, body: &Body, oid: ObligationId) -> Result<Option<u32>, String> {
        for k in K_SCHEDULE {
            let cost = smt_encode::k_induction_cost(body, oid, k).unwrap_or(usize::MAX);
            if cost > MAX_ENCODING_COST {
                debug!(
                    "k-induction: {oid:?} at k={k} would encode ~{cost} terms, over the \
                     {MAX_ENCODING_COST} cap; skipping (a larger k is bigger still)"
                );
                return Ok(None);
            }
            debug!("k-induction: {oid:?} at k={k} costs ~{cost} terms");
            let mut solver = self.factory.create()?;
            let Some(q) = smt_encode::encode_k_induction(solver.as_mut(), body, oid, k) else {
                // Shape the encoder cannot handle; a larger k will not change
                // that, so stop rather than repeat the work.
                return Ok(None);
            };

            debug!("k-induction: {oid:?} k={k} encoded; checking base");
            solver.push();
            solver.assert(q.base);
            let base = solver.check_sat();
            solver.pop();
            if base != SatResult::Unsat {
                // A violation within the first k iterations. This is a real
                // counterexample if `base` is Sat, and unknown otherwise;
                // either way there is nothing to prove and no larger k helps.
                debug!("k-induction: base case for {oid:?} at k={k} came back {base:?}");
                return Ok(None);
            }

            debug!("k-induction: {oid:?} k={k} base UNSAT; checking step");
            solver.push();
            solver.assert(q.step);
            let step = solver.check_sat();
            solver.pop();
            if step == SatResult::Unsat {
                return Ok(Some(k));
            }
            debug!("k-induction: step case for {oid:?} not inductive at k={k}");
        }
        Ok(None)
    }

    /// Try to prove the obligation cannot be violated anywhere in `body`.
    ///
    /// Returns `Ok(true)` only when the encoding covers **every** execution of
    /// the body and the violation term is UNSAT on it. Anything else is
    /// inconclusive.
    ///
    /// # Why this is not yet a step case
    ///
    /// It is named for what the engine is meant to do, and what it does is
    /// weaker: a single check that the obligation is unviolable from an
    /// arbitrary initial state. That is a valid safety argument for a body the
    /// encoder describes completely, and it is *only* that.
    ///
    /// It used to be applied to bodies the encoder does **not** describe
    /// completely — anything with a loop, where the formula covers one
    /// iteration — and the resulting UNSAT was published as a proof. That is
    /// how `LoopFailsOnSecondIteration` was "proved" despite failing on its
    /// second iteration (#76). Real k-induction needs a base case over the
    /// first k iterations and a step case over the transition relation, and
    /// `Status::Bounded { k }` cannot supply the base case: its `k` is the
    /// BMC's `max_depth`, a bound on path length, not on loop iterations.
    /// Consuming it as an iteration count would be the same confusion in a
    /// different place.
    ///
    /// Until that exists, a body with loops is declined.
    fn try_step_case(&self, body: &Body, oid: ObligationId) -> Result<bool, String> {
        let mut solver = self.factory.create()?;
        let encoding = smt_encode::encode_body(solver.as_mut(), body, "step");

        // The encoder reports whether it followed every edge. A formula that
        // omits back-edges, handlers, or unlifted instructions can be UNSAT
        // for a program that is unsafe on the paths it left out.
        if !encoding.complete {
            debug!("k-induction: encoding of {} is incomplete, declining", body.key);
            return Ok(false);
        }

        let violation = match encoding.violation_terms.get(&oid) {
            Some(&t) => t,
            // Not encoded. If the obligation is in the body at all, this means
            // the encoder never reached it, which is not the same as it being
            // safe.
            None => return Ok(body.obligations.iter().all(|o| o.id != oid)),
        };

        solver.push();
        solver.assert(violation);
        let result = solver.check_sat();
        solver.pop();

        match result {
            SatResult::Unsat => Ok(true),
            _ => Ok(false),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_core::smt_smtlib::SmtLibFactory;

    fn key() -> MethodKey {
        MethodKey { class: "Main".into(), name: "main".into(), desc: "()V".into() }
    }

    fn int_var(slot: u16) -> VarInfo {
        VarInfo { kind: VarKind::Local(slot), ty: Ty::Int }
    }

    /// ```text
    /// B0: x = 0; i = 0;            -> B1
    /// B1: if (i < 3) B2 else B3
    /// B2: x = x + 1; check(x < 2); i = i + 1;  -> B1   (back-edge)
    /// B3: return
    /// ```
    ///
    /// x is 1 on the first iteration and 2 on the second, so the obligation
    /// `x < 2` holds once and then fails. This is the IR of
    /// `benchmarks/ajave/kinduction/LoopFailsOnSecondIteration`.
    fn loop_failing_on_second_iteration() -> Body {
        let (x, i, t) = (VarId(0), VarId(1), VarId(2));
        Body {
            key: key(),
            entry: BlockId(0),
            vars: vec![int_var(0), int_var(1), int_var(2)],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(t),
                bytecode_offset: 0,
                line: None,
                guarded: false,
            }],
            blocks: vec![
                Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![
                        Stmt::Assign(x, Rvalue::Use(Operand::int(0))),
                        Stmt::Assign(i, Rvalue::Use(Operand::int(0))),
                    ],
                    term: Terminator::Goto(BlockId(1)),
                    exceptional: vec![],
                },
                Block {
                    id: BlockId(1),
                    bytecode_offset: 1,
                    stmts: vec![Stmt::Assign(
                        t,
                        Rvalue::Bin(BinOp::Lt, Operand::Var(i), Operand::int(3)),
                    )],
                    term: Terminator::Branch {
                        cond: Operand::Var(t),
                        then_: BlockId(2),
                        else_: BlockId(3),
                    },
                    exceptional: vec![],
                },
                Block {
                    id: BlockId(2),
                    bytecode_offset: 2,
                    stmts: vec![
                        Stmt::Assign(
                            x,
                            Rvalue::Bin(BinOp::Add, Operand::Var(x), Operand::int(1)),
                        ),
                        Stmt::Assign(
                            t,
                            Rvalue::Bin(BinOp::Lt, Operand::Var(x), Operand::int(2)),
                        ),
                        Stmt::Check(ObligationId(0)),
                        Stmt::Assign(
                            i,
                            Rvalue::Bin(BinOp::Add, Operand::Var(i), Operand::int(1)),
                        ),
                    ],
                    term: Terminator::Goto(BlockId(1)),
                    exceptional: vec![],
                },
                Block {
                    id: BlockId(3),
                    bytecode_offset: 3,
                    stmts: vec![],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                },
            ],
        }
    }

    /// The regression this file exists for (#76).
    ///
    /// `smt_encode::encode_body` visits each block once in ID order, so the
    /// back-edge from B2 to B1 merges into a block that has already been
    /// processed and is dropped. The formula therefore describes exactly one
    /// pass through the loop, on which `x == 1` and the obligation holds, so
    /// the violation term is UNSAT.
    ///
    /// Reporting that UNSAT as a proof is the bug: the program does violate
    /// the assertion, on its second iteration. A step case must not claim it.
    #[test]
    fn step_case_rejects_property_that_fails_after_one_unrolling() {
        let Some(factory) = SmtLibFactory::from_env() else {
            eprintln!("no SMT solver on PATH; skipping");
            return;
        };
        let engine = KInduction::new(Box::new(factory));
        let body = loop_failing_on_second_iteration();
        assert!(
            body_has_loops(&body),
            "test fixture must have a back-edge, or it exercises the loop-free \
             path instead of the one under test"
        );
        assert_eq!(
            engine.try_step_case(&body, ObligationId(0)),
            Ok(false),
            "the step case claimed a proof for a program that violates its \
             assertion on the second iteration. One unrolling is not an \
             induction argument (#76)."
        );
    }

    /// ```text
    /// B0: if (nondet) B1 else B2
    /// B1: x = 0    -> B3
    /// B2: x = 5    -> B3
    /// B3: check(x > 0); return
    /// ```
    ///
    /// The then-path reaches the check with `x == 0` and violates it. The
    /// body is loop-free, so this isolates a *second* defect in
    /// `smt_encode::encode_body`, independent of the back-edge one: `Env::vars`
    /// is a single map that each block overwrites in turn, and `merge_pc`
    /// joins only path conditions. At B3 the encoder therefore reads whatever
    /// the last-processed predecessor assigned — B2's `x == 5` — instead of an
    /// `ite` over the two reaching definitions. The violating path is simply
    /// not in the formula.
    ///
    /// The block ids matter: with the assignments swapped the stale value
    /// happens to be the violating one and the encoder gets the right answer
    /// by luck, which is why this went unnoticed.
    fn branch_join_reads_stale_definition() -> Body {
        let (x, t) = (VarId(0), VarId(1));
        let blk = |id: u32, stmts: Vec<Stmt>, term: Terminator| Block {
            id: BlockId(id),
            bytecode_offset: id as u16,
            stmts,
            term,
            exceptional: vec![],
        };
        Body {
            key: key(),
            entry: BlockId(0),
            vars: vec![int_var(0), int_var(1)],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(t),
                bytecode_offset: 0,
                line: None,
                guarded: false,
            }],
            blocks: vec![
                blk(
                    0,
                    vec![Stmt::Assign(t, Rvalue::Nondet(Ty::Int, None))],
                    Terminator::Branch {
                        cond: Operand::Var(t),
                        then_: BlockId(1),
                        else_: BlockId(2),
                    },
                ),
                blk(
                    1,
                    vec![Stmt::Assign(x, Rvalue::Use(Operand::int(0)))],
                    Terminator::Goto(BlockId(3)),
                ),
                blk(
                    2,
                    vec![Stmt::Assign(x, Rvalue::Use(Operand::int(5)))],
                    Terminator::Goto(BlockId(3)),
                ),
                blk(
                    3,
                    vec![
                        Stmt::Assign(
                            t,
                            Rvalue::Bin(BinOp::Gt, Operand::Var(x), Operand::int(0)),
                        ),
                        Stmt::Check(ObligationId(0)),
                    ],
                    Terminator::Return(None),
                ),
            ],
        }
    }

    #[test]
    fn step_case_rejects_violation_on_an_unmerged_branch() {
        let Some(factory) = SmtLibFactory::from_env() else {
            eprintln!("no SMT solver on PATH; skipping");
            return;
        };
        let engine = KInduction::new(Box::new(factory));
        assert_eq!(
            engine.try_step_case(&branch_join_reads_stale_definition(), ObligationId(0)),
            Ok(false),
            "the step case claimed a proof for a program whose then-branch \
             violates the obligation. Reaching definitions are not joined at \
             merge points, so the violating path is missing from the formula \
             entirely (#76)."
        );
    }

    /// The same branching shape as `branch_join_reads_stale_definition`, but
    /// with both branches satisfying the obligation.
    ///
    /// Guards against the completeness gate becoming vacuous: it is easy to
    /// make an engine sound by having it decline everything, and this asserts
    /// the loop-free branching path still reaches a proof.
    #[test]
    fn step_case_proves_a_safe_branching_body() {
        let Some(factory) = SmtLibFactory::from_env() else {
            eprintln!("no SMT solver on PATH; skipping");
            return;
        };
        let mut body = branch_join_reads_stale_definition();
        // then-branch now assigns 3 rather than 0, so `x > 0` holds on both.
        body.blocks[1].stmts = vec![Stmt::Assign(VarId(0), Rvalue::Use(Operand::int(3)))];
        let engine = KInduction::new(Box::new(factory));
        assert_eq!(
            engine.try_step_case(&body, ObligationId(0)),
            Ok(true),
            "a loop-free body with no violating path should still be proved; \
             an engine that declines everything is sound and useless"
        );
    }

    /// `complete` must distinguish the two shapes, not be constantly false.
    #[test]
    fn completeness_flag_tracks_back_edges() {
        let Some(factory) = SmtLibFactory::from_env() else {
            eprintln!("no SMT solver on PATH; skipping");
            return;
        };
        let mut solver = factory.create().expect("solver");
        let looped = smt_encode::encode_body(
            solver.as_mut(),
            &loop_failing_on_second_iteration(),
            "a",
        );
        assert!(!looped.complete, "a body with a back-edge is not fully encoded");
        let flat = smt_encode::encode_body(
            solver.as_mut(),
            &branch_join_reads_stale_definition(),
            "b",
        );
        assert!(flat.complete, "a loop-free body with no handlers is fully encoded");
    }

    // ---------------------------------------------------------------
    // Heap. Before these, every heap read was a fresh unconstrained value
    // and every write was discarded, so no property depending on a stored
    // value could be proved -- the encoder could not tell
    // `benchmarks/ajave/heap/ArrayInvariantHoldsForAllElements` from
    // `ArrayInvariantViolated`.
    // ---------------------------------------------------------------

    /// A single straight-line block ending in `check`, over `nvars` locals.
    fn straight_line(stmts: Vec<Stmt>, nvars: usize, cond: VarId) -> Body {
        Body {
            key: key(),
            entry: BlockId(0),
            vars: (0..nvars).map(|i| int_var(i as u16)).collect(),
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(cond),
                bytecode_offset: 0,
                line: None,
                guarded: false,
            }],
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts,
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    fn prove(body: &Body) -> Result<bool, String> {
        let Some(factory) = SmtLibFactory::from_env() else {
            return Ok(true); // caller's assertion is skipped; see the guards
        };
        KInduction::new(Box::new(factory)).try_step_case(body, ObligationId(0))
    }

    fn have_solver() -> bool {
        SmtLibFactory::from_env().is_some()
    }

    /// `a = new int[4]; a[0] = 5; x = a[0]; assert x > 0;`
    #[test]
    fn array_store_is_visible_to_a_later_load() {
        if !have_solver() {
            return;
        }
        let (a, x, c) = (VarId(0), VarId(1), VarId(2));
        let body = straight_line(
            vec![
                Stmt::Assign(a, Rvalue::NewArray { elem: "I".into(), len: Operand::int(4) }),
                Stmt::ArrayStore {
                    arr: Operand::Var(a),
                    idx: Operand::int(0),
                    val: Operand::int(5),
                },
                Stmt::Assign(x, Rvalue::ArrayLoad {
                    arr: Operand::Var(a),
                    idx: Operand::int(0),
                }),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Gt, Operand::Var(x), Operand::int(0))),
                Stmt::Check(ObligationId(0)),
            ],
            3,
            c,
        );
        assert_eq!(prove(&body), Ok(true), "a[0] was written 5, so a[0] > 0");
    }

    /// The same shape storing 0, which does violate `a[0] > 0`. Guards against
    /// the heap being modelled as something that satisfies everything.
    #[test]
    fn array_store_of_a_violating_value_is_not_proved() {
        if !have_solver() {
            return;
        }
        let (a, x, c) = (VarId(0), VarId(1), VarId(2));
        let body = straight_line(
            vec![
                Stmt::Assign(a, Rvalue::NewArray { elem: "I".into(), len: Operand::int(4) }),
                Stmt::ArrayStore {
                    arr: Operand::Var(a),
                    idx: Operand::int(0),
                    val: Operand::int(0),
                },
                Stmt::Assign(x, Rvalue::ArrayLoad {
                    arr: Operand::Var(a),
                    idx: Operand::int(0),
                }),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Gt, Operand::Var(x), Operand::int(0))),
                Stmt::Check(ObligationId(0)),
            ],
            3,
            c,
        );
        assert_eq!(prove(&body), Ok(false), "a[0] was written 0, so a[0] > 0 fails");
    }

    /// A store at one index must not be visible at another.
    #[test]
    fn array_indices_are_separated() {
        if !have_solver() {
            return;
        }
        let (a, x, c) = (VarId(0), VarId(1), VarId(2));
        let body = straight_line(
            vec![
                Stmt::Assign(a, Rvalue::NewArray { elem: "I".into(), len: Operand::int(4) }),
                Stmt::ArrayStore {
                    arr: Operand::Var(a),
                    idx: Operand::int(0),
                    val: Operand::int(5),
                },
                Stmt::Assign(x, Rvalue::ArrayLoad {
                    arr: Operand::Var(a),
                    idx: Operand::int(1),
                }),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Gt, Operand::Var(x), Operand::int(0))),
                Stmt::Check(ObligationId(0)),
            ],
            3,
            c,
        );
        assert_eq!(
            prove(&body),
            Ok(false),
            "a[1] was never written, so nothing bounds it"
        );
    }

    /// `o = new; p = new; o.f = 1; p.f = 2; assert o.f == 1;`
    ///
    /// Two allocations are distinct objects, so the write through `p` cannot
    /// disturb `o.f`. This is what the allocation addresses buy: with fresh
    /// unconstrained references the solver could set `o == p` and the
    /// assertion would come back violable.
    #[test]
    fn distinct_allocations_do_not_alias() {
        if !have_solver() {
            return;
        }
        let (o, q, y, c) = (VarId(0), VarId(1), VarId(2), VarId(3));
        let f = FieldKey { class: "Obj".into(), name: "f".into(), desc: "I".into() };
        let body = straight_line(
            vec![
                Stmt::Assign(o, Rvalue::New("Obj".into())),
                Stmt::Assign(q, Rvalue::New("Obj".into())),
                Stmt::PutField { obj: Operand::Var(o), field: f.clone(), val: Operand::int(1) },
                Stmt::PutField { obj: Operand::Var(q), field: f.clone(), val: Operand::int(2) },
                Stmt::Assign(y, Rvalue::GetField { obj: Operand::Var(o), field: f }),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Eq, Operand::Var(y), Operand::int(1))),
                Stmt::Check(ObligationId(0)),
            ],
            4,
            c,
        );
        assert_eq!(prove(&body), Ok(true));
    }

    /// A reference the encoder did not allocate may alias anything, so a write
    /// through it has to be assumed to reach `o.f`. Soundness in the other
    /// direction: the heap must not prove things it cannot know.
    #[test]
    fn an_unknown_reference_may_alias() {
        if !have_solver() {
            return;
        }
        let (o, u, y, c) = (VarId(0), VarId(1), VarId(2), VarId(3));
        let f = FieldKey { class: "Obj".into(), name: "f".into(), desc: "I".into() };
        let body = straight_line(
            vec![
                Stmt::Assign(o, Rvalue::New("Obj".into())),
                Stmt::PutField { obj: Operand::Var(o), field: f.clone(), val: Operand::int(1) },
                // `u` is an incoming reference, not an allocation.
                Stmt::Assign(u, Rvalue::Nondet(Ty::Ref, None)),
                Stmt::PutField { obj: Operand::Var(u), field: f.clone(), val: Operand::int(2) },
                Stmt::Assign(y, Rvalue::GetField { obj: Operand::Var(o), field: f }),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Eq, Operand::Var(y), Operand::int(1))),
                Stmt::Check(ObligationId(0)),
            ],
            4,
            c,
        );
        assert_eq!(
            prove(&body),
            Ok(false),
            "u could be o, so o.f may have been overwritten with 2"
        );
    }

    /// A call that is not known to be pure can write any field, so a value
    /// stored before it cannot be relied on afterwards.
    #[test]
    fn an_opaque_call_havocs_the_heap() {
        if !have_solver() {
            return;
        }
        let (o, y, c, r) = (VarId(0), VarId(1), VarId(2), VarId(3));
        let f = FieldKey { class: "Obj".into(), name: "f".into(), desc: "I".into() };
        let body = straight_line(
            vec![
                Stmt::Assign(o, Rvalue::New("Obj".into())),
                Stmt::PutField { obj: Operand::Var(o), field: f.clone(), val: Operand::int(1) },
                Stmt::Assign(r, Rvalue::Call {
                    target: MethodKey {
                        class: "Helper".into(),
                        name: "mutate".into(),
                        desc: "()V".into(),
                    },
                    args: vec![],
                    is_virtual: false,
                }),
                Stmt::Assign(y, Rvalue::GetField { obj: Operand::Var(o), field: f }),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Eq, Operand::Var(y), Operand::int(1))),
                Stmt::Check(ObligationId(0)),
            ],
            4,
            c,
        );
        assert_eq!(prove(&body), Ok(false), "Helper.mutate may have written o.f");
    }

    // ---------------------------------------------------------------
    // Induction over the iteration count.
    // ---------------------------------------------------------------

    /// ```text
    /// B0: x = 0; i = 0;                  -> B1
    /// B1: if (i < n) B2 else B3
    /// B2: x = x + 2; check(x % 2 == 0); i = i + 1;  -> B1
    /// B3: return
    /// ```
    ///
    /// `n` is unconstrained, so no finite unrolling covers every execution.
    /// The invariant is inductive as written: 0 is even, and even + 2 is even.
    /// This is the IR of `benchmarks/ajave/kinduction/LoopInvariantNeedsInduction`.
    fn loop_with_inductive_invariant() -> Body {
        let (x, i, n, t) = (VarId(0), VarId(1), VarId(2), VarId(3));
        let blk = |id: u32, stmts: Vec<Stmt>, term: Terminator| Block {
            id: BlockId(id),
            bytecode_offset: id as u16,
            stmts,
            term,
            exceptional: vec![],
        };
        Body {
            key: key(),
            entry: BlockId(0),
            vars: vec![int_var(0), int_var(1), int_var(2), int_var(3)],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(t),
                bytecode_offset: 0,
                line: None,
                guarded: false,
            }],
            blocks: vec![
                blk(
                    0,
                    vec![
                        Stmt::Assign(x, Rvalue::Use(Operand::int(0))),
                        Stmt::Assign(i, Rvalue::Use(Operand::int(0))),
                        Stmt::Assign(n, Rvalue::Nondet(Ty::Int, None)),
                    ],
                    Terminator::Goto(BlockId(1)),
                ),
                blk(
                    1,
                    vec![Stmt::Assign(
                        t,
                        Rvalue::Bin(BinOp::Lt, Operand::Var(i), Operand::Var(n)),
                    )],
                    Terminator::Branch {
                        cond: Operand::Var(t),
                        then_: BlockId(2),
                        else_: BlockId(3),
                    },
                ),
                blk(
                    2,
                    vec![
                        Stmt::Assign(
                            x,
                            Rvalue::Bin(BinOp::Add, Operand::Var(x), Operand::int(2)),
                        ),
                        Stmt::Assign(
                            t,
                            Rvalue::Bin(BinOp::Rem, Operand::Var(x), Operand::int(2)),
                        ),
                        Stmt::Assign(
                            t,
                            Rvalue::Bin(BinOp::Eq, Operand::Var(t), Operand::int(0)),
                        ),
                        Stmt::Check(ObligationId(0)),
                        Stmt::Assign(
                            i,
                            Rvalue::Bin(BinOp::Add, Operand::Var(i), Operand::int(1)),
                        ),
                    ],
                    Terminator::Goto(BlockId(1)),
                ),
                blk(3, vec![], Terminator::Return(None)),
            ],
        }
    }

    /// The whole point of the engine: a property no bounded unrolling
    /// establishes, proved by induction on the iteration count.
    #[test]
    fn k_induction_proves_an_inductive_loop_invariant() {
        if !have_solver() {
            return;
        }
        let engine = KInduction::new(Box::new(SmtLibFactory::from_env().expect("solver")));
        assert_eq!(
            engine.try_k_induction(&loop_with_inductive_invariant(), ObligationId(0)),
            Ok(Some(1)),
            "x is even at every check: 0 is even and even + 2 is even, which is \
             an induction of depth 1"
        );
    }

    /// The counterpart. The step case is satisfiable — x = 1 survives one
    /// iteration and fails the next — so no k proves it.
    #[test]
    fn k_induction_refuses_a_loop_that_fails_on_the_second_iteration() {
        if !have_solver() {
            return;
        }
        let engine = KInduction::new(Box::new(SmtLibFactory::from_env().expect("solver")));
        assert_eq!(
            engine.try_k_induction(&loop_failing_on_second_iteration(), ObligationId(0)),
            Ok(None),
            "the base case admits a violation at the second iteration, so there \
             is nothing to prove at any depth"
        );
    }

    /// An obligation outside the loop is out of scope rather than silently
    /// proved: discharging it needs the loop's exit state.
    #[test]
    fn k_induction_declines_an_obligation_outside_the_loop() {
        if !have_solver() {
            return;
        }
        let mut body = loop_with_inductive_invariant();
        // Move the check from the loop body to the block after the loop.
        body.blocks[2].stmts.retain(|s| !matches!(s, Stmt::Check(_)));
        body.blocks[3].stmts.push(Stmt::Check(ObligationId(0)));
        let engine = KInduction::new(Box::new(SmtLibFactory::from_env().expect("solver")));
        assert_eq!(
            engine.try_k_induction(&body, ObligationId(0)),
            Ok(None),
        );
    }
}

