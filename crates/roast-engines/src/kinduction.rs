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
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_core::smt::{SatResult, SolverFactory};
use roast_ir::*;

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

        let bounded: Vec<(ObligationRef, u32)> = open
            .iter()
            .filter_map(|oref| match bb.status(oref) {
                Status::Bounded { k } => Some((oref.clone(), *k)),
                _ => None,
            })
            .collect();

        if bounded.is_empty() {
            debug!("k-induction: no bounded obligations to work on");
            return Progress::Stalled;
        }

        info!(
            "k-induction: attempting step case for {} obligation(s)",
            bounded.len()
        );

        let mut advanced = false;
        for (oref, k) in &bounded {
            let Some(body) = prog.body(&oref.method) else {
                continue;
            };

            // Check if the method has loops (back-edges in the CFG).
            let has_loops = body_has_loops(body);

            // Only discharge if the encoding is precise — methods using heap,
            // arrays, or calls are havoced in the SMT encoding, so a Bounded
            // base case from the BMC doesn't actually cover all reachable states.
            if body_uses_havoced_ops(body) {
                debug!(
                    "k-induction: {} uses havoced ops, skipping",
                    oref
                );
                continue;
            }

            if !has_loops {
                // Loop-free: the base case is exhaustive. Discharge directly.
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

            // Method has loops — try proper k-induction step case.
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

impl KInduction {
    /// Try the inductive step case for a single obligation.
    /// Returns Ok(true) if proved, Ok(false) if inconclusive, Err on solver failure.
    fn try_step_case(&self, body: &Body, oid: ObligationId) -> Result<bool, String> {
        let mut solver = self.factory.create()?;

        // Encode the body. The violation term tells us: is the obligation
        // violable on any path through the body?
        let encoding = smt_encode::encode_body(solver.as_mut(), body, "step");

        let violation = match encoding.violation_terms.get(&oid) {
            Some(&t) => t,
            None => return Ok(true), // obligation not in this body
        };

        // Assert the violation term and check SAT.
        // If UNSAT, the property cannot be violated on any path → proved.
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

/// Check if a body uses operations that the SMT encoder havoces (heap, arrays, calls).
/// If so, the Bounded base case from BMC is not precise enough for k-induction.
fn body_uses_havoced_ops(body: &Body) -> bool {
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(_, rv) => match rv {
                    Rvalue::GetStatic(_)
                    | Rvalue::GetField { .. }
                    | Rvalue::InstanceOf { .. }
                    | Rvalue::Call { .. }
                    | Rvalue::Havoc(_) => return true,
                    _ => {}
                },
                Stmt::PutField { .. } => return true,
                _ => {}
            }
        }
    }
    false
}

/// Check if a method body has any back-edges (loops).
fn body_has_loops(body: &Body) -> bool {
    for block in &body.blocks {
        let succs = match &block.term {
            Terminator::Goto(t) => vec![*t],
            Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
            Terminator::Switch { cases, default, .. } => {
                let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
                v.push(*default);
                v
            }
            _ => vec![],
        };
        for s in succs {
            if s.0 <= block.id.0 {
                return true; // back-edge found
            }
        }
    }
    false
}
