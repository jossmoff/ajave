//! Tier 0/1: the cheap sweep.
//!
//! Discharges obligations whose safety condition is syntactically true. That
//! sounds trivial, and it is, but on the runtime-exception property a large
//! fraction of checks guard operations on constants, and nobody in the field
//! is collecting them cleanly. Free score before any solver runs.
//!
//! This is where interval + nullness abstract interpretation grows (stage 7).
//! It is over-approximating, so the blackboard will refuse to let it emit a
//! violation no matter what it computes.

use log::{debug, info};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::{Const, Operand, Program};

pub struct Presolve {
    done: bool,
}

impl Presolve {
    pub fn new() -> Self {
        Presolve { done: false }
    }
}

impl Default for Presolve {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine for Presolve {
    fn id(&self) -> EngineId {
        EngineId("presolve")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        info!("presolve: scanning {} open obligations", bb.open().len());
        let mut advanced = false;
        let mut discharged = 0usize;
        for oref in bb.open() {
            let Some(body) = prog.body(&oref.method) else {
                continue;
            };
            let ob = body.obligation(oref.id);
            // A non-zero integer constant safety condition holds on every path,
            // so the obligation is discharged without any reachability question.
            let trivially_safe = matches!(&ob.cond, Operand::Const(Const::Int(v)) if *v != 0);
            if trivially_safe {
                debug!("presolve: trivially discharging {oref:?}");
                let _ = bb.publish(
                    self.id(),
                    self.direction(),
                    Artifact::Status(
                        oref.clone(),
                        Status::Discharged {
                            by: self.id(),
                            proof: ProofKind::Trivial,
                        },
                    ),
                );
                discharged += 1;
                advanced = true;
            }
        }
        info!("presolve: discharged {discharged} obligations trivially");

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}
