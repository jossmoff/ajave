//! The schedule.
//!
//! Falsify before prove: bugs are cheap to find and cheap to certify, and one
//! ends the task immediately. Proofs are expensive and only worth starting once
//! the cheap exit is closed off.

use crate::blackboard::Blackboard;
use crate::engine::{Budget, Engine, Progress};
use log::{debug, info};
use roast_ir::verdict::Verdict;
use roast_ir::Program;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    Presolve,
    Falsify,
    Prove,
    Refine,
    Report,
}

pub struct Orchestrator {
    pub engines: Vec<Box<dyn Engine>>,
    pub bb: Blackboard,
    pub phase: Phase,
    pub budget: Budget,
    pub trace: Vec<String>,
    pub assertion_only: bool,
}

impl Orchestrator {
    pub fn new(engines: Vec<Box<dyn Engine>>) -> Self {
        Orchestrator {
            engines,
            bb: Blackboard::new(),
            phase: Phase::Presolve,
            budget: Budget::default(),
            trace: Vec::new(),
            assertion_only: true,
        }
    }

    pub fn run(&mut self, prog: &Program, max_rounds: usize) -> Verdict {
        info!(
            "orchestrator: starting with {} engines, max_rounds={}",
            self.engines.len(),
            max_rounds
        );
        self.bb.seed(prog, self.assertion_only);
        for e in self.engines.iter_mut() {
            debug!("orchestrator: initialising engine {}", e.id());
            // Register before init so the direction discipline is armed for
            // anything an engine publishes during initialisation.
            self.bb.register_engine(e.id(), e.direction());
            e.init(prog, &mut self.bb);
        }

        let mut retired = vec![false; self.engines.len()];

        for round in 0..max_rounds {
            if self.phase == Phase::Report {
                break;
            }

            let mut advanced = false;
            for (i, e) in self.engines.iter_mut().enumerate() {
                if retired[i] {
                    continue;
                }
                // Short-circuit: if a violation was already found by a
                // previous engine in this round, skip remaining engines.
                if self.bb.any_violated() {
                    break;
                }
                match e.step(prog, &mut self.bb, self.budget) {
                    Progress::Advanced => advanced = true,
                    Progress::Stalled => {}
                    Progress::Exhausted => {
                        debug!("orchestrator: engine {} exhausted, retiring", e.id());
                        retired[i] = true;
                    }
                }
            }

            let open = self.bb.open_count();
            let violated = self.bb.any_violated();

            let msg = format!(
                "round {round}: phase={:?} open={open} advanced={advanced}",
                self.phase
            );
            debug!("orchestrator: {msg}");
            self.trace.push(msg);

            self.phase = self.next_phase(open, violated, advanced, retired.iter().all(|r| *r));
        }

        let verdict = self.bb.verdict();
        info!("orchestrator: done, verdict={verdict:?}");
        verdict
    }

    /// The schedule state machine from ARCHITECTURE.md section 4.
    fn next_phase(&self, open: usize, violated: bool, advanced: bool, all_retired: bool) -> Phase {
        if violated || open == 0 || all_retired {
            return Phase::Report;
        }
        match self.phase {
            Phase::Presolve => Phase::Falsify,
            Phase::Falsify => {
                if advanced {
                    Phase::Falsify
                } else {
                    Phase::Prove
                }
            }
            Phase::Prove => {
                if advanced {
                    Phase::Prove
                } else {
                    Phase::Refine
                }
            }
            Phase::Refine => {
                if advanced {
                    Phase::Falsify
                } else {
                    Phase::Report
                }
            }
            Phase::Report => Phase::Report,
        }
    }
}
