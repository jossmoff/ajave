//! Tier 1, wired up: run the interval domain to a fixpoint over the entry
//! method, then discharge every obligation whose safety condition provably
//! holds at every state that reaches it.
//!
//! Scoped deliberately to a single body (no interprocedural reasoning yet --
//! consistent with the frontend, which diverges rather than guessing at
//! unmodelled calls). Extending this across method boundaries is a `Cpa`
//! composition exercise, not a rewrite: `core::cpa::Product` exists for
//! exactly that.

use std::collections::HashMap;

use crate::interval::IntervalCpa;
use log::{debug, info};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::cpa::{reachability, HasLocation};
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::{Const, ObligationId, Operand, Program, Stmt};

pub struct AiEngine {
    done: bool,
}

impl AiEngine {
    pub fn new() -> Self {
        AiEngine { done: false }
    }
}

impl Default for AiEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine for AiEngine {
    fn id(&self) -> EngineId {
        EngineId("interval-ai")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };
        // A body we couldn't fully lift may hide obligations behind the
        // divergence. Over-approximating engines cannot see past that, so
        // nothing here is provably safe.
        if !body.is_fully_lifted() {
            return Progress::Stalled;
        }

        info!("interval-ai: starting abstract interpretation of {entry:?}");
        let start = ProgramPoint {
            method: entry.clone(),
            block: body.entry,
            index: 0,
        };
        let max_states = (budget.work as usize).max(64);
        let (reached, complete) = reachability(&IntervalCpa, prog, &start, (), max_states);

        if !complete {
            // The search was cut short. Silence at an unexplored obligation is
            // not a proof of anything -- see the doc on `cpa::reachability`.
            debug!("interval-ai: analysis incomplete at max_states={max_states}, stalling");
            return Progress::Stalled;
        }
        debug!("interval-ai: reached {} abstract states", reached.len());

        // For each obligation, every reached state sitting at its check point
        // must show the safety condition can never be false there. A single
        // state where it *could* be false (interval includes zero) rules the
        // obligation out.
        //
        // Crucially: an obligation the search never reaches at all is *also*
        // safe, not merely unassessed. `reachability` returned `complete`,
        // meaning this is a sound over-approximation of every real execution
        // -- so if the abstract search never sets foot at a check point, no
        // concrete execution can either. That's the case that actually fires
        // here on stage01/02: once `v3 > 3` is proven always true, the branch
        // to the `AssertionError` path narrows to a bottom state and is
        // pruned outright, so its `Check` is never visited. Starting every
        // obligation at `true` and only falsifying it on an actual sighting
        // is what lets that count as the proof it is, instead of silently
        // sitting at Open forever because nothing ever "saw" it.
        let mut safe: HashMap<ObligationId, bool> =
            body.obligations.iter().map(|o| (o.id, true)).collect();

        for state in &reached {
            let loc = state.location();
            if loc.method != *entry {
                continue;
            }
            let Some(Stmt::Check(oid)) = body.block(loc.block).stmts.get(loc.index) else {
                continue;
            };
            let ob = body.obligation(*oid);
            let cond_ok = match &ob.cond {
                Operand::Const(Const::Int(v)) => *v != 0,
                _ => state.eval_operand(&ob.cond).definitely_nonzero(),
            };
            let entry_flag = safe.entry(*oid).or_insert(true);
            *entry_flag = *entry_flag && cond_ok;
        }

        let safe_count = safe.values().filter(|&&v| v).count();
        debug!(
            "interval-ai: {safe_count}/{} obligations proved safe by interval analysis",
            safe.len()
        );

        let mut advanced = false;
        for (oid, is_safe) in safe {
            if !is_safe {
                continue;
            }
            let oref = ObligationRef {
                method: entry.clone(),
                id: oid,
            };
            debug!("interval-ai: discharging {oref:?}");
            let inv_id = bb.fresh_invariant_id();
            let published = bb.publish(
                self.id(),
                self.direction(),
                Artifact::Status(
                    oref,
                    Status::Discharged {
                        by: self.id(),
                        proof: ProofKind::Invariant(inv_id),
                    },
                ),
            );
            if published.is_ok() {
                advanced = true;
            }
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}
