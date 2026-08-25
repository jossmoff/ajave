//! The engine abstraction.
//!
//! An engine is a state machine that does a bounded amount of work per `step`
//! and communicates only through the blackboard. That constraint is what makes
//! the portfolio schedulable and makes any engine removable without the others
//! noticing.

use crate::artifact::{Direction, EngineId};
use crate::blackboard::Blackboard;
use ajave_ir::Program;

/// What a `step` achieved. The orchestrator schedules on this.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Progress {
    /// Published something new.
    Advanced,
    /// Ran, learned nothing, but could do more with a bigger budget.
    Stalled,
    /// Will never publish again. The orchestrator retires it.
    Exhausted,
}

#[derive(Clone, Copy, Debug)]
pub struct Budget {
    /// Soft cap on units of work per `step`. Units are engine-defined —
    /// unrolling depth, states explored, solver calls.
    pub work: u64,
}

impl Default for Budget {
    fn default() -> Self {
        Budget { work: 1_000 }
    }
}

pub trait Engine {
    fn id(&self) -> EngineId;

    /// Declares what this engine is entitled to conclude. The blackboard
    /// enforces it on every publish.
    fn direction(&self) -> Direction;

    /// Called once before scheduling begins.
    fn init(&mut self, _prog: &Program, _bb: &mut Blackboard) {}

    /// Do a bounded slice of work. Engines read deltas via their own cursor
    /// into the blackboard, so they pick up other engines' artifacts without
    /// any direct coupling.
    fn step(&mut self, prog: &Program, bb: &mut Blackboard, budget: Budget) -> Progress;
}
