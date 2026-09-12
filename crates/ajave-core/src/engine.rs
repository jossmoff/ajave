//! The engine abstraction.
//!
//! An engine is a state machine that does a bounded amount of work per `step`
//! and communicates only through the blackboard. That constraint is what makes
//! the portfolio schedulable and makes any engine removable without the others
//! noticing.

use crate::artifact::{Direction, EngineId, Interest};
use crate::blackboard::Blackboard;
use ajave_ir::Program;

/// What a `step` achieved. The orchestrator schedules on this.
///
/// The three-way version of this enum had one arm, `Stalled`, meaning "ran,
/// learned nothing, but could do more with a bigger budget" — which is two
/// states wearing one name. An engine that stopped on the clock with work
/// outstanding wants a fresh slice immediately and needs no new information; an
/// engine that ran out of *information* wants to be left alone until its inputs
/// change. They want opposite scheduling, and conflating them is why the round
/// loop could never do anything useful: every engine also set `done = true`
/// before returning `Stalled`, so the only honest reading was the second.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Progress {
    /// Published something new.
    Advanced,
    /// Stopped on the clock with work outstanding. Re-entering with a fresh
    /// slice makes strictly more progress on the *same* inputs, so the
    /// scheduler re-enters without waiting for anything to change.
    ///
    /// **Contract.** An engine may return this only if its next entry runs at a
    /// strictly higher setting of a *bounded* precision parameter. That is what
    /// makes the loop terminate when there is no deadline, which is how every
    /// unit test and most `just` recipes invoke the tool. An engine that
    /// suspends without advancing anything would otherwise spin to
    /// `max_rounds` on every task.
    Suspended,
    /// Ran, learned nothing, and more time alone will not help. Re-entered only
    /// once something matching `interest()` has been published.
    Blocked,
    /// Will never publish again. The orchestrator retires it.
    Exhausted,
}

#[derive(Clone, Copy, Debug)]
pub struct Budget {
    /// Soft cap on units of work per `step`. Units are engine-defined —
    /// unrolling depth, states explored, solver calls.
    pub work: u64,
    /// When this step must stop, in wall-clock time.
    ///
    /// `work` alone cannot bound a step: the BMC counts solver calls, and one
    /// solver call may take a minute. Measured over 20 sampled tasks that hit
    /// the 60s budget, **`smt-bmc` held the process on 18 of 18** — so `chc`,
    /// `k-induction`, `imc` and `cegar` never ran at all on exactly the tasks
    /// that needed a different angle.
    ///
    /// `None` means unbounded, which is the behaviour when no `--timeout` is
    /// given and keeps every existing invocation identical.
    pub deadline: Option<std::time::Instant>,
}

impl Budget {
    /// Whether the wall-clock slice for this step is spent.
    pub fn expired(&self) -> bool {
        self.deadline
            .is_some_and(|d| std::time::Instant::now() >= d)
    }
}

impl Default for Budget {
    fn default() -> Self {
        Budget {
            work: 1_000,
            deadline: None,
        }
    }
}

/// Whether engines may return `Progress::Suspended` at all.
///
/// An ablation switch, not a tuning knob. The scheduler (`Progress`, `Interest`,
/// cursors) and the resumption built on top of it are separable changes with
/// very different risk profiles: the first only ever removes work, while the
/// second adds a bounded amount and could in principle push a task over the
/// timeout cliff. A single number for both cannot say whether the second earns
/// its keep, and `AJAVE_RESUME=0` is how that gets measured rather than argued.
pub fn resumption_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_RESUME").as_deref() != Ok("0"))
}

pub trait Engine {
    fn id(&self) -> EngineId;

    /// Declares what this engine is entitled to conclude. The blackboard
    /// enforces it on every publish.
    fn direction(&self) -> Direction;

    /// Called once before scheduling begins.
    fn init(&mut self, _prog: &Program, _bb: &mut Blackboard) {}

    /// What this engine reads from the blackboard.
    ///
    /// A `Progress::Blocked` engine is re-entered only once an artifact
    /// matching this set has been published since its last step. The default is
    /// the widest set because under-declaring loses answers silently while
    /// over-declaring costs one wasted step — the same asymmetry `Approximations`
    /// is governed by.
    ///
    /// Declaring `Interest::NOTHING` says the engine works from the program
    /// alone. That is true of every under-approximating engine here, and it is
    /// what lets the round loop skip them instead of paying for a step that
    /// re-derives the same answer.
    fn interest(&self) -> Interest {
        Interest::ANY
    }

    /// Do a bounded slice of work. Engines read deltas via their own cursor
    /// into the blackboard, so they pick up other engines' artifacts without
    /// any direct coupling.
    fn step(&mut self, prog: &Program, bb: &mut Blackboard, budget: Budget) -> Progress;
}
