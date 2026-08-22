//! What engines exchange.
//!
//! The intended design: engines publish *artifacts*, not verdicts. A portfolio
//! that only exchanges verdicts discards everything each engine learned on the
//! way, which is most of the value.
//!
//! **What is actually built today is narrower than that, and the gap is worth
//! stating plainly rather than leaving a reader to infer it from grep.** Every
//! engine publishes exactly one artifact kind, `Status`, and reads shared state
//! through exactly one method, `Blackboard::open`. The cursor API
//! (`Blackboard::since` / `head`), which is what would let an engine pull
//! another's deltas without coupling to it, has no callers. Neither do
//! `Invariant`, `Trace`, `Precision` or `Residual` -- nothing constructs them,
//! so nothing consumes them.
//!
//! They are kept because the shapes are right and the first real consumer is
//! identifiable: CEGAR already computes both a spurious-trace and a refined
//! precision on every refinement round, and throws both away (see
//! `docs/strategies/cegar.md`). Publishing those is the obvious first use.
//! Until something does, treat this module as a designed interface with one
//! implemented case, not as a description of how the portfolio currently
//! communicates.

use roast_ir::verdict::Witness;
use roast_ir::{BlockId, MethodKey, ObligationId, VarId};

/// Which way an artifact's producer approximates. This is the safety-critical
/// tag in the whole system: it decides what a consumer is entitled to conclude.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Direction {
    /// Over-approximates reachable states. May prove safety, never a bug.
    Over,
    /// Under-approximates reachable states. May exhibit a bug, never safety.
    Under,
    /// Exact: sound in both directions, so entitled to both discharge and
    /// violate. The frontend and the certifier claim this, and so does an
    /// engine whose reasoning is exact under conditions it checks for itself --
    /// `smt_bmc` exhibits bugs from concrete witnesses (an under-approximating
    /// justification) and proves safety from exhaustive path coverage (an
    /// over-approximating one), tagging each artifact with whichever justifies
    /// it. See `Blackboard::register_engine`.
    Exact,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct EngineId(pub &'static str);

impl std::fmt::Display for EngineId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ObligationRef {
    pub method: MethodKey,
    pub id: ObligationId,
}

impl std::fmt::Display for ObligationRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}#{}", self.method, self.id.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProgramPoint {
    pub method: MethodKey,
    pub block: BlockId,
    /// Index into the block's statements; `stmts.len()` means "at terminator".
    pub index: usize,
}

/// How an obligation was discharged. Carried so the certifier can re-check it
/// independently rather than taking the engine's word.
#[derive(Clone, Debug)]
pub enum ProofKind {
    /// Discharged syntactically: the safety condition is a true constant.
    Trivial,
    /// Discharged by an invariant that must itself be checked inductively.
    Invariant(u32),
    /// Discharged by k-induction at the given depth.
    KInduction { k: u32 },
    /// The state space below this point was explored exhaustively.
    Exhaustive,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum InvStatus {
    /// Proposed but not yet checked. Never enough on its own to discharge.
    Candidate,
    /// Verified initial-and-preserved by the certifier.
    Inductive,
}

#[derive(Clone, Debug)]
pub struct Invariant {
    pub id: u32,
    pub at: ProgramPoint,
    /// Placeholder for a real term IR. A string is fine while the consumers are
    /// stubs, and deliberately painful enough that it will get replaced before
    /// anything depends on it structurally.
    pub formula: String,
    pub status: InvStatus,
}

#[derive(Clone, Debug, Default)]
pub struct Precision {
    pub predicates: Vec<String>,
    pub tracked: Vec<VarId>,
}

/// A path through the CFG that some engine considers suspect. `feasible` is
/// `None` until something decides; `Some(false)` makes it refinement material.
#[derive(Clone, Debug)]
pub struct AbstractTrace {
    pub obligation: ObligationRef,
    pub path: Vec<(BlockId, Option<bool>)>,
    pub feasible: Option<bool>,
}

/// Conditional model checking: the region of the state space a giving-up engine
/// already covered, so the next engine only has to analyse the residual.
#[derive(Clone, Debug)]
pub struct Condition {
    pub covered: Vec<ProgramPoint>,
    pub note: String,
}

#[derive(Clone, Debug)]
pub enum Status {
    Open,
    /// BMC reached depth `k` without a hit. Not a proof; a fact about effort,
    /// and the precondition for k-induction to take over.
    Bounded {
        k: u32,
    },
    Discharged {
        by: EngineId,
        proof: ProofKind,
    },
    Violated {
        by: EngineId,
        witness: Witness,
    },
    Unknown {
        reason: String,
    },
}

impl Status {
    pub fn is_final(&self) -> bool {
        matches!(self, Status::Discharged { .. } | Status::Violated { .. })
    }
}

#[derive(Clone, Debug)]
pub enum Artifact {
    Status(ObligationRef, Status),
    Invariant(Invariant),
    Precision(ProgramPoint, Precision),
    Trace(AbstractTrace),
    Residual(Condition),
}

#[derive(Clone, Debug)]
pub struct Tagged {
    pub seq: u64,
    pub producer: EngineId,
    pub direction: Direction,
    pub artifact: Artifact,
}
