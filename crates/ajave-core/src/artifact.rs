//! What engines exchange.
//!
//! The central idea of the architecture: engines publish *artifacts*, not
//! verdicts. A portfolio that only exchanges verdicts discards everything each
//! engine learned on the way, which is most of the value.

use ajave_ir::verdict::Witness;
use ajave_ir::{BlockId, MethodKey, ObligationId, VarId};

/// Which way an artifact's producer approximates. This is the safety-critical
/// tag in the whole system: it decides what a consumer is entitled to conclude.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Direction {
    /// Over-approximates reachable states. May prove safety, never a bug.
    Over,
    /// Under-approximates reachable states. May exhibit a bug, never safety.
    Under,
    /// Exact. Only the frontend and the certifier get to claim this.
    Exact,
}

/// Which parts of the JVM's semantics an artifact's producer did *not* model
/// faithfully.
///
/// `Direction` says what a consumer may conclude from an artifact. It does not
/// say whether the producer's encoding was a model of *this* program, and those
/// are different questions. An engine that encodes `dmul` as a bitvector
/// multiply is still honestly under-approximating — it just under-approximates
/// a program that is not ours.
///
/// Both defects found on 2026-09-04 sit in that gap. The cheap BMC pass encodes
/// float arithmetic as bitvector arithmetic by default, published a violation
/// derived from it, and thereby closed the obligation — so the FPA pass, which
/// exists precisely to decide those, skipped the task because nothing was
/// `open()`. Replay refuted the witness and nothing reopened it.
///
/// Recording what was approximated turns that into a condition a consumer can
/// test: an engine asks for the obligations *it* can do better on, rather than
/// only the ones nobody has touched. See `Blackboard::open_for`.
///
/// A bitset rather than a `BTreeSet`, so it stays `Copy` and rides along in
/// `Tagged` without allocating on every publish.
#[derive(Clone, Copy, PartialEq, Eq, Default, Hash, PartialOrd, Ord)]
pub struct Approximations(u16);

impl Approximations {
    /// The producer modelled everything it touched.
    pub const EXACT: Approximations = Approximations(0);

    /// IEEE-754 arithmetic encoded as bitvector arithmetic on the bit
    /// patterns. Comparisons survive this — `dcmpg`/`dcmpl` are a total order
    /// on the patterns — but `dadd`/`dmul` and friends do not.
    pub const FLOAT_ARITH: Approximations = Approximations(1 << 0);

    /// Floats encoded as mathematical reals. Sound over ℝ, and ℝ is not
    /// IEEE-754: no NaN, no infinities, no rounding, no signed zero.
    pub const REAL_ARITH: Approximations = Approximations(1 << 1);

    /// Machine integers encoded as unbounded `Int`, so nothing wraps.
    pub const INT_WRAPPING: Approximations = Approximations(1 << 2);

    /// The heap modelled per-variable rather than through an addressable
    /// store, so a write through one alias is invisible to another name.
    pub const HEAP_ALIASING: Approximations = Approximations(1 << 3);

    pub const fn union(self, other: Approximations) -> Approximations {
        Approximations(self.0 | other.0)
    }

    /// Does this set include everything in `other`?
    pub const fn contains(self, other: Approximations) -> bool {
        self.0 & other.0 == other.0
    }

    /// Do the two sets overlap at all?
    pub const fn intersects(self, other: Approximations) -> bool {
        self.0 & other.0 != 0
    }

    pub const fn is_exact(self) -> bool {
        self.0 == 0
    }
}

impl std::fmt::Debug for Approximations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_exact() {
            return f.write_str("exact");
        }
        let mut first = true;
        for (bit, name) in [
            (Self::FLOAT_ARITH, "float-arith"),
            (Self::REAL_ARITH, "real-arith"),
            (Self::INT_WRAPPING, "int-wrapping"),
            (Self::HEAP_ALIASING, "heap-aliasing"),
        ] {
            if self.contains(bit) {
                if !first {
                    f.write_str("+")?;
                }
                f.write_str(name)?;
                first = false;
            }
        }
        Ok(())
    }
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
    /// What the producer did not model faithfully while deriving this.
    pub approximated: Approximations,
    pub artifact: Artifact,
}

/// Where a given obligation's `Check` statement lives, as a `ProgramPoint`.
///
/// This lives here rather than as a method on `ajave_ir::Body` because
/// `ProgramPoint` is a `ajave-core` type: `ajave-ir` has zero dependencies by
/// design (every other crate depends on it, never the reverse), so anything
/// that needs to hand back a core-crate type has to live on the core side of
/// that boundary, even though it's `Body`'s data it's walking.
pub fn check_point(body: &ajave_ir::Body, id: ajave_ir::ObligationId) -> Option<ProgramPoint> {
    for b in &body.blocks {
        for (i, s) in b.stmts.iter().enumerate() {
            if let ajave_ir::Stmt::Check(cid) = s {
                if *cid == id {
                    return Some(ProgramPoint {
                        method: body.key.clone(),
                        block: b.id,
                        index: i,
                    });
                }
            }
        }
    }
    None
}
