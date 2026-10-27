//! What engines exchange.
//!
//! The central idea of the architecture: engines publish *artifacts*, not
//! verdicts. A portfolio that only exchanges verdicts discards everything each
//! engine learned on the way, which is most of the value.

use crate::term::Expr;
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
    ///
    /// # Parked: no producer, and the reason is worth keeping
    ///
    /// Nothing in the tree sets this, and an attempt to make `interval-ai` set
    /// it (#99) established why. This flag describes an **unsound** scheme —
    /// losing a write — and no engine here has that defect:
    ///
    /// * `interval`'s field cells are flat (one per `(class, name, desc)`,
    ///   receiver ignored), but a non-strong update **joins**
    ///   (`IState::set_field`), and an absent cell reads as Top. Every heap
    ///   fact it holds is an over-approximation, so it never closes an
    ///   obligation on a too-narrow one. A strong update is taken only for a
    ///   static or a proven-singleton class, where it is exact.
    /// * `chc` reads array and field contents as unconstrained values, which
    ///   is the same widening.
    ///
    /// So their heap limitation is **imprecision, not unfaithfulness**, and
    /// `Approximations` is the vocabulary for the second. The right vocabulary
    /// for "a better heap would let me prove more" is `Artifact::Precision` —
    /// which also has no producer.
    ///
    /// Kept rather than deleted because an engine *could* acquire this defect:
    /// a site-indexed abstraction that reads a cell no write reached would
    /// have exactly it. That is the risk H3 of
    /// `docs/proposals/heap-theory.md` carries, and this flag is where it
    /// would be declared.
    pub const HEAP_ALIASING: Approximations = Approximations(1 << 3);

    /// Heap *reads* return a value narrower than the program permits.
    ///
    /// # Parked: no producer
    ///
    /// Not to be confused with reading Top, which is what `chc` and `interval`
    /// actually do and which is a sound widening. This is for an engine that
    /// claims to know a cell's contents and is wrong — which nothing here does
    /// yet, and which H4 of `docs/proposals/heap-theory.md` could introduce by
    /// threading heap state through Horn clauses incorrectly. The previous
    /// attempt at that (#95) used an uninterpreted predicate in a clause body
    /// that the solver could read as empty, making the read path vacuously
    /// safe; that is precisely this flag's situation.
    ///
    /// Distinct from `HEAP_ALIASING`, which is about *identity* — an engine
    /// that keys cells per-object but still cannot say what is in them has
    /// fixed the second and not the first. `open_for` requires a caller to fix
    /// everything that went wrong, not merely something, so handing a
    /// contents-blind engine an obligation lost to aliasing is pure cost.
    pub const HEAP_NO_CONTENTS: Approximations = Approximations(1 << 5);

    /// No reasoning about shape: acyclicity, disjointness, reachability
    /// through a linked structure.
    ///
    /// # Parked: no producer
    ///
    /// Array theory cannot express these, so no engine here reasons about
    /// shape — but none *claims* to either, and an engine that leaves a
    /// shape-dependent obligation open has not approximated anything. It would
    /// be declared by an engine that discharged such an obligation while
    /// assuming acyclicity, which H6 of `docs/proposals/heap-theory.md` would
    /// be the first to do.
    pub const HEAP_NO_SHAPE: Approximations = Approximations(1 << 6);

    /// A call whose behaviour we do not model at all, replaced by a fresh
    /// unconstrained value. No encoding fixes this — only a model of the
    /// callee does — which is what makes it worth distinguishing from the
    /// others. An engine offering a more faithful *encoding* cannot improve on
    /// an obligation that failed for this reason.
    pub const UNMODELLED_CALL: Approximations = Approximations(1 << 4);

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

    /// What is in `self` but not in `other`.
    pub const fn difference(self, other: Approximations) -> Approximations {
        Approximations(self.0 & !other.0)
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
            (Self::HEAP_NO_CONTENTS, "heap-no-contents"),
            (Self::HEAP_NO_SHAPE, "heap-no-shape"),
            (Self::UNMODELLED_CALL, "unmodelled-call"),
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

/// Which kinds of artifact an engine reads.
///
/// The scheduler re-enters a `Progress::Blocked` engine only once something
/// matching its interest has been published since its last step. Without that
/// test the round loop is unaffordable: thirteen engines re-deriving the same
/// answers every round spends the deadline and changes nothing.
///
/// The discipline is the one `Approximations` already states, with the signs
/// swapped. Under-declaring means an engine never learns the thing that would
/// unblock it, and that is silent. Over-declaring costs one wasted step. So the
/// default is the widest set, and an engine narrows it deliberately.
///
/// A bitset over `Artifact` variants rather than over producers: "who told me"
/// is exactly the coupling the blackboard exists to remove.
#[derive(Clone, Copy, PartialEq, Eq, Default, Hash, PartialOrd, Ord)]
pub struct Interest(u8);

impl Interest {
    /// Reads nothing from the board. A one-shot engine that works from the
    /// program alone declares this and is never re-entered while blocked.
    pub const NOTHING: Interest = Interest(0);

    pub const STATUS: Interest = Interest(1 << 0);
    pub const INVARIANT: Interest = Interest(1 << 1);
    pub const PRECISION: Interest = Interest(1 << 2);
    pub const TRACE: Interest = Interest(1 << 3);
    pub const RESIDUAL: Interest = Interest(1 << 4);
    pub const QUERY: Interest = Interest(1 << 5);
    pub const LEMMA: Interest = Interest(1 << 6);

    /// Every kind. The default, because over-declaring is the cheap mistake.
    pub const ANY: Interest = Interest(0x7f);

    pub const fn union(self, other: Interest) -> Interest {
        Interest(self.0 | other.0)
    }

    pub const fn intersects(self, other: Interest) -> bool {
        self.0 & other.0 != 0
    }

    pub const fn is_nothing(self) -> bool {
        self.0 == 0
    }
}

impl std::fmt::Debug for Interest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_nothing() {
            return f.write_str("nothing");
        }
        let mut first = true;
        for (bit, name) in [
            (Self::STATUS, "status"),
            (Self::INVARIANT, "invariant"),
            (Self::PRECISION, "precision"),
            (Self::TRACE, "trace"),
            (Self::RESIDUAL, "residual"),
            (Self::QUERY, "query"),
            (Self::LEMMA, "lemma"),
        ] {
            if self.intersects(bit) {
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

/// What an artifact's variable references are relative to.
///
/// The field `docs/contracts.md` Part I identified as missing. Heap work is
/// what forces it: a `VarId` indexes exactly one `Body`, but `o.f` means the
/// same cell in every method, so the two cannot share a scope. A consumer
/// reading a method-relative claim as a global one is the defect class
/// `CLAUDE.md` records as having cost 32 points.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Scope {
    /// True of every execution of the whole program.
    Execution,
    /// `VarId`s are relative to this method's `Body`.
    Method(MethodKey),
    /// As `Method`, and only at this point.
    Point(ProgramPoint),
    /// About heap cells, which are global. Mentions no `VarId` that needs a
    /// method to interpret it — a `Field`'s receiver is itself an expression.
    Heap,
}

#[derive(Clone, Debug)]
pub struct Invariant {
    pub id: u32,
    pub at: ProgramPoint,
    /// What holds at `at`, on every execution that reaches it.
    ///
    /// `VarId` is relative to `at.method`'s body, so a consumer looking at a
    /// different body must not read this — see `Expr::vars`.
    pub formula: Expr,
    pub status: InvStatus,
    /// What `formula`'s variable references are relative to.
    ///
    /// `Scope::Point(at)` is the historical behaviour and what every producer
    /// meant before this existed; a heap claim must say `Scope::Heap` instead,
    /// because its truth does not depend on which method is executing.
    pub scope: Scope,
}

#[derive(Clone, Debug, Default)]
pub struct Precision {
    pub predicates: Vec<Expr>,
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

/// What kind of answer would help.
///
/// Separate from the question itself because the same term admits different
/// useful answers, and because *who may answer* depends on which is wanted:
/// a universal claim needs an over-approximating engine, an existential one
/// needs an under-approximating engine. That is the same discipline
/// `Direction` already enforces on `Status`, applied one level down.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Want {
    /// Numeric bounds on the term. Universal: needs Over.
    Bounds,
    /// Can this reference be null here? Universal: needs Over.
    ///
    /// Added because no-runtime-exception is more than half the total score and
    /// its content is almost entirely nullness, which previously could not be
    /// asked. Engines routed around it privately: a hardcoded static list in
    /// `interval.rs`, a lifter special case for constructor parameters, a
    /// program-level fallback in `eval_nullness`. Each is a private answer to a
    /// question several engines could answer.
    NonNull,
    /// Does the predicate hold on every reaching execution? Universal.
    Valid,
    /// Is there an assignment making it true? Existential: needs Under.
    Satisfiable,
}

/// A question one engine wants another to answer.
///
/// The point of the whole mechanism. Without it a stuck engine has exactly one
/// move — give up on the obligation, conservatively — and everything it had
/// established on the way is discarded. When the BMC meets `Math.sin(x)` it
/// knows `x` is constrained and the path is feasible, and throws all of it away
/// because there is nobody to ask.
///
/// It also changes what a specialised engine *is*. Today one is an alternative
/// to the others, so an engine that understood transcendentals would have to
/// reimplement heaps, strings and inlining before it could help. As an answerer
/// it only has to answer the question it is good at.
#[derive(Clone, Debug)]
pub struct Query {
    pub id: u32,
    pub asked_by: EngineId,
    /// Where the question arose. Fixes what the `VarId`s in `about` and
    /// `given` mean; a `VarId` indexes exactly one `Body`.
    pub at: ProgramPoint,
    pub about: Expr,
    pub want: Want,
    /// What the asker already knows and the answerer may assume. An answer
    /// derived from these is only as good as they are, so the asker must
    /// supply facts it is itself entitled to.
    pub given: Vec<Expr>,
}

/// What an answerer found.
#[derive(Clone, Debug)]
pub enum Answer {
    /// `lo <= about <= hi` on every reaching execution.
    Bounds { lo: Expr, hi: Expr },
    /// The predicate holds on every reaching execution.
    Holds,
    /// It does not hold, and here is a reaching assignment that shows it.
    RefutedBy(Vec<(VarId, i64)>),
    /// An assignment satisfying it.
    SatisfiedBy(Vec<(VarId, i64)>),
    /// The reference is not null on any reaching execution.
    ///
    /// **The most dangerous answer in this enum.** A wrong one discharges a
    /// NullDeref that can really fire — a wrong TRUE at -16. `CLAUDE.md`
    /// records the specific trap: `System.out` looks like a non-null
    /// `static final` and is mutable through `System.setOut(null)`, so it does
    /// not qualify. An answerer must justify this from a contract, keyed on the
    /// full `(class, name, desc)` signature, and validated against a real JVM
    /// with adversarial inputs — not from a lattice result that happens to be
    /// convenient.
    NonNull,
    /// Asked and could not say. Worth publishing: it stops the scheduler
    /// asking the same engine the same question again.
    Unknown,
}

impl Answer {
    /// Does asserting this require a claim about *every* execution?
    ///
    /// The publish rule turns on exactly this: a universal answer from an
    /// under-approximating engine would be a proof from an engine that has
    /// only ever looked at some of the paths.
    pub fn is_universal(&self) -> bool {
        matches!(
            self,
            Answer::Bounds { .. } | Answer::Holds | Answer::NonNull
        )
    }
}

/// An answer to a `Query`.
#[derive(Clone, Debug)]
pub struct Lemma {
    pub query: u32,
    pub by: EngineId,
    pub answer: Answer,
}

#[derive(Clone, Debug)]
pub enum Artifact {
    Status(ObligationRef, Status),
    Invariant(Invariant),
    Precision(ProgramPoint, Precision),
    Trace(AbstractTrace),
    Residual(Condition),
    /// A question. Publishing one costs nothing and commits to nothing.
    Query(Query),
    /// An answer. Governed by `Direction` exactly as a `Status` is.
    Lemma(Lemma),
}

impl Artifact {
    /// Which `Interest` bit this artifact satisfies.
    ///
    /// One arm per variant on purpose: adding a variant should not silently
    /// become invisible to every engine that declared a narrow interest.
    pub fn interest(&self) -> Interest {
        match self {
            Artifact::Status(..) => Interest::STATUS,
            Artifact::Invariant(_) => Interest::INVARIANT,
            Artifact::Precision(..) => Interest::PRECISION,
            Artifact::Trace(_) => Interest::TRACE,
            Artifact::Residual(_) => Interest::RESIDUAL,
            Artifact::Query(_) => Interest::QUERY,
            Artifact::Lemma(_) => Interest::LEMMA,
        }
    }
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
