//! The verdict lattice, and the type-level guard that keeps analyses honest.
//!
//! The design rule from the outset: an analysis must declare which direction it
//! approximates in, and the type system refuses to let it emit the verdict it is
//! not entitled to. An over-approximating analysis (abstract interpretation) may
//! conclude TRUE but never FALSE; an under-approximating one (BMC, concolic) may
//! conclude FALSE but never TRUE. Getting this wrong is what costs -16 or -32 a
//! task, so it should not be enforceable only by code review.

use std::fmt;

/// Belnap-style four-valued verdict. `Unknown` is bottom (no information),
/// `Contradiction` is top (two analyses disagreed — always a bug in us).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verdict {
    Unknown,
    True,
    False,
    Contradiction,
}

impl Verdict {
    /// Lattice join. Note this can only ever move *up* the lattice, so merging
    /// portfolio results cannot silently turn a correct verdict into a wrong one:
    /// disagreement surfaces as `Contradiction` rather than as a coin flip.
    pub fn join(self, other: Verdict) -> Verdict {
        use Verdict::*;
        match (self, other) {
            (Unknown, v) | (v, Unknown) => v,
            (a, b) if a == b => a,
            _ => Contradiction,
        }
    }

    /// What we actually print to stdout for BenchExec. A `Contradiction` is
    /// reported as `Unknown`: we scored zero either way, and claiming a verdict
    /// we know to be internally inconsistent is how you get a -32.
    pub fn as_svcomp(self) -> &'static str {
        match self {
            Verdict::True => "TRUE",
            Verdict::False => "FALSE",
            Verdict::Unknown | Verdict::Contradiction => "UNKNOWN",
        }
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_svcomp())
    }
}

/// A single nondeterministic value chosen during execution, with its type
/// preserved so witness emitters can format it correctly (especially strings).
#[derive(Clone, Debug)]
pub enum NondetValue {
    Int(i32),
    Long(i64),
    Bool(bool),
    Str(String),
}

impl NondetValue {
    /// The raw i64 encoding used by JvmReplay's `-Dajave.seq` property.
    pub fn as_raw(&self) -> i64 {
        match self {
            NondetValue::Int(v) => *v as i64,
            NondetValue::Long(v) => *v,
            NondetValue::Bool(v) => *v as i64,
            NondetValue::Str(_) => 0, // string index is in the raw sequence separately
        }
    }
}

/// One nondet call site in the witness, carrying the typed value and optional
/// source location for the witness automaton.
#[derive(Clone, Debug)]
pub struct NondetEntry {
    pub value: NondetValue,
    /// Which `Verifier.nondet*()` variant was called.
    pub nondet_method: &'static str,
    /// Source line from LineNumberTable, if known.
    pub line: Option<u16>,
}

/// Identifies a thread within one explored execution.
///
/// `ThreadId(0)` is always the main thread. Ids are assigned in the order
/// threads are started, so a schedule replays identically as long as the
/// program's thread-creation order is deterministic — which it is for the
/// bounded fragment we explore.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ThreadId(pub u32);

/// One slice of a thread schedule: run `thread` for `steps` events, then yield.
///
/// A "step" is one concurrency-relevant event (a shared read or write, a
/// monitor operation, a thread lifecycle call) rather than one bytecode
/// instruction. Counting steps at instruction granularity would make a
/// schedule brittle against unrelated changes to lifting, and would not
/// correspond to anything a JVM-side harness could enforce.
///
/// # Relationship to the SV-COMP witness formats
///
/// Violation witness format **2.0** — the YAML format we emit — does not define
/// concurrency witnesses at all; the format paper states they "have not yet
/// been defined for concurrency safety". So there is no standard shape to
/// follow here yet.
///
/// Format **1.0** (GraphML) did carry them: Beyer & Friedberger (2020)
/// annotated each automaton transition with a `threadId` and marked thread
/// creation with `createThread`. This type is a run-length encoding of exactly
/// that per-transition sequence — `[(T0,3),(T1,2)]` expands to
/// `T0 T0 T0 T1 T1` — so converting either way is mechanical, and we stay
/// alignable with whatever 2.0 eventually specifies.
///
/// The practical consequence: until 2.0 gains concurrency support, external
/// validators cannot check a witness carrying a schedule. That is a second
/// reason certification has to be our own harness rather than a third party's.
/// See `docs/strategies/concurrency.md`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScheduleSlice {
    pub thread: ThreadId,
    pub steps: u32,
}

/// A violation witness: records the nondeterministic choices an execution made
/// so they can be (a) replayed on a real JVM, and (b) emitted as a
/// SV-COMP witness file that external validators can check.
#[derive(Clone, Debug, Default)]
pub struct Witness {
    /// Values to be returned by successive `Verifier.nondet*()` calls, in order.
    /// This is all a replay harness needs for the stage 0-2 fragment.
    pub nondet_sequence: Vec<i64>,
    /// Typed entries for witness file emission. Parallel to `nondet_sequence`
    /// but carries the original type and source location.
    pub entries: Vec<NondetEntry>,
    /// The thread interleaving this execution took, if concurrency was
    /// involved. Empty for every sequential witness, which is all of them
    /// today.
    ///
    /// Nondeterminism in a concurrent program has two independent sources —
    /// the input values *and* the schedule — and reproducing a failure needs
    /// both. `nondet_sequence` alone cannot express an interleaving, so a
    /// concurrency counterexample recorded without this field is not
    /// replayable even in principle.
    ///
    /// Note the certification asymmetry this creates, spelled out in
    /// `docs/strategies/concurrency.md`: `JvmReplay` can feed input values to a
    /// stock JVM, but it cannot force a schedule. A witness carrying a schedule
    /// therefore needs a different certifier, and until one exists a
    /// concurrency FALSE is weaker evidence than every other FALSE ajave emits.
    pub schedule: Vec<ScheduleSlice>,
    /// Decisions the program itself does not determine, in the order the
    /// execution needed them — whether a timed wait expired, and later which
    /// write a read observed.
    ///
    /// A third independent source of nondeterminism alongside inputs and the
    /// schedule. An execution that consulted one of these is not reproducible
    /// from the schedule alone: replaying the same interleaving with the other
    /// outcome reaches a different state, so the violation would not recur and
    /// a correct FALSE would be discarded as unreproducible.
    pub choices: Vec<u32>,
}

impl Witness {
    /// Does reproducing this witness require controlling the thread schedule?
    ///
    /// Used to route a witness to the right certifier: a sequential witness can
    /// go to `JvmReplay`, a scheduled one cannot.
    pub fn needs_schedule(&self) -> bool {
        !self.schedule.is_empty()
    }

    /// Did this execution depend on a decision the program does not make?
    pub fn needs_choices(&self) -> bool {
        !self.choices.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::Verdict::*;

    #[test]
    fn join_is_monotone_and_surfaces_disagreement() {
        assert_eq!(Unknown.join(True), True);
        assert_eq!(True.join(True), True);
        assert_eq!(True.join(False), Contradiction);
        assert_eq!(Contradiction.as_svcomp(), "UNKNOWN");
    }
}
