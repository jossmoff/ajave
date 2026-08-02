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
    /// The raw i64 encoding used by JvmReplay's `-Droast.seq` property.
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
