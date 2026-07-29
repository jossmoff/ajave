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

/// Marker for an analysis that over-approximates reachable states.
/// It may prove safety; it may never claim a bug.
pub trait OverApprox {
    /// `true` means "proved safe". `false` means "don't know" — never "unsafe".
    fn proves_safe(&self) -> bool;

    fn verdict(&self) -> Verdict {
        if self.proves_safe() {
            Verdict::True
        } else {
            Verdict::Unknown
        }
    }
}

/// Marker for an analysis that under-approximates reachable states.
/// It may exhibit a bug; it may never claim safety.
pub trait UnderApprox {
    /// A witness is required, not optional. An unreplayable FALSE is worth zero
    /// points, so we do not have a representation for "found a bug, no witness".
    fn witness(&self) -> Option<&Witness>;

    fn verdict(&self) -> Verdict {
        if self.witness().is_some() {
            Verdict::False
        } else {
            Verdict::Unknown
        }
    }
}

/// Placeholder for a violation witness. Stage 2 fills this in properly; the
/// point of declaring it now is that `UnderApprox` cannot be implemented
/// without producing one.
#[derive(Clone, Debug, Default)]
pub struct Witness {
    /// Values to be returned by successive `Verifier.nondet*()` calls, in order.
    /// This is all a replay harness needs for the stage 0-2 fragment.
    pub nondet_sequence: Vec<i64>,
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
