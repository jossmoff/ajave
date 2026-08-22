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
    ///
    /// Strings have no raw encoding: the shadow `Verifier` reads them from
    /// separate `-Droast.str.N` properties and its `nondetString()` never
    /// advances the numeric cursor. `Witness::nondet_sequence` therefore skips
    /// them entirely rather than reserving a slot -- see the note there.
    pub fn as_raw(&self) -> Option<i64> {
        match self {
            NondetValue::Int(v) => Some(*v as i64),
            NondetValue::Long(v) => Some(*v),
            NondetValue::Bool(v) => Some(*v as i64),
            NondetValue::Str(_) => None,
        }
    }

    /// The `Verifier` method this value came back from.
    pub fn nondet_method(&self) -> &'static str {
        match self {
            NondetValue::Int(_) => "nondetInt",
            NondetValue::Long(_) => "nondetLong",
            NondetValue::Bool(_) => "nondetBoolean",
            NondetValue::Str(_) => "nondetString",
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
///
/// One list, in call order. This used to be two -- a `Vec<i64>` of raw values
/// alongside the typed entries, documented as "parallel to" each other with
/// nothing enforcing it. They were in fact kept in lockstep by every producer,
/// and that was the bug: the shadow `Verifier`'s `nondetString()` reads from
/// `-Droast.str.N` and does *not* advance the numeric cursor, so reserving a
/// slot in the raw sequence for a string shifted every later numeric value by
/// one. A program calling `nondetString()` before `nondetInt()` replayed the
/// wrong input, the expected exception did not fire, and a correct FALSE was
/// downgraded to UNKNOWN by its own certifier.
#[derive(Clone, Debug, Default)]
pub struct Witness {
    /// Every nondeterministic choice, in the order the program made them.
    pub entries: Vec<NondetEntry>,
}

impl Witness {
    /// Values for successive numeric `Verifier.nondet*()` calls, in order, as
    /// the shadow `Verifier` consumes them. Strings are excluded: they are
    /// passed out of band and do not advance that cursor.
    pub fn nondet_sequence(&self) -> Vec<i64> {
        self.entries
            .iter()
            .filter_map(|e| e.value.as_raw())
            .collect()
    }

    /// String values in call order, matching the shadow `Verifier`'s separate
    /// `roast.str.N` cursor.
    pub fn string_values(&self) -> Vec<&str> {
        self.entries
            .iter()
            .filter_map(|e| match &e.value {
                NondetValue::Str(s) => Some(s.as_str()),
                _ => None,
            })
            .collect()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
mod witness_tests {
    use super::*;

    fn entry(value: NondetValue) -> NondetEntry {
        NondetEntry {
            nondet_method: value.nondet_method(),
            value,
            line: None,
        }
    }

    #[test]
    fn a_string_does_not_consume_a_numeric_slot() {
        // The shadow Verifier's nondetString() advances only its own cursor, so
        // a string must not shift the numeric sequence.
        let w = Witness {
            entries: vec![
                entry(NondetValue::Str("hello".into())),
                entry(NondetValue::Int(42)),
            ],
        };
        assert_eq!(w.nondet_sequence(), vec![42]);
        assert_eq!(w.string_values(), vec!["hello"]);
    }

    #[test]
    fn numeric_values_keep_their_order_and_encoding() {
        let w = Witness {
            entries: vec![
                entry(NondetValue::Int(-1)),
                entry(NondetValue::Long(1 << 40)),
                entry(NondetValue::Bool(true)),
                entry(NondetValue::Bool(false)),
            ],
        };
        assert_eq!(w.nondet_sequence(), vec![-1, 1 << 40, 1, 0]);
    }

    #[test]
    fn an_empty_witness_is_legitimate() {
        // A deterministic bug needs no inputs; that is not a missing witness.
        let w = Witness::default();
        assert!(w.is_empty());
        assert!(w.nondet_sequence().is_empty());
    }
}
