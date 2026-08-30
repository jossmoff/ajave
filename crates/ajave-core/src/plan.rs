//! Verification planning: decide *what work to do* before doing any of it.
//!
//! Every obligation and every engine invocation costs budget, and its value
//! depends on the pair (property being checked, shape of the program). Until
//! now both were decided statically and uniformly — obligations emitted for
//! every property, engines run in one hardcoded order, budgets fixed as
//! constants. Four measured problems came out of that:
//!
//! * Library-call preconditions produce only runtime-exception obligations, yet
//!   were emitted under `--property assert`, which seeds none of them. Cost:
//!   ~30 additional timeouts on a full valid-assert run, concentrated in
//!   `autostub` (+11, nothing but JDK calls) and `alarm` (+9, enormous
//!   methods).
//! * NRA runs on every float program and publishes real-valued counterexamples
//!   that IEEE-754 refutes, which vetoed BMC's proofs and lost an entire
//!   category.
//! * `MAX_FORKS`, `widen_delay` and `max_switches` were each raised until a
//!   specific benchmark passed (issue #50).
//! * CHC and CEGAR run on every program and decide under 1% of them.
//!
//! # The soundness rule
//!
//! **A plan may only remove work that provably cannot change the verdict. It
//! may never change what a verdict means.**
//!
//! Every decision here must be classifiable as one of:
//!
//! * *verdict-neutral* — the removed work could not have affected the answer
//!   (skipping NRE obligations when checking valid-assert);
//! * *precision-only* — the answer may become UNKNOWN but never wrong
//!   (skipping an engine that might have found a violation).
//!
//! Anything that could turn one definite answer into a different definite
//! answer does not belong in a plan. In particular **engine ordering is not
//! currently verdict-neutral**: the blackboard keeps the first status published
//! per obligation, so which engine runs first can decide the answer. That is
//! why `engines` here is descriptive rather than something the planner
//! reorders on shape — see the note on `Plan::engines`.

use std::collections::HashSet;

use ajave_ir::ObligationKind;

/// Which SV-COMP property is being checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Property {
    /// `valid-assert.prp` — `CHECK( init(Main.main()), LTL(G assert) )`
    ValidAssert,
    /// `no-runtime-exception.prp`
    NoRuntimeException,
    /// `no-deadlock.prp` — answered outside the obligation system.
    NoDeadlock,
}

impl Property {
    pub fn parse(s: &str) -> Option<Property> {
        match s {
            "assert" | "valid-assert" => Some(Property::ValidAssert),
            "no-runtime-exception" => Some(Property::NoRuntimeException),
            "no-deadlock" => Some(Property::NoDeadlock),
            _ => None,
        }
    }

    /// Obligation kinds this property can actually be violated by.
    ///
    /// This is the relevance filter, and it is verdict-neutral by definition:
    /// an obligation of a kind the property does not consume cannot change the
    /// answer, so generating it is pure cost.
    pub fn relevant_kinds(self) -> HashSet<ObligationKind> {
        use ObligationKind::*;
        match self {
            // An assertion failure is an AssertionError, which is an Error and
            // not a RuntimeException — the two properties genuinely do not
            // overlap.
            Property::ValidAssert => [Assertion].into_iter().collect(),
            Property::NoRuntimeException => [
                DivByZero,
                NullDeref,
                ArrayBounds,
                NegArraySize,
                ClassCast,
                ExplicitThrow,
            ]
            .into_iter()
            .collect(),
            // Deadlock is a property of the execution, not of any program
            // point, so it consumes no point obligations at all.
            Property::NoDeadlock => HashSet::new(),
        }
    }

    /// Should the lifter emit obligations for library-call preconditions?
    ///
    /// These are all runtime-exception kinds, so only that property consumes
    /// them. Emitting them elsewhere costs every engine the extra statements —
    /// a materialised `length()` call, its comparisons and the `Check` — for
    /// obligations that are then discarded at seed time.
    pub fn wants_call_preconditions(self) -> bool {
        matches!(self, Property::NoRuntimeException)
    }
}

/// A decision the planner made, with the reason.
///
/// Recorded so `--explain-plan` can print *why* work was skipped. Today's
/// regressions were hard to find precisely because nothing reported "a scan
/// was added to every program"; a plan that cannot explain itself repeats
/// that.
#[derive(Clone, Debug)]
pub struct Decision {
    pub subject: String,
    pub included: bool,
    pub reason: String,
}

/// What to verify and how.
#[derive(Clone, Debug)]
pub struct Plan {
    pub property: Property,
    /// Obligation kinds to seed. Anything else is not generated or not seeded.
    pub obligation_kinds: HashSet<ObligationKind>,
    /// Whether the lifter should emit library-call precondition obligations.
    pub seed_call_preconditions: bool,
    /// Engines to run, in order.
    ///
    /// **Descriptive, not yet chosen by shape.** Ordering is currently not
    /// verdict-neutral — the blackboard keeps the first status published per
    /// obligation, so running engine X before Y can change the answer. That
    /// mechanism gained six benchmarks when the concurrency engine was moved
    /// first, and previously *lost* the whole float-nonlinear category when NRA
    /// got there first. Until status precedence is fixed so that a later,
    /// better-justified result can supersede an earlier one, the planner
    /// records the order rather than deriving it.
    pub engines: Vec<&'static str>,
    /// Every decision taken, for `--explain-plan`.
    pub decisions: Vec<Decision>,
}

impl Plan {
    /// Build a plan for a property.
    ///
    /// Deliberately does not consult program shape yet: the relevance filter is
    /// property-determined and pays for itself, whereas shape-derived engine
    /// selection and budgets need the ordering question resolved first.
    pub fn for_property(property: Property) -> Plan {
        let kinds = property.relevant_kinds();
        let precond = property.wants_call_preconditions();

        let mut decisions = vec![Decision {
            subject: "obligation kinds".into(),
            included: true,
            reason: format!(
                "{} kind(s) can violate {:?}; others are not seeded",
                kinds.len(),
                property
            ),
        }];
        decisions.push(Decision {
            subject: "library-call preconditions".into(),
            included: precond,
            reason: if precond {
                "runtime-exception obligations are consumed by this property".into()
            } else {
                "these produce only runtime-exception obligations, which this \
                 property never seeds — emitting them is pure cost"
                    .into()
            },
        });

        Plan {
            property,
            obligation_kinds: kinds,
            seed_call_preconditions: precond,
            engines: Vec::new(),
            decisions,
        }
    }

    /// Is this obligation kind worth seeding under this plan?
    pub fn wants(&self, kind: ObligationKind) -> bool {
        self.obligation_kinds.contains(&kind)
    }

    /// Human-readable summary for `--explain-plan`.
    pub fn explain(&self) -> String {
        let mut s = format!("verification plan for {:?}\n", self.property);
        for d in &self.decisions {
            s.push_str(&format!(
                "  [{}] {:<28} {}\n",
                if d.included { "on " } else { "off" },
                d.subject,
                d.reason
            ));
        }
        if !self.engines.is_empty() {
            s.push_str(&format!("  engines: {}\n", self.engines.join(" -> ")));
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn properties_consume_disjoint_obligation_kinds() {
        let a = Property::ValidAssert.relevant_kinds();
        let n = Property::NoRuntimeException.relevant_kinds();
        assert!(
            a.is_disjoint(&n),
            "an assertion failure is an Error, not a RuntimeException; if these \
             ever overlap the relevance filter is no longer verdict-neutral"
        );
        assert!(Property::NoDeadlock.relevant_kinds().is_empty());
    }

    #[test]
    fn only_nre_wants_call_preconditions() {
        assert!(Property::NoRuntimeException.wants_call_preconditions());
        assert!(!Property::ValidAssert.wants_call_preconditions());
        assert!(!Property::NoDeadlock.wants_call_preconditions());
    }

    #[test]
    fn assertion_is_seeded_only_for_valid_assert() {
        let p = Plan::for_property(Property::ValidAssert);
        assert!(p.wants(ObligationKind::Assertion));
        assert!(!p.wants(ObligationKind::NullDeref));

        let q = Plan::for_property(Property::NoRuntimeException);
        assert!(!q.wants(ObligationKind::Assertion));
        assert!(q.wants(ObligationKind::NullDeref));
    }

    #[test]
    fn plan_explains_why_work_was_skipped() {
        let p = Plan::for_property(Property::ValidAssert);
        let text = p.explain();
        assert!(text.contains("off"), "a skipped decision must be visible");
        assert!(
            text.contains("pure cost"),
            "the reason must say why, not just that"
        );
    }
}
