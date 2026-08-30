//! The shared artifact store.
//!
//! Two jobs: keep an append-only log so engines can pull deltas since their own
//! cursor, and refuse artifacts that violate the direction discipline.

use std::collections::{BTreeMap, HashMap};

use crate::artifact::*;
use log::{debug, trace, warn};
use ajave_ir::verdict::Verdict;
use ajave_ir::{BlockId, MethodKey, Program, VarId};

#[derive(Debug)]
pub struct Rejected {
    pub reason: String,
}

/// An interval bound [lo, hi] discovered by abstract interpretation.
#[derive(Clone, Debug)]
pub struct IntervalHint {
    pub lo: i64,
    pub hi: i64,
}

#[derive(Default)]
pub struct Blackboard {
    log: Vec<Tagged>,
    statuses: BTreeMap<ObligationRef, Status>,
    /// Obligations an over-approximating engine proved safe, kept even when a
    /// `Violated` status occupies `statuses` for the same obligation.
    ///
    /// The two are not contradictory until the violation is *confirmed*: an
    /// Under engine's witness is a candidate, and one that fails JVM replay is
    /// withdrawn. Recording the proof separately means a refuted candidate no
    /// longer erases it — previously whichever engine ran first won outright,
    /// so NRA's real-valued counterexamples silently voided BMC's exhaustive
    /// proofs on the entire float-nonlinear-calculation category.
    proved_safe: std::collections::BTreeSet<ObligationRef>,
    invariants: Vec<Invariant>,
    traces: Vec<AbstractTrace>,
    next_seq: u64,
    next_inv: u32,
    pub rejections: Vec<String>,
    /// Total assertion obligations in the program (seeded + unreachable).
    /// Used to detect vacuous TRUE when reachability is incomplete.
    total_assertions: usize,
    /// Whether we are checking only assertions (valid-assert property).
    /// When false (no-runtime-exception), the vacuous-TRUE guard is skipped.
    assertion_only: bool,
    /// Interval bounds from abstract interpretation, keyed by (method, block, var).
    /// Only populated when AI analysis is complete (sound over-approximation).
    interval_hints: HashMap<(MethodKey, BlockId, VarId), IntervalHint>,
}

impl Blackboard {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register every obligation reachable from the entry point as `Open`.
    ///
    /// Deliberately *not* every obligation in every loaded class: `main.rs`
    /// loads the whole classpath, including `Verifier`'s own bytecode and
    /// every class's `<clinit>`, none of which the program can actually
    /// execute through in a way that matters to the property. Seeding those
    /// too would mean the whole-task verdict could never reach TRUE no
    /// matter what the engines proved -- it would be permanently blocked on
    /// obligations nothing ever analyses, which is exactly the bug that
    /// showed up the first time this ran end to end.
    pub fn seed(&mut self, prog: &Program, assertion_only: bool) {
        self.assertion_only = assertion_only;
        let reachable: std::collections::HashSet<_> =
            prog.reachable_from_entry().into_iter().collect();
        // Count total assertions across ALL loaded methods (not just reachable).
        // If assertions exist somewhere but none are reachable, our call-graph
        // analysis may be incomplete (e.g. reflection via Class.forName), so
        // we should return Unknown rather than a vacuous TRUE.
        self.total_assertions = prog
            .obligations()
            .iter()
            .filter(|(method, id)| {
                prog.body(method)
                    .map(|b| b.obligation(*id).kind.is_assertion())
                    .unwrap_or(false)
            })
            .count();
        for (method, id) in prog.obligations() {
            if !reachable.contains(&method) {
                continue;
            }
            let body = prog.body(&method).unwrap();
            let ob = body.obligation(id);
            if assertion_only {
                // valid-assert: only Assertion obligations
                if !ob.kind.is_assertion() {
                    continue;
                }
            } else {
                // no-runtime-exception: all runtime-exception kinds,
                // but NOT Assertion (separate property) and NOT guarded
                // (exceptions caught within the method don't escape main)
                if ob.kind.is_assertion() {
                    continue;
                }
                if ob.guarded {
                    continue;
                }
            }
            self.statuses
                .insert(ObligationRef { method, id }, Status::Open);
        }
        debug!(
            "blackboard: seeded {} reachable obligations (total assertions in program: {}){}",
            self.statuses.len(),
            self.total_assertions,
            if assertion_only { " (assertion-only)" } else { "" }
        );
    }

    /// The soundness gate.
    ///
    /// An under-approximating engine cannot discharge an obligation; an
    /// over-approximating one cannot violate it. `verdict.rs` enforces the same
    /// rule in the type system for engines that use those traits, but engines
    /// are allowed to be hand-written state machines, so the runtime check
    /// stays. This is the one place where a slip becomes a -32.
    pub fn publish(
        &mut self,
        producer: EngineId,
        direction: Direction,
        artifact: Artifact,
    ) -> Result<u64, Rejected> {
        if let Artifact::Status(oref, st) = &artifact {
            match (direction, st) {
                (Direction::Under, Status::Discharged { .. }) => {
                    return self.reject(format!(
                        "{producer} is under-approximating and may not discharge {oref}"
                    ))
                }
                (Direction::Over, Status::Violated { .. }) => {
                    return self.reject(format!(
                        "{producer} is over-approximating and may not violate {oref}"
                    ))
                }
                _ => {}
            }
            // Deliberately NOT rejecting on `witness.nondet_sequence.is_empty()`
            // here. That was an earlier version of this gate, and it was
            // wrong: a deterministic bug (no `nondet` calls on the path at
            // all) has a legitimately empty witness, and is exactly as
            // replayable as one with values in it. The blackboard cannot
            // distinguish "genuinely no inputs needed" from "engine didn't
            // bother constructing a witness" by looking at the shape of the
            // value alone -- only actually attempting the replay can, which
            // is `certify::JvmReplay`'s job, not this gate's. Publishing here
            // is provisional; certification is what makes a FALSE final.
        }

        let seq = self.next_seq;
        self.next_seq += 1;

        trace!("blackboard: publish seq={seq} producer={producer} direction={direction:?}");

        match &artifact {
            Artifact::Status(oref, st) => {
                // Only accept status updates for obligations that were
                // originally seeded. Non-seeded obligations (e.g. ArrayBounds,
                // NullDeref in callee bodies) are not property-relevant and
                // must not influence the verdict.
                if !self.statuses.contains_key(oref) {
                    trace!("blackboard: ignoring status for non-seeded {oref}");
                } else {
                    // Remember every discharge, whatever else is recorded.
                    if matches!(st, Status::Discharged { .. }) {
                        self.proved_safe.insert(oref.clone());
                    }
                    let keep =
                        !matches!(self.statuses.get(oref), Some(existing) if existing.is_final());
                    if keep {
                        self.statuses.insert(oref.clone(), st.clone());
                    }
                }
            }
            Artifact::Invariant(inv) => self.invariants.push(inv.clone()),
            Artifact::Trace(t) => self.traces.push(t.clone()),
            _ => {}
        }

        self.log.push(Tagged {
            seq,
            producer,
            direction,
            artifact,
        });
        Ok(seq)
    }

    fn reject(&mut self, reason: String) -> Result<u64, Rejected> {
        warn!("blackboard: rejected artifact — {reason}");
        self.rejections.push(reason.clone());
        Err(Rejected { reason })
    }

    /// Everything published at or after `cursor`. Engines keep their own cursor
    /// so they can be added, removed or restarted without coordination.
    pub fn since(&self, cursor: u64) -> &[Tagged] {
        let start = self
            .log
            .iter()
            .position(|t| t.seq >= cursor)
            .unwrap_or(self.log.len());
        &self.log[start..]
    }

    pub fn head(&self) -> u64 {
        self.next_seq
    }

    pub fn fresh_invariant_id(&mut self) -> u32 {
        self.next_inv += 1;
        self.next_inv
    }

    pub fn status(&self, oref: &ObligationRef) -> &Status {
        self.statuses.get(oref).unwrap_or(&Status::Open)
    }

    pub fn open(&self) -> Vec<ObligationRef> {
        self.statuses
            .iter()
            .filter(|(_, s)| !s.is_final())
            .map(|(k, _)| k.clone())
            .collect()
    }

    /// Obligations still open, plus those whose only status is an *unconfirmed*
    /// violation.
    ///
    /// A violation from an under-approximating engine is a candidate until JVM
    /// replay confirms it, so an over-approximating engine that can prove the
    /// obligation safe should still be given the chance. Without this, whichever
    /// engine published first won outright: NRA's real-valued counterexamples
    /// took the obligation out of `open()` before the BMC — which had explored
    /// the same body exhaustively and found nothing — was ever asked.
    ///
    /// Only for engines that record a `Discharged`; the verdict still refuses
    /// to call TRUE while an unrefuted violation stands.
    pub fn open_or_unconfirmed(&self) -> Vec<ObligationRef> {
        self.statuses
            .iter()
            .filter(|(_, s)| !s.is_final() || matches!(s, Status::Violated { .. }))
            .map(|(k, _)| k.clone())
            .collect()
    }

    pub fn inductive_invariants(&self) -> impl Iterator<Item = &Invariant> {
        self.invariants
            .iter()
            .filter(|i| i.status == InvStatus::Inductive)
    }

    pub fn pending_traces(&self) -> impl Iterator<Item = &AbstractTrace> {
        self.traces.iter().filter(|t| t.feasible != Some(true))
    }

    /// Publish an interval bound discovered by abstract interpretation.
    /// Only call this when the analysis was complete (sound over-approximation).
    pub fn publish_interval_hint(
        &mut self,
        method: MethodKey,
        block: BlockId,
        var: VarId,
        lo: i64,
        hi: i64,
    ) {
        self.interval_hints
            .insert((method, block, var), IntervalHint { lo, hi });
    }

    /// Retrieve all interval hints for a given method and block.
    pub fn interval_hints_for(
        &self,
        method: &MethodKey,
        block: BlockId,
    ) -> Vec<(VarId, i64, i64)> {
        self.interval_hints
            .iter()
            .filter(|((m, b, _), _)| m == method && *b == block)
            .map(|((_, _, v), h)| (*v, h.lo, h.hi))
            .collect()
    }

    /// Whether any interval hints have been published.
    pub fn has_interval_hints(&self) -> bool {
        !self.interval_hints.is_empty()
    }

    /// Retrieve all interval hints for a given method, as (block, var) → (lo, hi).
    pub fn interval_hints_for_method(
        &self,
        method: &MethodKey,
    ) -> HashMap<(BlockId, VarId), (i64, i64)> {
        self.interval_hints
            .iter()
            .filter(|((m, _, _), _)| m == method)
            .map(|((_, b, v), h)| ((*b, *v), (h.lo, h.hi)))
            .collect()
    }

    pub fn statuses(&self) -> impl Iterator<Item = (&ObligationRef, &Status)> {
        self.statuses.iter()
    }

    /// Whether we are checking the assert property (vs no-runtime-exception).
    /// How many distinct obligations any engine has ever *published* a
    /// discharge for.
    ///
    /// Not the same as counting `Status::Discharged` in `statuses`: a discharge
    /// published after a violation is recorded here but discarded there, because
    /// the first final status wins. That discarded discharge still steers the
    /// verdict via `verdict_excluding`, so measuring only stored statuses hides
    /// the thing that decided the answer (#66).
    pub fn proved_safe_count(&self) -> usize {
        self.proved_safe.len()
    }

    pub fn is_assertion_only(&self) -> bool {
        self.assertion_only
    }

    /// The whole-task verdict. One violation is enough to say FALSE; TRUE
    /// requires every obligation discharged.
    pub fn verdict(&self) -> Verdict {
        if self.statuses.is_empty() {
            if self.assertion_only && self.total_assertions > 0 {
                // Program has assertions but none were reachable — incomplete
                // reachability analysis. Return Unknown rather than vacuous TRUE.
                // For no-runtime-exception, empty = no runtime checks = TRUE.
                return Verdict::Unknown;
            }
            return Verdict::True;
        }
        if self
            .statuses
            .values()
            .any(|s| matches!(s, Status::Violated { .. }))
        {
            return Verdict::False;
        }
        if self
            .statuses
            .values()
            .all(|s| matches!(s, Status::Discharged { .. }))
        {
            return Verdict::True;
        }
        Verdict::Unknown
    }

    /// The verdict that would hold if the named violations had never been
    /// published.
    ///
    /// A violation refuted by JVM replay is a withdrawn *claim*, not evidence
    /// the program is unsafe. Treating a refutation as an automatic UNKNOWN
    /// throws away any proof an over-approximating engine already established
    /// for the same obligation — which is exactly what an under-approximating
    /// engine's spurious candidate should not be able to do.
    ///
    /// Excluded obligations are treated as still open, so this only returns
    /// TRUE when every *remaining* obligation is discharged. A refuted
    /// violation on an obligation nothing else proved still yields UNKNOWN.
    pub fn verdict_excluding(&self, excluded: &[ObligationRef]) -> Verdict {
        let remaining: Vec<&Status> = self
            .statuses
            .iter()
            .filter(|(k, _)| !excluded.contains(k))
            .map(|(_, v)| v)
            .collect();

        if remaining.iter().any(|s| matches!(s, Status::Violated { .. })) {
            return Verdict::False;
        }
        // The blackboard holds one status per obligation, so an obligation
        // whose only status was the refuted violation is left unproven — no
        // engine independently discharged it. Excluding it cannot manufacture
        // a proof, and this must not return TRUE on that basis.
        //
        // What this *does* recover is the case where the refuted violation and
        // the discharge concern different obligations: engine A wrongly
        // flagged obligation 1 while engine B proved obligations 1..n safe.
        // Dropping A's withdrawn claim then leaves a complete set of proofs.
        for k in excluded {
            let discharged = matches!(self.statuses.get(k), Some(Status::Discharged { .. }))
                || self.proved_safe.contains(k);
            if !discharged {
                return Verdict::Unknown;
            }
        }
        if remaining.iter().all(|s| matches!(s, Status::Discharged { .. })) {
            return Verdict::True;
        }
        Verdict::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::{MethodKey, ObligationId};

    fn oref() -> ObligationRef {
        ObligationRef {
            method: MethodKey {
                class: "Main".into(),
                name: "main".into(),
                desc: "()V".into(),
            },
            id: ObligationId(0),
        }
    }

    #[test]
    fn under_approx_may_not_discharge() {
        let mut bb = Blackboard::new();
        let r = bb.publish(
            EngineId("bmc"),
            Direction::Under,
            Artifact::Status(
                oref(),
                Status::Discharged {
                    by: EngineId("bmc"),
                    proof: ProofKind::Trivial,
                },
            ),
        );
        assert!(r.is_err());
    }

    #[test]
    fn over_approx_may_not_violate() {
        let mut bb = Blackboard::new();
        let r = bb.publish(
            EngineId("presolve"),
            Direction::Over,
            Artifact::Status(
                oref(),
                Status::Violated {
                    by: EngineId("presolve"),
                    witness: Default::default(),
                },
            ),
        );
        assert!(r.is_err());
    }

    #[test]
    fn deterministic_violation_with_empty_witness_is_accepted() {
        // The case the old (wrong) rule used to reject: no nondet calls on
        // the path, so an empty sequence is the *correct* witness, not a
        // missing one.
        let mut bb = Blackboard::new();
        let r = bb.publish(
            EngineId("concrete"),
            Direction::Under,
            Artifact::Status(
                oref(),
                Status::Violated {
                    by: EngineId("concrete"),
                    witness: Default::default(),
                },
            ),
        );
        assert!(r.is_ok());
    }
}
