//! The shared artifact store.
//!
//! Two jobs: keep an append-only log so engines can pull deltas since their own
//! cursor, and refuse artifacts that violate the direction discipline.

use std::collections::BTreeMap;

use crate::artifact::*;
use log::{debug, trace, warn};
use roast_ir::verdict::Verdict;
use roast_ir::Program;

#[derive(Debug)]
pub struct Rejected {
    pub reason: String,
}

#[derive(Default)]
pub struct Blackboard {
    log: Vec<Tagged>,
    statuses: BTreeMap<ObligationRef, Status>,
    invariants: Vec<Invariant>,
    traces: Vec<AbstractTrace>,
    next_seq: u64,
    next_inv: u32,
    pub rejections: Vec<String>,
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
    pub fn seed(&mut self, prog: &Program) {
        let reachable: std::collections::HashSet<_> =
            prog.reachable_from_entry().into_iter().collect();
        for (method, id) in prog.obligations() {
            if reachable.contains(&method) {
                self.statuses
                    .insert(ObligationRef { method, id }, Status::Open);
            }
        }
        debug!("blackboard: seeded {} reachable obligations", self.statuses.len());
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
                let keep = match self.statuses.get(oref) {
                    Some(existing) if existing.is_final() => false,
                    _ => true,
                };
                if keep {
                    self.statuses.insert(oref.clone(), st.clone());
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

    pub fn inductive_invariants(&self) -> impl Iterator<Item = &Invariant> {
        self.invariants
            .iter()
            .filter(|i| i.status == InvStatus::Inductive)
    }

    pub fn pending_traces(&self) -> impl Iterator<Item = &AbstractTrace> {
        self.traces.iter().filter(|t| t.feasible != Some(true))
    }

    pub fn statuses(&self) -> impl Iterator<Item = (&ObligationRef, &Status)> {
        self.statuses.iter()
    }

    /// The whole-task verdict. One violation is enough to say FALSE; TRUE
    /// requires every obligation discharged.
    pub fn verdict(&self) -> Verdict {
        if self.statuses.is_empty() {
            // No obligations at all means nothing can go wrong.
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use roast_ir::{MethodKey, ObligationId};

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
