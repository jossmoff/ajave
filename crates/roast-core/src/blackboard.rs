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
    /// Total assertion obligations in the program (seeded + unreachable).
    /// Used to detect vacuous TRUE when reachability is incomplete.
    total_assertions: usize,
    /// The direction each engine *declared* via `Engine::direction`, recorded
    /// by the orchestrator before scheduling starts. See `register_engine`.
    declared: BTreeMap<EngineId, Direction>,
}

impl Blackboard {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record what an engine declared it is entitled to conclude.
    ///
    /// The soundness gate below reads the `direction` passed to `publish`, not
    /// the engine's `Engine::direction()`. Those are supposed to be the same
    /// value, and for every engine but one they were -- `NraEngine` declared
    /// `Over` while passing `Direction::Under` at its publish site, and nothing
    /// noticed, because the gate had no way to compare them. That particular
    /// case was benign (NRA never discharges, so `Under` was the honest label
    /// and the declaration was the wrong half), but an engine free to pass a
    /// different direction per call can route around the discipline entirely.
    ///
    /// So the orchestrator registers every engine here first, and `publish`
    /// rejects any artifact whose direction disagrees with the registration.
    /// Engines constructed outside an orchestrator -- unit tests, mostly --
    /// simply are not registered, and are gated on the passed direction alone.
    pub fn register_engine(&mut self, id: EngineId, direction: Direction) {
        self.declared.insert(id, direction);
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
        let reachable: std::collections::HashSet<_> =
            prog.reachable_from_entry().into_iter().collect();
        // Count total assertions in the entire program (for vacuous-TRUE guard).
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
            if assertion_only {
                let body = prog.body(&method).unwrap();
                let ob = body.obligation(id);
                if !ob.kind.is_assertion() {
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
            if assertion_only {
                " (assertion-only)"
            } else {
                ""
            }
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
        if let Some(&declared) = self.declared.get(&producer) {
            if declared != direction {
                return self.reject(format!(
                    "{producer} declared {declared:?} but published as {direction:?}"
                ));
            }
        }

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
            if self.total_assertions > 0 {
                // Program has assertions but none were reachable — incomplete
                // reachability analysis. Return Unknown rather than vacuous TRUE.
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
    fn declared_direction_must_match_the_published_one() {
        // The hole this closes: the gate reads the direction passed to
        // `publish`, so an engine could declare Over and publish Under (or the
        // reverse) and never be caught. NraEngine actually did.
        let mut bb = Blackboard::new();
        bb.register_engine(EngineId("nra"), Direction::Over);
        let r = bb.publish(
            EngineId("nra"),
            Direction::Under,
            Artifact::Status(
                oref(),
                Status::Violated {
                    by: EngineId("nra"),
                    witness: Default::default(),
                },
            ),
        );
        assert!(
            r.is_err(),
            "a direction that disagrees with the declaration is rejected"
        );
    }

    #[test]
    fn matching_declared_direction_is_accepted() {
        let mut bb = Blackboard::new();
        bb.register_engine(EngineId("concrete"), Direction::Under);
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

    #[test]
    fn unregistered_engines_are_gated_on_the_passed_direction_alone() {
        // Engines built outside an orchestrator (unit tests) are not
        // registered; the original direction gate must still apply.
        let mut bb = Blackboard::new();
        let r = bb.publish(
            EngineId("ad-hoc"),
            Direction::Over,
            Artifact::Status(
                oref(),
                Status::Violated {
                    by: EngineId("ad-hoc"),
                    witness: Default::default(),
                },
            ),
        );
        assert!(r.is_err(), "over-approximating engines may not violate");
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
