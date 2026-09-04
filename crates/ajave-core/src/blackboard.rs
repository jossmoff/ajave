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
    /// Does the program under analysis start threads?
    ///
    /// Gates the discharge rule below. Set from `seed`, which is the only
    /// place the blackboard sees the program.
    concurrent_program: bool,
    next_seq: u64,
    next_inv: u32,
    pub rejections: Vec<String>,
    /// Total assertion obligations in the program (seeded + unreachable).
    /// Used to detect vacuous TRUE when reachability is incomplete.
    total_assertions: usize,
    /// Whether we are checking only assertions (valid-assert property).
    /// When false (no-runtime-exception), the vacuous-TRUE guard is skipped.
    assertion_only: bool,
    /// Open questions, and the answers they have attracted.
    ///
    /// Kept beside the log rather than only in it, because the point of a
    /// query is that someone can find it without replaying history.
    queries: Vec<Query>,
    lemmas: Vec<(Lemma, Approximations)>,
    next_query: u32,
    /// What the producer of each obligation's *current* status approximated.
    ///
    /// Kept beside `statuses` rather than inside `Status` because it is a fact
    /// about how the status was derived, not about the obligation, and every
    /// existing match on `Status` would otherwise have to be touched.
    status_approx: BTreeMap<ObligationRef, Approximations>,
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
        self.concurrent_program = prog.uses_concurrency();
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
    /// Publish an artifact the producer modelled faithfully.
    ///
    /// Engines whose encoding approximates part of the JVM's semantics must use
    /// `publish_with` and say so, or a more faithful engine will never be
    /// offered the obligation they closed.
    pub fn publish(
        &mut self,
        producer: EngineId,
        direction: Direction,
        artifact: Artifact,
    ) -> Result<u64, Rejected> {
        self.publish_with(producer, direction, Approximations::EXACT, artifact)
    }

    pub fn publish_with(
        &mut self,
        producer: EngineId,
        direction: Direction,
        approximated: Approximations,
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
                // An engine that does not model threads may not prove anything
                // about a program that starts them.
                //
                // `Thread.start()` is not a call a sequential engine follows,
                // so to one of them the thread simply never runs. Any
                // obligation whose reachability depends on another thread's
                // writes then looks unreachable and is discharged as proven.
                // `UnsafePublicationSeesStaleData` is the case: the reader's
                // `if (ready == 1)` is dead if nothing ever sets `ready`, so
                // the assertion inside it was "proved" -- a wrong TRUE for the
                // canonical unsafe-publication bug.
                //
                // The violation side of the same blind spot was already
                // handled, by refuting candidates at replay. Nothing guarded
                // the proof side, which is the more expensive direction.
                (_, Status::Discharged { .. })
                    if self.concurrent_program && producer != EngineId("concurrency") =>
                {
                    return self.reject(format!(
                        "{producer} does not model threads and may not discharge {oref} \
                         in a program that starts them"
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

        // A lemma is a claim, and the same discipline governs it as governs a
        // status: an engine that has looked at only some executions may not
        // make a statement about all of them. Without this, an Under engine
        // could publish `Holds` and a prover could assume it — a proof resting
        // on a partial search, which is the wrong-TRUE shape the direction
        // rule exists to prevent.
        if let Artifact::Lemma(l) = &artifact {
            if l.answer.is_universal() && direction == Direction::Under {
                return self.reject(format!(
                    "{producer} is under-approximating and may not answer \
                     query {} with a claim about every execution",
                    l.query
                ));
            }
            if !l.answer.is_universal()
                && !matches!(l.answer, Answer::Unknown)
                && direction == Direction::Over
            {
                return self.reject(format!(
                    "{producer} is over-approximating and may not answer \
                     query {} with a witness",
                    l.query
                ));
            }
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
                        self.status_approx.insert(oref.clone(), approximated);
                    }
                }
            }
            Artifact::Invariant(inv) => self.invariants.push(inv.clone()),
            Artifact::Trace(t) => self.traces.push(t.clone()),
            Artifact::Query(q) => self.queries.push(q.clone()),
            Artifact::Lemma(l) => self.lemmas.push((l.clone(), approximated)),
            _ => {}
        }

        self.log.push(Tagged {
            seq,
            producer,
            direction,
            approximated,
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

    /// Obligations this engine should be offered, given what it models
    /// faithfully that others do not.
    ///
    /// `models_faithfully` is what the *caller* gets right. An obligation whose
    /// status was derived under an approximation the caller does not make is
    /// still that engine's business: the answer on the board was computed about
    /// a program that is not quite ours, and this engine can do better.
    ///
    /// The caller must fix **everything** the closer got wrong, not merely
    /// something. An engine that models float arithmetic faithfully cannot
    /// improve on an obligation that also failed because a call was left
    /// unmodelled — a better float encoding does not conjure a model of
    /// `Math.sin`. Reclaiming it anyway is pure cost, and the first engine
    /// census measured exactly that: the FPA escalation pass consumed 63% of
    /// all engine wall time and decided one task in 142, with 36 of its 51
    /// seconds spent on transcendental programs where SMT-LIB's FloatingPoint
    /// theory has nothing to say.
    ///
    /// This is the general form of `open_or_unconfirmed`, which hard-codes one
    /// instance of the same idea (an Under engine's witness is a candidate
    /// until replay confirms it). Both are cases of "a status is only as good
    /// as the model it came from".
    ///
    /// Note the deliberate asymmetry with soundness: this only ever *widens*
    /// what an engine looks at relative to `open()`, so a wrong answer here
    /// costs time, never correctness. Nothing can be discharged that could not
    /// be already.
    pub fn open_for(&self, models_faithfully: Approximations) -> Vec<ObligationRef> {
        self.statuses
            .iter()
            .filter(|(oref, s)| {
                if !s.is_final() {
                    return true;
                }
                let approx = self
                    .status_approx
                    .get(*oref)
                    .copied()
                    .unwrap_or(Approximations::EXACT);
                // Something to fix, and nothing left over that this engine
                // would not fix.
                approx.intersects(models_faithfully)
                    && approx.difference(models_faithfully).is_exact()
            })
            .map(|(k, _)| k.clone())
            .collect()
    }

    /// What the producer of this obligation's current status approximated.
    pub fn status_approximations(&self, oref: &ObligationRef) -> Approximations {
        self.status_approx
            .get(oref)
            .copied()
            .unwrap_or(Approximations::EXACT)
    }

    /// Register a question. Returns its id, which the answers refer to.
    pub fn ask(
        &mut self,
        asked_by: EngineId,
        at: ProgramPoint,
        about: crate::term::Expr,
        want: Want,
        given: Vec<crate::term::Expr>,
    ) -> u32 {
        // Identical questions are one question. An engine re-deriving the same
        // subgoal on twenty paths should not make twenty engines answer it
        // twenty times, and the answer is the same either way.
        if let Some(q) = self.queries.iter().find(|q| {
            q.at == at && q.about == about && q.want == want && q.given == given
        }) {
            return q.id;
        }
        let id = self.next_query;
        self.next_query += 1;
        let q = Query { id, asked_by, at, about, want, given };
        debug!("blackboard: query {id} from {asked_by}: {} ({want:?})", q.about);
        let _ = self.publish(asked_by, Direction::Exact, Artifact::Query(q));
        id
    }

    /// Questions nobody has answered yet.
    pub fn unanswered(&self) -> Vec<&Query> {
        self.queries
            .iter()
            .filter(|q| !self.lemmas.iter().any(|(l, _)| l.query == q.id))
            .collect()
    }

    /// Answers to a question, with what each answerer approximated.
    ///
    /// The approximations travel with the answer for the same reason they
    /// travel with a status: assuming a lemma derived under an approximation
    /// you do not make is assuming a fact about a different program.
    pub fn answers(&self, query: u32) -> Vec<(&Lemma, Approximations)> {
        self.lemmas
            .iter()
            .filter(|(l, _)| l.query == query)
            .map(|(l, a)| (l, *a))
            .collect()
    }

    pub fn query(&self, id: u32) -> Option<&Query> {
        self.queries.iter().find(|q| q.id == id)
    }

    pub fn inductive_invariants(&self) -> impl Iterator<Item = &Invariant> {
        self.invariants
            .iter()
            .filter(|i| i.status == InvStatus::Inductive)
    }

    /// Every invariant claimed at a point in this method, checked or not.
    ///
    /// Deliberately *not* filtered to `Inductive`. A candidate is not a proof
    /// and must never discharge anything — but it is exactly what a Horn
    /// solver wants as a hint, and what a bounded engine wants for pruning.
    /// The consumer decides what it is entitled to do with it, which is the
    /// same split `Status::Bounded { k }` makes.
    pub fn invariants_for(&self, method: &MethodKey) -> Vec<&Invariant> {
        self.invariants
            .iter()
            .filter(|i| &i.at.method == method)
            .collect()
    }

    pub fn pending_traces(&self) -> impl Iterator<Item = &AbstractTrace> {
        self.traces.iter().filter(|t| t.feasible != Some(true))
    }

    /// Whether any interval bounds have been published.
    pub fn has_interval_hints(&self) -> bool {
        self.invariants.iter().any(|i| i.status == InvStatus::Candidate)
    }

    /// Interval bounds for a method, read off the **artifact log**.
    ///
    /// This used to read a bespoke `HashMap` that only the BMC knew about, so
    /// the interval engine's most useful output was invisible to every other
    /// engine — including CHC, for which bounds are candidate invariants and
    /// the most valuable hint a Horn solver can be given. The facts now travel
    /// as `Artifact::Invariant` and anything can read them.
    ///
    /// Recognises the shape the interval engine publishes, `lo <= v && v <= hi`,
    /// and ignores anything else. A consumer that cannot read a claim must
    /// skip it, never guess at it.
    pub fn interval_hints_for_method(
        &self,
        method: &MethodKey,
    ) -> HashMap<(BlockId, VarId), (i64, i64)> {
        use crate::term::{Expr, Op};
        let mut out = HashMap::new();
        for inv in self.invariants.iter().filter(|i| &i.at.method == method) {
            let Expr::Bin(Op::And, lo_e, hi_e) = &inv.formula else { continue };
            let (Expr::Bin(Op::Le, l, lv), Expr::Bin(Op::Le, hv, h)) =
                (lo_e.as_ref(), hi_e.as_ref()) else { continue };
            let (Expr::Int(lo), Expr::Var(v1), Expr::Var(v2), Expr::Int(hi)) =
                (l.as_ref(), lv.as_ref(), hv.as_ref(), h.as_ref()) else { continue };
            if v1 != v2 {
                continue;
            }
            out.insert((inv.at.block, *v1), (*lo, *hi));
        }
        out
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
    /// Obligations that an Over engine proved *and* an Under engine flagged.
    ///
    /// Not a contradiction on its own: a violation is a candidate until JVM
    /// replay confirms it, and the two coexisting is exactly what
    /// `proved_safe` exists to record. It becomes one once the violation is
    /// **confirmed**, because then two engines disagree about a fact of the
    /// program and one of them is wrong.
    ///
    /// The blackboard is the only place that sees both, and checking them
    /// against each other needs no expected-verdict label -- which makes it a
    /// stronger oracle than the corpus, and one that looks *between* engines
    /// rather than inside one. That is where most of the defects found on
    /// 2026-09-02 lived.
    pub fn contested(&self) -> Vec<(ObligationRef, &'static str)> {
        self.statuses
            .iter()
            .filter_map(|(oref, st)| match st {
                Status::Violated { by, .. } if self.proved_safe.contains(oref) => {
                    Some((oref.clone(), by.0))
                }
                _ => None,
            })
            .collect()
    }

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

    /// `publish` only records a status for an obligation that was seeded, and
    /// seeding needs a whole `Program`. These tests are about the bookkeeping,
    /// not about seeding, so they put the obligation on the board directly.
    fn seeded() -> Blackboard {
        let mut bb = Blackboard::new();
        bb.statuses.insert(oref(), Status::Open);
        bb
    }

    fn violate(bb: &mut Blackboard, approx: Approximations) {
        bb.publish_with(
            EngineId("smt-bmc"),
            Direction::Under,
            approx,
            Artifact::Status(
                oref(),
                Status::Violated {
                    by: EngineId("smt-bmc"),
                    witness: Default::default(),
                },
            ),
        )
        .unwrap();
    }

    /// The regression this whole mechanism exists for.
    ///
    /// The cheap BMC pass encodes `dmul` as a bitvector multiply, "finds" a
    /// violation and closes the obligation. The FPA pass, which models the
    /// multiply properly, then skipped the task because `open()` was empty —
    /// and JVM replay refuted the witness with nothing left to reopen it.
    #[test]
    fn a_float_approximated_violation_stays_open_to_an_engine_that_models_floats() {
        let mut bb = seeded();
        violate(&mut bb, Approximations::FLOAT_ARITH);

        assert!(bb.open().is_empty(), "the violation closes it for open()");
        assert_eq!(
            bb.open_for(Approximations::FLOAT_ARITH),
            vec![oref()],
            "but an engine that models float arithmetic must still be offered it"
        );
    }

    #[test]
    fn a_faithfully_derived_violation_closes_the_obligation_for_everyone() {
        let mut bb = seeded();
        violate(&mut bb, Approximations::EXACT);

        assert!(bb.open().is_empty());
        assert!(
            bb.open_for(Approximations::FLOAT_ARITH).is_empty(),
            "nothing was approximated, so there is nothing to do better"
        );
    }

    /// Reopening is targeted, not blanket. An engine only gets an obligation
    /// back when it models something the closer actually got wrong — otherwise
    /// every precise pass would re-explore every task, which measured as a
    /// large regression when the FPA pass did exactly that.
    #[test]
    fn an_unrelated_approximation_does_not_reopen_the_obligation() {
        let mut bb = seeded();
        violate(&mut bb, Approximations::INT_WRAPPING);

        assert!(bb.open_for(Approximations::FLOAT_ARITH).is_empty());
        assert_eq!(bb.open_for(Approximations::INT_WRAPPING), vec![oref()]);
    }

    /// The census finding, as a rule. A better float encoding does not conjure
    /// a model of `Math.sin`, so an obligation that failed for both reasons is
    /// not worth reclaiming — and reclaiming it was 63% of all engine time.
    #[test]
    fn an_engine_must_fix_everything_that_went_wrong_not_merely_something() {
        let mut bb = seeded();
        violate(
            &mut bb,
            Approximations::FLOAT_ARITH.union(Approximations::UNMODELLED_CALL),
        );

        assert!(
            bb.open_for(Approximations::FLOAT_ARITH).is_empty(),
            "fixing the float encoding leaves the unmodelled call unfixed"
        );
        assert_eq!(
            bb.open_for(
                Approximations::FLOAT_ARITH.union(Approximations::UNMODELLED_CALL)
            ),
            vec![oref()],
            "an engine that fixes both should still be offered it"
        );
    }

    /// The reader and the writer of an interval bound must agree on its shape.
    ///
    /// This is the `Bounded { k }` lesson as a test: `ai.rs` writes
    /// `lo <= v && v <= hi` and `interval_hints_for_method` pattern-matches it
    /// back. Nothing in the type system connects the two, so a change to
    /// either silently drops every hint — and losing them costs precision in
    /// the BMC with no error anywhere.
    #[test]
    fn an_interval_bound_survives_the_round_trip() {
        use crate::term::{Expr, Op};
        let mut bb = Blackboard::new();
        let at = point();
        let v = ajave_ir::VarId(7);

        // Exactly what `AiEngine::publish_interval_hints` writes.
        let lo = Expr::bin(Op::Le, Expr::Int(-3), Expr::Var(v));
        let hi = Expr::bin(Op::Le, Expr::Var(v), Expr::Int(42));
        let id = bb.fresh_invariant_id();
        bb.publish(
            EngineId("interval-ai"),
            Direction::Over,
            Artifact::Invariant(Invariant {
                id,
                at: at.clone(),
                formula: Expr::bin(Op::And, lo, hi),
                status: InvStatus::Candidate,
            }),
        )
        .unwrap();

        let hints = bb.interval_hints_for_method(&at.method);
        assert_eq!(hints.get(&(at.block, v)), Some(&(-3, 42)));
        assert!(bb.has_interval_hints());
    }

    /// A claim the reader cannot parse must be skipped, never guessed at.
    #[test]
    fn an_unrecognised_claim_is_ignored_rather_than_misread() {
        use crate::term::{Expr, Op};
        let mut bb = Blackboard::new();
        let at = point();
        let id = bb.fresh_invariant_id();
        bb.publish(
            EngineId("cegar"),
            Direction::Over,
            Artifact::Invariant(Invariant {
                id,
                at: at.clone(),
                // A different shape entirely: v0 != v1.
                formula: Expr::bin(
                    Op::Ne,
                    Expr::Var(ajave_ir::VarId(0)),
                    Expr::Var(ajave_ir::VarId(1)),
                ),
                status: InvStatus::Candidate,
            }),
        )
        .unwrap();
        assert!(bb.interval_hints_for_method(&at.method).is_empty());
    }

    // ── the query/lemma channel ────────────────────────────────────────

    fn point() -> ProgramPoint {
        ProgramPoint { method: oref().method, block: ajave_ir::BlockId(0), index: 0 }
    }

    fn sin_x() -> crate::term::Expr {
        crate::term::Expr::call(
            "java/lang/Math", "sin", "(D)D",
            vec![crate::term::Expr::Var(ajave_ir::VarId(0))],
        )
    }

    /// The same subgoal reached on twenty paths is one question, not twenty.
    /// Without this an engine re-deriving `sin(x)` in a loop would make every
    /// answerer re-answer it for each unrolling.
    #[test]
    fn identical_questions_are_one_question() {
        let mut bb = Blackboard::new();
        let a = bb.ask(EngineId("smt-bmc"), point(), sin_x(), Want::Bounds, vec![]);
        let b = bb.ask(EngineId("smt-bmc"), point(), sin_x(), Want::Bounds, vec![]);
        assert_eq!(a, b);
        assert_eq!(bb.unanswered().len(), 1);
    }

    /// An engine that has looked at only some executions may not make a claim
    /// about all of them. This is the `Direction` rule that governs `Status`,
    /// applied one level down — without it an Under engine could publish
    /// `Holds` and a prover could assume it, resting a proof on a partial
    /// search.
    #[test]
    fn an_under_approximating_engine_may_not_answer_universally() {
        let mut bb = Blackboard::new();
        let q = bb.ask(EngineId("smt-bmc"), point(), sin_x(), Want::Bounds, vec![]);
        let r = bb.publish(
            EngineId("float-search"),
            Direction::Under,
            Artifact::Lemma(Lemma {
                query: q,
                by: EngineId("float-search"),
                answer: Answer::Bounds {
                    lo: crate::term::Expr::double(-1.0),
                    hi: crate::term::Expr::double(1.0),
                },
            }),
        );
        assert!(r.is_err());
        assert!(bb.answers(q).is_empty());
    }

    #[test]
    fn an_over_approximating_engine_may_not_answer_with_a_witness() {
        let mut bb = Blackboard::new();
        let q = bb.ask(EngineId("smt-bmc"), point(), sin_x(), Want::Satisfiable, vec![]);
        let r = bb.publish(
            EngineId("interval-ai"),
            Direction::Over,
            Artifact::Lemma(Lemma {
                query: q,
                by: EngineId("interval-ai"),
                answer: Answer::SatisfiedBy(vec![(ajave_ir::VarId(0), 3)]),
            }),
        );
        assert!(r.is_err());
    }

    /// A bound on `sin` is sound from an over-approximating engine, and the
    /// approximations it was derived under travel with it — assuming a lemma
    /// derived under an approximation you do not make is assuming a fact about
    /// a different program.
    #[test]
    fn an_answer_carries_what_its_author_approximated() {
        let mut bb = Blackboard::new();
        let q = bb.ask(EngineId("smt-bmc"), point(), sin_x(), Want::Bounds, vec![]);
        bb.publish_with(
            EngineId("interval-ai"),
            Direction::Over,
            Approximations::REAL_ARITH,
            Artifact::Lemma(Lemma {
                query: q,
                by: EngineId("interval-ai"),
                answer: Answer::Bounds {
                    lo: crate::term::Expr::double(-1.0),
                    hi: crate::term::Expr::double(1.0),
                },
            }),
        )
        .unwrap();

        let answers = bb.answers(q);
        assert_eq!(answers.len(), 1);
        assert_eq!(answers[0].1, Approximations::REAL_ARITH);
        assert!(bb.unanswered().is_empty());
    }

    /// "I looked and cannot say" is worth publishing: it stops the scheduler
    /// asking the same engine the same question again.
    #[test]
    fn declining_to_answer_is_still_an_answer() {
        let mut bb = Blackboard::new();
        let q = bb.ask(EngineId("smt-bmc"), point(), sin_x(), Want::Bounds, vec![]);
        bb.publish(
            EngineId("nra"),
            Direction::Under,
            Artifact::Lemma(Lemma {
                query: q,
                by: EngineId("nra"),
                answer: Answer::Unknown,
            }),
        )
        .unwrap();
        assert!(bb.unanswered().is_empty());
    }

    #[test]
    fn open_obligations_are_offered_to_everyone_regardless() {
        let bb = seeded();
        assert_eq!(bb.open_for(Approximations::EXACT), vec![oref()]);
        assert_eq!(bb.open_for(Approximations::FLOAT_ARITH), vec![oref()]);
    }

    #[test]
    fn approximation_sets_compose() {
        let both = Approximations::FLOAT_ARITH.union(Approximations::REAL_ARITH);
        assert!(both.contains(Approximations::FLOAT_ARITH));
        assert!(both.contains(Approximations::REAL_ARITH));
        assert!(!both.contains(Approximations::INT_WRAPPING));
        assert!(both.intersects(Approximations::FLOAT_ARITH));
        assert!(!both.intersects(Approximations::INT_WRAPPING));
        assert!(Approximations::EXACT.is_exact());
        assert_eq!(format!("{:?}", both), "float-arith+real-arith");
        assert_eq!(format!("{:?}", Approximations::EXACT), "exact");
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
