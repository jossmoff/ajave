//! The schedule.
//!
//! Falsify before prove: bugs are cheap to find and cheap to certify, and one
//! ends the task immediately. Proofs are expensive and only worth starting once
//! the cheap exit is closed off.

use crate::artifact::{EngineId, Interest, Status};
use crate::blackboard::Blackboard;
use crate::engine::{Budget, Engine, Progress};
use ajave_ir::verdict::Verdict;
use ajave_ir::Program;
use log::{debug, info};

/// Below this, a slice is not worth the cost of entering an engine: solver
/// startup alone eats it, and the step returns having done nothing but consume
/// the tail of the budget.
const MIN_SLICE: std::time::Duration = std::time::Duration::from_millis(250);

/// A scheduling fraction from the environment, for sweeping without rebuilding.
///
/// `CLAUDE.md` records a rebuild mid-run as a hazard that cost three
/// measurements in one day, and a constant sweep is precisely a run per point.
/// Values outside `(0, 1]` are ignored rather than clamped: a typo should not
/// silently produce a different schedule than the one being swept.
fn env_share(name: &str, default: f64) -> f64 {
    match std::env::var(name).ok().and_then(|v| v.parse::<f64>().ok()) {
        Some(v) if v > 0.0 && v <= 1.0 => v,
        Some(v) => {
            log::warn!("orchestrator: ignoring {name}={v}, not in (0, 1]");
            default
        }
        None => default,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    Presolve,
    Falsify,
    Prove,
    Refine,
    Report,
}

pub struct Orchestrator {
    pub engines: Vec<Box<dyn Engine>>,
    pub bb: Blackboard,
    pub phase: Phase,
    pub budget: Budget,
    pub trace: Vec<String>,
    pub assertion_only: bool,
    /// When the whole verification must be finished, if known.
    ///
    /// Set from `--timeout`. Without it the run is unbounded, which is what
    /// every invocation did before and remains the default.
    pub deadline: Option<std::time::Instant>,
    /// Ceiling on a single engine step's slice, as a fraction of the time
    /// remaining.
    ///
    /// A share rather than an equal split, because the engines are not equally
    /// valuable and the order already encodes that: `interval-ai` and
    /// `smt-bmc` discharge on 119 and 30 of 172 sampled tasks respectively,
    /// and the four behind them on none. Splitting evenly would starve the two
    /// that work in order to feed four that do not.
    ///
    /// The point is only to stop one engine taking *everything*.
    pub engine_cap: f64,
    /// Fraction of the remaining time one *round* may consume.
    ///
    /// `engine_cap` alone was enough while there was only ever one round: six
    /// engines at 0.6 of the remainder leave `0.4^6` — four parts in a
    /// thousand — which is correct when nothing is coming after them and
    /// useless when a resumed engine is. The per-engine share is derived from
    /// this so that a full round lands on `round_share` regardless of how many
    /// engines are live, and the geometry across rounds is what gives early
    /// rounds more time than late ones.
    pub round_share: f64,
}

impl Orchestrator {
    pub fn new(engines: Vec<Box<dyn Engine>>) -> Self {
        Orchestrator {
            engines,
            bb: Blackboard::new(),
            phase: Phase::Presolve,
            budget: Budget::default(),
            trace: Vec::new(),
            assertion_only: true,
            deadline: None,
            engine_cap: env_share("AJAVE_ENGINE_CAP", 0.6),
            round_share: env_share("AJAVE_ROUND_SHARE", 0.7),
        }
    }

    /// Time until the run must be finished, if a deadline is known.
    fn time_left(&self) -> Option<std::time::Duration> {
        self.deadline
            .map(|end| end.saturating_duration_since(std::time::Instant::now()))
    }

    /// The fraction of the remaining time one engine step may take.
    ///
    /// **Round 0 is scheduled exactly as before.** It is the run every number
    /// in `changes.md` was measured on, so the resumption machinery has to be
    /// strictly additive to it — the same rule the deepening passes follow, for
    /// the same reason. Deriving a share from `round_share` here instead gave
    /// thirteen live engines 0.088 of the remainder apiece where they used to
    /// get 0.6, which is a different first round and therefore a different
    /// baseline, measured against nothing.
    ///
    /// From round 1 the geometry applies: a full round of `live` steps consumes
    /// `round_share` of what was left, because each step takes `share` of the
    /// *remainder* and `(1 - share)^live = 1 - round_share` solves to the
    /// expression below. Still capped by `engine_cap`, so a round with one live
    /// engine cannot hand it everything.
    ///
    /// At the defaults: one live engine gets 0.6; six get 0.188 each and the
    /// round lands on 0.7.
    fn slice_share(&self, round: usize, live: usize) -> f64 {
        if round == 0 {
            return self.engine_cap;
        }
        let live = live.max(1) as f64;
        let per_round = 1.0 - (1.0 - self.round_share).powf(1.0 / live);
        self.engine_cap.min(per_round)
    }

    pub fn run(&mut self, prog: &Program, max_rounds: usize) -> Verdict {
        info!(
            "orchestrator: starting with {} engines, max_rounds={}",
            self.engines.len(),
            max_rounds
        );
        self.bb.seed(prog, self.assertion_only);
        // Per-engine wall clock. Timeouts dominate the score far more than
        // precision does, and twice now a performance regression has been
        // misattributed by reasoning about the code instead of measuring it.
        // This makes the attribution a fact rather than a hypothesis.
        let mut init_ms: Vec<(EngineId, u128)> = Vec::new();
        let mut step_ms: std::collections::HashMap<String, u128> = std::collections::HashMap::new();
        let mut discharged_by: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        let mut violated_by: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        for e in self.engines.iter_mut() {
            debug!("orchestrator: initialising engine {}", e.id());
            let t0 = std::time::Instant::now();
            e.init(prog, &mut self.bb);
            init_ms.push((e.id(), t0.elapsed().as_millis()));
        }

        // Per-engine scheduling state. Cursors live here rather than inside the
        // engines on purpose: an engine that forgets to advance its own cursor
        // silently disables its skip test, and one that advances it twice
        // silently drops artifacts. Both failures are invisible. Here it is
        // advanced in exactly one place, immediately after the step.
        struct EngineState {
            retired: bool,
            /// The last step stopped on the clock with work outstanding.
            suspended: bool,
            /// Blackboard head at the end of this engine's last step.
            cursor: u64,
            steps: u32,
        }
        let mut state: Vec<EngineState> = (0..self.engines.len())
            .map(|_| EngineState {
                retired: false,
                suspended: false,
                cursor: 0,
                steps: 0,
            })
            .collect();
        // Fixed for the run: `interest` is a declaration about the engine, not
        // about its current state.
        let interests: Vec<Interest> = self.engines.iter().map(|e| e.interest()).collect();
        let ids: Vec<EngineId> = self.engines.iter().map(|e| e.id()).collect();

        for round in 0..max_rounds {
            if self.phase == Phase::Report {
                break;
            }
            if self.time_left().is_some_and(|left| left < MIN_SLICE) {
                debug!("orchestrator: stopping at round {round}, too little time left to slice");
                break;
            }

            // Who is worth running this round.
            //
            // `steps == 0` is not redundant with the delta test, and leaving it
            // out answers UNKNOWN on every task: `Blackboard::seed` inserts
            // statuses directly and publishes nothing to the log, so at round 0
            // the log is empty and `changed_since(0, ANY)` is false for
            // everyone.
            let live: Vec<usize> = (0..self.engines.len())
                .filter(|&i| {
                    let st = &state[i];
                    !st.retired
                        && (st.steps == 0
                            || st.suspended
                            || self.bb.changed_since(st.cursor, interests[i]))
                })
                .collect();
            if live.is_empty() {
                debug!("orchestrator: round {round}: nothing live, stopping");
                break;
            }
            let share = self.slice_share(round, live.len());

            let mut advanced = false;
            let mut ran = 0usize;
            for &i in &live {
                // Note: no short-circuit on violations. Over-approximating
                // engines (CHC, k-induction) should still run to discharge
                // obligations that BMC couldn't determine. BMC may publish
                // spurious violations on tainted paths; the CHC engine can
                // prove those obligations safe by looking at open obligations
                // (which exclude already-Violated finals).
                // Count both directions. Under-approximating engines (NRA,
                // concrete) publish *violations*, never discharges, so scoring
                // them by discharges alone reads as "contributes nothing" when
                // they may be earning FALSEs. Same mistake, opposite sign, as
                // judging an Over engine by violations.
                // Count *published* discharges, not stored ones. A discharge
                // published after a violation is discarded from `statuses`
                // (first final status wins) yet still steers the verdict
                // through `verdict_excluding` — so counting stored statuses
                // reported "no discharges" for the very publication that
                // decided the answer (#66).
                let before = self.bb.proved_safe_count();
                let before_v = self
                    .bb
                    .statuses()
                    .filter(|(_, s)| matches!(s, Status::Violated { .. }))
                    .count();
                // Slice the remaining time so neither one engine nor one round
                // can consume it all. Recomputed per step, so time an engine
                // leaves on the table is recycled by the ones behind it.
                let mut budget = self.budget;
                if let Some(left) = self.time_left() {
                    if left < MIN_SLICE {
                        debug!("orchestrator: round {round}: out of time mid-round");
                        break;
                    }
                    budget.deadline = Some(std::time::Instant::now() + left.mul_f64(share));
                }
                let t0 = std::time::Instant::now();
                let progress = self.engines[i].step(prog, &mut self.bb, budget);
                ran += 1;
                // The one place a cursor moves.
                state[i].cursor = self.bb.head();
                state[i].steps += 1;
                *step_ms.entry(ids[i].0.to_string()).or_default() += t0.elapsed().as_millis();
                let after = self.bb.proved_safe_count();
                let after_v = self
                    .bb
                    .statuses()
                    .filter(|(_, s)| matches!(s, Status::Violated { .. }))
                    .count();
                if after > before {
                    *discharged_by.entry(ids[i].0.to_string()).or_default() += after - before;
                }
                if after_v > before_v {
                    *violated_by.entry(ids[i].0.to_string()).or_default() += after_v - before_v;
                }
                state[i].suspended = progress == Progress::Suspended;
                match progress {
                    Progress::Advanced => advanced = true,
                    Progress::Suspended | Progress::Blocked => {}
                    Progress::Exhausted => {
                        debug!("orchestrator: engine {} exhausted, retiring", ids[i]);
                        state[i].retired = true;
                    }
                }
            }
            let skipped = self.engines.len() - ran;

            let open = self.bb.open().len();
            let violated = self
                .bb
                .statuses()
                .any(|(_, s)| matches!(s, Status::Violated { .. }));

            let msg = format!(
                "round {round}: phase={:?} open={open} advanced={advanced} ran={ran} skipped={skipped}",
                self.phase
            );
            debug!("orchestrator: {msg}");
            self.trace.push(msg);

            // A question nobody has answered is unfinished business, even if
            // every obligation is closed. The BMC routinely *closes* an
            // obligation with a violation derived from an unconstrained
            // `Math.sin`, and the answer that would settle it arrives a round
            // later — so terminating on `open == 0` alone ended the run in
            // exactly the case that motivated asking.
            let outstanding = !self.bb.unanswered().is_empty();
            self.phase = self.next_phase(
                open,
                violated,
                advanced,
                state.iter().all(|st| st.retired),
                outstanding,
            );
        }

        for (id, ms) in &init_ms {
            if *ms > 0 {
                info!("orchestrator: timing init {} {}ms", id, ms);
            }
        }
        let mut steps: Vec<_> = step_ms.iter().collect();
        steps.sort_by_key(|(_, ms)| std::cmp::Reverse(**ms));
        for (id, ms) in steps {
            if *ms > 0 {
                info!(
                    "orchestrator: timing step {} {}ms discharged={} violated={}",
                    id,
                    ms,
                    discharged_by.get(id).copied().unwrap_or(0),
                    violated_by.get(id).copied().unwrap_or(0)
                );
            }
        }

        // What is still open, and of what kind.
        //
        // Without this the only way to ask "why is this task UNKNOWN" was to
        // read each engine's own refusal log and hope one of them mentioned
        // the obligation that mattered. A survey of the unproven corpus needs
        // the answer directly: an UNKNOWN verdict is one or more obligations
        // nobody closed, and their *kind* is what says which engine ought to
        // have.
        let still_open = self.bb.open();
        if !still_open.is_empty() {
            let mut by_kind: std::collections::BTreeMap<String, usize> =
                std::collections::BTreeMap::new();
            for oref in &still_open {
                let kind = prog
                    .body(&oref.method)
                    .map(|b| format!("{:?}", b.obligation(oref.id).kind))
                    .unwrap_or_else(|| "?".to_string());
                *by_kind.entry(kind).or_default() += 1;
            }
            let summary = by_kind
                .iter()
                .map(|(k, n)| format!("{k}={n}"))
                .collect::<Vec<_>>()
                .join(" ");
            info!(
                "orchestrator: {} obligation(s) still open — {}",
                still_open.len(),
                summary
            );
            for oref in still_open.iter().take(6) {
                if let Some(b) = prog.body(&oref.method) {
                    let ob = b.obligation(oref.id);
                    debug!(
                        "orchestrator:   open {:?} in {}.{} line={:?} bytecode={}",
                        ob.kind, oref.method.class, oref.method.name, ob.line, ob.bytecode_offset
                    );
                }
            }
        }

        let verdict = self.bb.verdict();
        info!("orchestrator: done, verdict={verdict:?}");
        verdict
    }

    /// The schedule state machine from ARCHITECTURE.md section 4.
    fn next_phase(
        &self,
        open: usize,
        _violated: bool,
        advanced: bool,
        all_retired: bool,
        questions_outstanding: bool,
    ) -> Phase {
        if all_retired {
            return Phase::Report;
        }
        if open == 0 && !questions_outstanding {
            return Phase::Report;
        }
        match self.phase {
            Phase::Presolve => Phase::Falsify,
            Phase::Falsify => {
                if advanced {
                    Phase::Falsify
                } else {
                    Phase::Prove
                }
            }
            Phase::Prove => {
                if advanced {
                    Phase::Prove
                } else {
                    Phase::Refine
                }
            }
            Phase::Refine => {
                if advanced {
                    Phase::Falsify
                } else {
                    Phase::Report
                }
            }
            Phase::Report => Phase::Report,
        }
    }
}

#[cfg(test)]
mod scheduling_tests {
    use super::*;
    use crate::artifact::{Artifact, Direction, ObligationRef, Status};
    use ajave_ir::{
        Block, BlockId, Body, Const, MethodKey, Obligation, ObligationId, ObligationKind, Operand,
        Stmt, Terminator, VarInfo, VarKind,
    };

    /// One reachable, never-discharged obligation.
    ///
    /// The loop needs it: `next_phase` moves straight to `Report` when nothing
    /// is open, so a program with no obligations ends after round 0 and every
    /// multi-round property below would pass vacuously.
    fn one_open_obligation() -> Program {
        let mk = MethodKey {
            class: "Main".into(),
            name: "main".into(),
            desc: "()V".into(),
        };
        let mut prog = Program::default();
        prog.bodies.insert(
            mk.clone(),
            Body {
                is_static: true,
                key: mk.clone(),
                entry: BlockId(0),
                vars: vec![VarInfo {
                    kind: VarKind::Local(0),
                    ty: ajave_ir::Ty::Int,
                }],
                obligations: vec![Obligation {
                    id: ObligationId(0),
                    kind: ObligationKind::Assertion,
                    cond: Operand::Const(Const::Int(0)),
                    guarded: false,
                    bytecode_offset: 1,
                    line: None,
                }],
                blocks: vec![Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![Stmt::Check(ObligationId(0))],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                }],
            },
        );
        prog.entry = Some(mk);
        prog
    }

    fn oref(prog: &Program) -> ObligationRef {
        ObligationRef {
            method: prog.entry.clone().unwrap(),
            id: ObligationId(0),
        }
    }

    /// Returns a scripted sequence of `Progress`, recording every entry.
    struct Scripted {
        id: EngineId,
        interest: Interest,
        script: Vec<Progress>,
        /// Entries on which to publish an `Invariant` — an artifact no test
        /// engine sees unless it declared an interest in it.
        publish_on: Vec<u32>,
        entries: std::rc::Rc<std::cell::RefCell<Vec<u32>>>,
        seen: u32,
    }

    impl Scripted {
        fn new(id: &'static str, interest: Interest, script: Vec<Progress>) -> Self {
            Scripted {
                id: EngineId(id),
                interest,
                script,
                publish_on: Vec::new(),
                entries: Default::default(),
                seen: 0,
            }
        }
    }

    impl Engine for Scripted {
        fn id(&self) -> EngineId {
            self.id
        }
        fn direction(&self) -> Direction {
            Direction::Over
        }
        fn interest(&self) -> Interest {
            self.interest
        }
        fn step(&mut self, _prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
            self.entries.borrow_mut().push(self.seen);
            if self.publish_on.contains(&self.seen) {
                let _ = bb.publish(
                    self.id,
                    Direction::Over,
                    Artifact::Invariant(crate::artifact::Invariant {
                        id: 0,
                        at: crate::artifact::ProgramPoint {
                            method: MethodKey {
                                class: "Main".into(),
                                name: "main".into(),
                                desc: "()V".into(),
                            },
                            block: BlockId(0),
                            index: 0,
                        },
                        formula: crate::term::Expr::Bool(true),
                        status: crate::artifact::InvStatus::Candidate,
                    }),
                );
            }
            let p = self
                .script
                .get(self.seen as usize)
                .copied()
                .unwrap_or(Progress::Blocked);
            self.seen += 1;
            p
        }
    }

    fn run_with(engines: Vec<Box<dyn Engine>>, rounds: usize) -> Orchestrator {
        let mut o = Orchestrator::new(engines);
        o.run(&one_open_obligation(), rounds);
        o
    }

    /// The point of the cursor. A `Blocked` engine has said that more time
    /// alone will not help, so re-entering it before its inputs change costs a
    /// step and cannot change the answer — which, over thirteen engines and
    /// sixteen rounds, is the whole budget.
    #[test]
    fn a_blocked_engine_is_not_re_entered_until_its_interest_changes() {
        let e = Scripted::new("blocked", Interest::INVARIANT, vec![Progress::Blocked; 8]);
        let entries = e.entries.clone();
        run_with(vec![Box::new(e)], 8);
        assert_eq!(
            entries.borrow().len(),
            1,
            "nothing published an Invariant, so one entry is all it should get"
        );
    }

    /// And the other half: an engine that declares an interest must actually
    /// be woken when it is satisfied, or the rule is sound and useless.
    #[test]
    fn a_blocked_engine_is_re_entered_when_its_interest_is_published() {
        let reader = Scripted::new("reader", Interest::INVARIANT, vec![Progress::Blocked; 8]);
        let entries = reader.entries.clone();
        let mut writer = Scripted::new("writer", Interest::NOTHING, vec![Progress::Advanced]);
        writer.publish_on = vec![0];
        run_with(vec![Box::new(reader), Box::new(writer)], 8);
        assert_eq!(
            entries.borrow().len(),
            2,
            "an Invariant landed after it blocked; it should have been woken"
        );
    }

    /// An engine that stopped on the clock needs no new information — the
    /// information it lacks is time. This is the case the three-way `Progress`
    /// could not express, and the reason the round loop was inert.
    #[test]
    fn a_suspended_engine_is_re_entered_with_no_new_artifacts() {
        let e = Scripted::new(
            "suspended",
            // Declares that it reads nothing at all, so only suspension can
            // bring it back.
            Interest::NOTHING,
            vec![Progress::Suspended, Progress::Suspended, Progress::Blocked],
        );
        let entries = e.entries.clone();
        run_with(vec![Box::new(e)], 8);
        assert_eq!(
            entries.borrow().len(),
            3,
            "two suspensions earn two re-entries; the Blocked ends it"
        );
    }

    /// `Blackboard::seed` writes statuses directly and publishes nothing to the
    /// log, so at round 0 the log is empty and the delta test is false for
    /// every engine. Without the `steps == 0` clause the portfolio never runs
    /// and every task answers UNKNOWN.
    #[test]
    fn an_engine_that_has_never_stepped_is_always_live() {
        let e = Scripted::new("cold", Interest::NOTHING, vec![Progress::Blocked]);
        let entries = e.entries.clone();
        run_with(vec![Box::new(e)], 4);
        assert_eq!(entries.borrow().len(), 1, "it must get its first entry");
    }

    /// The `Suspended` contract in `engine.rs` says an engine may only suspend
    /// while a bounded precision parameter is still rising. An engine that
    /// ignores that must still not hang the tool, because most invocations —
    /// every unit test, most `just` recipes — pass no `--timeout` at all and so
    /// have no deadline to fall back on.
    #[test]
    fn an_engine_that_always_suspends_terminates_without_a_deadline() {
        let e = Scripted::new("greedy", Interest::NOTHING, vec![Progress::Suspended; 64]);
        let entries = e.entries.clone();
        let o = run_with(vec![Box::new(e)], 5);
        assert!(o.deadline.is_none());
        let n = entries.borrow().len();
        assert!(
            n > 1,
            "it suspended, so it must have been resumed at least once"
        );
        assert!(n <= 5, "it must not outrun max_rounds; got {n}");
    }

    /// An engine does not wake itself. The cursor is advanced *after* the step,
    /// so an artifact an engine published during its own step is behind its own
    /// cursor — otherwise any engine that publishes and reads the same kind
    /// would spin until `max_rounds` on every task.
    #[test]
    fn an_engine_is_not_woken_by_its_own_publication() {
        let mut e = Scripted::new("selfish", Interest::INVARIANT, vec![Progress::Advanced; 8]);
        e.publish_on = (0..8).collect();
        let entries = e.entries.clone();
        run_with(vec![Box::new(e)], 6);
        assert_eq!(entries.borrow().len(), 1);
    }

    /// `max_rounds` specifically, with the phase machine unable to help: two
    /// engines that read each other's artifacts and report `Advanced` keep
    /// `Phase::Falsify` from ever moving on and keep each other live forever.
    /// Only the round cap ends this.
    #[test]
    fn max_rounds_bounds_two_engines_that_keep_feeding_each_other() {
        let mut a = Scripted::new("ping", Interest::INVARIANT, vec![Progress::Advanced; 64]);
        a.publish_on = (0..64).collect();
        let mut b = Scripted::new("pong", Interest::INVARIANT, vec![Progress::Advanced; 64]);
        b.publish_on = (0..64).collect();
        let o = run_with(vec![Box::new(a), Box::new(b)], 6);
        assert_eq!(
            o.trace.len(),
            6,
            "the round cap is the only thing stopping this"
        );
    }

    /// One cursor advance per step. Too few and the engine is woken every
    /// round forever on artifacts it has already seen; too many and it misses
    /// the one that would unblock it. Both are silent, which is why the
    /// orchestrator owns this and the engines do not.
    ///
    /// Two publications, two wake-ups, and no third: a lagging cursor would
    /// give more entries than publications, a leading one fewer.
    #[test]
    fn a_cursor_advances_exactly_once_per_step() {
        let reader = Scripted::new("reader", Interest::INVARIANT, vec![Progress::Blocked; 8]);
        let entries = reader.entries.clone();
        // Suspends so it stays live long enough to publish twice.
        let mut writer = Scripted::new(
            "writer",
            Interest::NOTHING,
            vec![Progress::Suspended, Progress::Advanced],
        );
        writer.publish_on = vec![0, 1];
        run_with(vec![Box::new(reader), Box::new(writer)], 8);
        assert_eq!(
            entries.borrow().len(),
            3,
            "one initial entry plus one per publication, and nothing more"
        );
    }

    /// A round of `n` engines lands on `round_share` of what was left, and one
    /// engine never exceeds `engine_cap`. Without the first, six engines at the
    /// old flat 0.6 left four parts in a thousand for everything after them.
    #[test]
    fn a_round_never_consumes_the_whole_remaining_time() {
        let o = Orchestrator::new(vec![]);
        for live in 1..=12 {
            let share = o.slice_share(1, live);
            let consumed = 1.0 - (1.0 - share).powi(live as i32);
            assert!(
                consumed <= o.round_share + 1e-9,
                "a round of {live} consumed {consumed}"
            );
            assert!(share <= o.engine_cap + 1e-9, "{live} engines got {share}");
        }
    }

    /// The no-regression pin on the allocator: round 0 is sliced at exactly
    /// the flat constant this replaced, whatever the engine count. P1 and P2
    /// are predicted to measure as zero, and this is the property that makes
    /// the prediction defensible rather than hopeful.
    #[test]
    fn round_zero_is_sliced_exactly_as_before() {
        let o = Orchestrator::new(vec![]);
        for live in 1..=13 {
            assert!((o.slice_share(0, live) - 0.6).abs() < 1e-12);
        }
        // ...and the geometry does apply once resumption is what is being
        // scheduled, or the round cap would be unenforceable.
        assert!(o.slice_share(1, 6) < 0.2);
    }

    /// Retirement still wins over everything else: an `Exhausted` engine is
    /// gone whatever it declared an interest in.
    #[test]
    fn an_exhausted_engine_is_never_re_entered() {
        let reader = Scripted::new("reader", Interest::ANY, vec![Progress::Exhausted]);
        let entries = reader.entries.clone();
        let mut writer = Scripted::new("writer", Interest::NOTHING, vec![Progress::Advanced; 8]);
        writer.publish_on = vec![0, 1];
        run_with(vec![Box::new(reader), Box::new(writer)], 8);
        assert_eq!(entries.borrow().len(), 1);
    }

    /// A published `Status` closes the obligation and the run ends, so this
    /// also pins that the cursor machinery did not break termination.
    #[test]
    fn the_loop_still_ends_when_the_last_obligation_closes() {
        struct Closer(std::rc::Rc<std::cell::RefCell<Vec<u32>>>);
        impl Engine for Closer {
            fn id(&self) -> EngineId {
                EngineId("closer")
            }
            fn direction(&self) -> Direction {
                Direction::Over
            }
            fn interest(&self) -> Interest {
                Interest::NOTHING
            }
            fn step(&mut self, prog: &Program, bb: &mut Blackboard, _b: Budget) -> Progress {
                self.0.borrow_mut().push(0);
                let _ = bb.publish(
                    EngineId("closer"),
                    Direction::Over,
                    Artifact::Status(
                        oref(prog),
                        Status::Discharged {
                            by: EngineId("closer"),
                            proof: crate::artifact::ProofKind::Trivial,
                        },
                    ),
                );
                Progress::Suspended
            }
        }
        let calls: std::rc::Rc<std::cell::RefCell<Vec<u32>>> = Default::default();
        run_with(vec![Box::new(Closer(calls.clone()))], 8);
        assert_eq!(
            calls.borrow().len(),
            1,
            "nothing left open, so no second round even though it suspended"
        );
    }
}
