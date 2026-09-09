//! SMT-backed bounded model checker.
//!
//! Encodes paths symbolically and asks a solver for satisfying assignments,
//! replacing the concrete engine's "enumerate, don't solve" with "solve, don't
//! enumerate". Finds any bug reachable within bounded depth for arbitrary
//! integer/long inputs, not just a fixed candidate pool.
//!
//! Direction: Under. JvmReplay confirms all witnesses.

mod char_encode;
mod encode;
mod explore;
// Re-exported so the AI engine can apply the same soundness rule: a call whose
// exceptional behaviour we do not model must block an NRE discharge, whichever
// engine is doing the discharging.
pub(crate) use explore::could_throw_runtime_exception;
mod math_encode;
mod merge;
mod str_encode;

use std::collections::{BTreeSet, HashMap, HashSet};

use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_core::smt::{SatResult, Solver, SolverFactory, Term};
use ajave_ir::verdict::{NondetEntry, NondetValue, Witness};
use ajave_ir::*;
use ajave_models;
use log::{debug, info, warn};

/// Field identification key with named fields for type safety.
///
/// `Ord` is required, not cosmetic: merge points iterate the union of two
/// states' field maps to build the merged constraints, and iterating a
/// `HashSet` there gave a different term order on every process. See `merge.rs`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct FK {
    class: String,
    name: String,
    desc: String,
}

impl FK {
    fn new(class: impl Into<String>, name: impl Into<String>, desc: impl Into<String>) -> Self {
        FK {
            class: class.into(),
            name: name.into(),
            desc: desc.into(),
        }
    }
}

/// Maximum number of solver check-sat calls per run to prevent hangs.
const MAX_SOLVER_CALLS: u32 = 10_000;

/// Cap on the parse-case cross product. Two cases per call, so this allows
/// four `parse*` calls on one path before falling back to the unconstrained
/// query.
const MAX_PARSE_COMBINATIONS: usize = 16;

/// Maximum number of violations to collect before stopping exploration.
const MAX_VIOLATIONS: usize = 50;

/// Maximum call inlining depth to prevent infinite recursion.
const MAX_CALL_DEPTH: u32 = 15;

/// Maximum number of times a loop back-edge may be taken on a single path.
const MAX_LOOP_UNROLL: u32 = 5;

/// Maximum total block visits across all paths. Prevents exponential blowup
/// from loops with internal branches: e.g. 5 unrolls × 3 branches per
/// iteration = 2^15 paths, each visiting ~10 blocks = 320k visits.
const MAX_BLOCK_VISITS: u64 = 50_000;

/// Maximum number of path forks. Path forking (as opposed to diamond merging)
/// doubles the work at each fork. This limit prevents exponential blowup.
const MAX_FORKS: u32 = 500;

/// Multiplier on the *resource* caps above — solver calls, block visits,
/// forks. Not on `MAX_CALL_DEPTH` or `MAX_LOOP_UNROLL`, which are semantic
/// bounds that change what `Bounded { k }` means to its consumers.
///
/// This exists to measure a number the blocker census cannot: **what fraction
/// of budget-truncated tasks a bigger budget actually decides.** The census
/// says `all_paths_complete` is the single commonest reason a task does not
/// score (27.9% of unproven valid-assert, 34.3% of no-runtime-exception), but
/// "more effort could decide this" is not "more effort will" — an exploration
/// can be exponentially large, and doubling changes nothing.
///
/// Sweeping this answers that directly, and the answer decides whether
/// iterative deepening is worth building. `CLAUDE.md` asks for exactly this
/// check on every fitted constant; these have never had one.
/// Whether the BMC posts questions to the blackboard and returns for the
/// answers. **Off by default, because it was measured and it does not pay.**
///
/// The mechanism works end to end: the BMC asks for bounds on a call it cannot
/// model, `ranges` answers from the Javadoc, and the second pass assumes the
/// bound. What it does not do is decide anything. A range does not make a path
/// through an unmodelled call *trusted* — the obligation is still refused with
/// `skipped_obligation` because the path is tainted, and taint blocks the check
/// independently of whether a branch was pruned.
///
/// Meanwhile the second pass costs a full re-exploration. On `MathHelper_true`,
/// which is dense in `Math` calls, that took the task from 7.6s to a 60s
/// timeout — one task lost, none gained.
///
/// The negative result is worth more than the feature: the query channel pays
/// when an answerer can supply a *value*, not when it can only bound one.
/// Lifting `FdLibm` would qualify; a range table does not. Kept behind this
/// flag so the next answerer has somewhere to plug in, and so the measurement
/// can be repeated rather than re-argued.
pub fn asking_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("AJAVE_ASK")
            .map(|v| v == "1")
            .unwrap_or(false)
    })
}

fn budget_scale() -> u64 {
    static SCALE: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *SCALE.get_or_init(|| {
        std::env::var("AJAVE_BMC_SCALE")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .filter(|v| *v >= 1)
            .unwrap_or(1)
    })
}

/// Tracks why exploration may be incomplete, replacing ad-hoc boolean flags.
/// Each field records a specific reason the engine cannot fully discharge.
#[derive(Clone, Debug, Default)]
struct Completeness {
    /// All paths were fully explored (no budget cuts, no unhandled throws).
    all_paths_complete: bool,
    /// Every call rvalue was resolved (inlined or math-modelled).
    all_calls_resolved: bool,
    /// A havoced (unresolved) call exists inside a try block, meaning an
    /// exception handler containing an assertion may be unreachable.
    has_unresolved_in_try: bool,
    /// A havoced call exists to a method that could throw a RuntimeException
    /// (e.g. String.substring, Float.parseFloat). For NRE, this blocks
    /// discharge because the exception isn't modelled as an obligation.
    has_potentially_throwing_havoc: bool,
    /// A call was havoced because MAX_CALL_DEPTH was reached (recursion cutoff).
    /// This means the callee's body was not explored — it could contain
    /// assertions reachable via deeper recursion. Blocks relaxed discharge.
    has_depth_limited_havoc: bool,
    /// Some paths had `path_tainted=true` (e.g. float/double imprecision).
    /// This means some obligation checks may have been skipped or never reached
    /// because tainted branch conditions prevented exploration. Blocks relaxed
    /// assertion discharge for non-entry methods.
    has_tainted_paths: bool,
}

impl Completeness {
    fn new() -> Self {
        Completeness {
            all_paths_complete: true,
            all_calls_resolved: true,
            has_unresolved_in_try: false,
            has_potentially_throwing_havoc: false,
            has_depth_limited_havoc: false,
            has_tainted_paths: false,
        }
    }

    /// Which condition in `can_discharge` refuses, for diagnostics.
    ///
    /// Kept beside `can_discharge` and in the same order, so a measurement of
    /// where the points are cannot drift from what the code actually tests.
    /// The distinction matters: `has_tainted_paths` is consulted **only** in
    /// the assertion-only branch, so on the no-runtime-exception property a
    /// set taint flag is not a blocker at all, and counting set flags rather
    /// than refusing ones would put the effort in the wrong place.
    fn discharge_blocker(
        &self,
        method: &MethodKey,
        entry: &MethodKey,
        method_explored: bool,
        assertion_only: bool,
    ) -> Option<&'static str> {
        if !assertion_only && self.has_potentially_throwing_havoc {
            return Some("has_potentially_throwing_havoc");
        }
        if method == entry {
            return self
                .has_unresolved_in_try
                .then_some("has_unresolved_in_try");
        }
        if method_explored {
            if assertion_only
                && !self.has_unresolved_in_try
                && !self.has_depth_limited_havoc
                && !self.has_tainted_paths
            {
                return None;
            }
            if assertion_only {
                if self.has_unresolved_in_try {
                    return Some("has_unresolved_in_try");
                }
                if self.has_depth_limited_havoc {
                    return Some("has_depth_limited_havoc");
                }
                if self.has_tainted_paths {
                    return Some("has_tainted_paths");
                }
            }
            return (!self.all_calls_resolved).then_some("all_calls_resolved");
        }
        if !self.all_paths_complete {
            return Some("all_paths_complete");
        }
        (!self.all_calls_resolved).then_some("all_calls_resolved")
    }

    /// Can we discharge an obligation for `method` given this completeness state?
    ///
    /// For NRE (assertion_only=false), havoced calls to methods that could
    /// throw RuntimeException block discharge — the exception isn't modelled
    /// as an obligation and could cause an undetected runtime exception.
    fn can_discharge(
        &self,
        method: &MethodKey,
        entry: &MethodKey,
        method_explored: bool,
        assertion_only: bool,
    ) -> bool {
        if !assertion_only && self.has_potentially_throwing_havoc {
            return false;
        }
        if method == entry {
            !self.has_unresolved_in_try
        } else if method_explored {
            // For assertions: if there are no unresolved calls in try blocks,
            // havoced calls can only affect values (not control flow to exception
            // handlers). The obligation check was evaluated at every reachable
            // point with the havoced values modeled as unconstrained — if the
            // solver proved it unreachable, that's sound.
            // Guard: has_unresolved_in_try=true means a havoced call in a try
            // block could throw to a handler containing the assertion, so we
            // can't discharge.
            if assertion_only
                && !self.has_unresolved_in_try
                && !self.has_depth_limited_havoc
                && !self.has_tainted_paths
            {
                true
            } else {
                self.all_calls_resolved
            }
        } else {
            self.all_paths_complete && self.all_calls_resolved
        }
    }
}

/// Obligations a truncation at any of `cut_points` could have hidden.
///
/// `all_paths_complete` is a whole-run boolean *and* the outer gate on
/// discharge, so one cut anywhere stops every obligation in the program from
/// being considered. But a cut cannot hide an obligation it cannot reach, and
/// the reachable set is usually far smaller than "everything": measured over
/// tasks stuck at this gate, the share with open obligations in a method that
/// was never truncated is 24 of 24 in `java-ranger-regression`.
///
/// At risk from a cut at `(m, b)`:
///
/// * every obligation in `m` in a block reachable from `b`, including `b`
///   itself — the cut is mid-block, so the rest of that block is unexplored;
/// * every obligation in any method reachable by a call from those blocks,
///   transitively, since the cut means those calls never happened;
///
/// and the caller frames are already in `cut_points`, recorded at the moment of
/// truncation, so a cut inside a callee charges each caller's continuation too.
/// Approximating those by "every method that can call `m`" was tried on paper
/// and is useless: it collapses to the whole program as soon as `main` calls
/// the truncated method.
///
/// Exceptional successors count as edges. Handler code is reachable from a
/// block that can throw, and a claim of having covered everything must include
/// it.
/// Whether a stopped run is entitled to publish `Status::Bounded { k }`.
///
/// `Bounded { k }` is a claim that the search **reached** depth k, and
/// `k-induction` acts on it: when nothing reachable has a back-edge it
/// discharges the obligation outright. So a run that stopped for a reason
/// other than depth has no bounded result to report, and saying it does turns
/// a search that never happened into a proof — a wrong TRUE at -16.
///
/// The four conditions, and which failure each rules out:
///
/// * `!exhausted` and `budget_left` — the run stopped on *depth*, not on the
///   wall clock or a fork/solver-call cap. This is the one the process
///   deadline made reachable: before `8c9d53a` a slice could not expire
///   mid-run, and afterwards it can. It held only because the publish
///   happened to sit inside an `if ... ctx.budget_left()`, which is an
///   invariant maintained by nesting and by nothing else.
/// * `!all_paths_complete` — a complete search is discharged outright and has
///   no need of a bounded status.
/// * `violations_empty` — a bounded status is evidence only when the search
///   was clean; alongside a violation it says nothing a consumer may use.
///
/// A named predicate rather than an enclosing `if`, because the caller is
/// exactly the code an iterative-deepening pass has to restructure, and
/// `CLAUDE.md` asks that a soundness argument stated in a comment have a test
/// named after it. See `bounded_is_not_published_when_the_slice_expired`.
/// How far this engine's work bounds may be raised across resumptions.
///
/// Bounded because `Progress::Suspended` promises it: a strictly increasing but
/// unbounded parameter never reaches `Exhausted`, and a run without
/// `--timeout` — every unit test, most `just` recipes — has no deadline to stop
/// it. Three doublings takes `MAX_FORKS` from 500 to 4000.
const SCALE_CEILING: u64 = 8;

/// Whether a finished pass should be resumed at a higher work bound.
///
/// Iterative deepening, with the parameter chosen from what actually binds. On
/// the tasks that truncate, `handle_branch_fork` exhausts `MAX_FORKS` while
/// `max_depth` is nowhere near — so deepening on depth would re-run an
/// identical exploration and stop in an identical place.
///
/// `clock_expired` is the interesting condition. A pass cut short by its
/// *slice* has not established that its bounds were too small, and resuming it
/// at a higher bound re-runs the same prefix with less time than it had the
/// first time. The counters are the only cut that resumption can answer.
///
/// Note what this does *not* claim: the previously-recorded result that a
/// larger BMC budget converts nothing still stands, and it was measured by
/// raising `AJAVE_BMC_SCALE` for the whole run. The difference here is that the
/// larger bound is paid for out of time nobody else wanted, after every other
/// engine has had its slice — not taken from them up front.
fn should_resume_deeper(
    all_paths_complete: bool,
    exhausted: bool,
    scale: u64,
    anything_open: bool,
    spent: std::time::Duration,
    left: Option<std::time::Duration>,
) -> bool {
    if all_paths_complete || exhausted || !anything_open || scale >= SCALE_CEILING {
        return false;
    }
    match left {
        // Doubling the bound roughly doubles the work, and the restart repeats
        // the prefix as well, so a pass that cost `spent` will cost at least
        // that much again. Entering one with less than that on the clock buys a
        // second truncation and throws away the first result's time.
        Some(left) => left >= spent.mul_f64(RESUME_HEADROOM),
        // No deadline: bounded by SCALE_CEILING, per the `Suspended` contract.
        None => true,
    }
}

/// How much of the pass just finished must still be on the clock before a
/// deeper one is worth starting.
///
/// The first version of this guard asked only whether the clock had *expired*,
/// which is a different question and a much weaker one: with 40% of a slice
/// left it would start a pass costing twice the 60% already spent, truncate it,
/// and report nothing for the whole of it. Measured on the smoke set that was
/// 6x to 20x on individual tasks — `BellmanFord-MemUnsat01` 11s to 72s — for
/// one point. Two, and not one, because the restart repeats the prefix on top
/// of the doubled bound.
const RESUME_HEADROOM: f64 = 2.0;

fn may_publish_bounded(
    exhausted: bool,
    budget_left: bool,
    all_paths_complete: bool,
    violations_empty: bool,
) -> bool {
    !exhausted && budget_left && !all_paths_complete && violations_empty
}

fn obligations_at_risk(
    prog: &Program,
    cut_points: &BTreeSet<(MethodKey, BlockId)>,
) -> HashSet<(MethodKey, ObligationId)> {
    let mut at_risk = HashSet::new();
    // Methods whose obligations are all at risk, because a cut means a call
    // into them may not have happened.
    let mut tainted_methods: BTreeSet<MethodKey> = BTreeSet::new();

    for (mk, start) in cut_points {
        let Some(body) = prog.body(mk) else {
            continue;
        };
        // Blocks reachable from the cut, within this method.
        let mut seen: BTreeSet<BlockId> = BTreeSet::new();
        let mut work = vec![*start];
        while let Some(bid) = work.pop() {
            if !seen.insert(bid) {
                continue;
            }
            let Some(block) = body.blocks.get(bid.0 as usize) else {
                continue;
            };
            for s in block_successors(block) {
                work.push(s);
            }
            for e in &block.exceptional {
                work.push(e.target);
            }
        }
        for bid in &seen {
            let Some(block) = body.blocks.get(bid.0 as usize) else {
                continue;
            };
            for stmt in &block.stmts {
                match stmt {
                    Stmt::Check(oid) => {
                        at_risk.insert((mk.clone(), *oid));
                    }
                    Stmt::Assign(_, Rvalue::Call { target, .. }) => {
                        tainted_methods.insert(target.clone());
                    }
                    _ => {}
                }
            }
        }
    }

    // Everything transitively callable from a cut-reachable call site.
    let mut work: Vec<MethodKey> = tainted_methods.iter().cloned().collect();
    let mut seen_m: BTreeSet<MethodKey> = BTreeSet::new();
    while let Some(mk) = work.pop() {
        if !seen_m.insert(mk.clone()) {
            continue;
        }
        let Some(body) = prog.body(&mk) else { continue };
        for block in &body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Stmt::Check(oid) => {
                        at_risk.insert((mk.clone(), *oid));
                    }
                    Stmt::Assign(_, Rvalue::Call { target, .. }) => {
                        work.push(target.clone());
                    }
                    _ => {}
                }
            }
        }
    }
    at_risk
}

/// Normal (non-exceptional) successors of a block.
fn block_successors(block: &Block) -> Vec<BlockId> {
    match &block.term {
        Terminator::Goto(t) => vec![*t],
        Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
        Terminator::Switch { cases, default, .. } => {
            let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
            v.push(*default);
            v
        }
        Terminator::Return(_)
        | Terminator::Halt
        | Terminator::Throw(_)
        | Terminator::Diverge(_) => vec![],
    }
}

/// Is this operator encoded in the FloatingPoint theory for float operands?
///
/// Java has no bitwise or shift operators on floats, so the arithmetic and
/// comparison operators below are the complete set that can appear.
fn fp_binop_modelled(op: BinOp) -> bool {
    // Which float operators the SMT encoding models precisely. An operator that
    // is *not* modelled taints its result, and a tainted branch condition is
    // never added to the path constraints — the guard simply is not imposed, so
    // every path looks reachable and the witness values are arbitrary.
    //
    // This must track `encode_binop`'s dispatch exactly. When arithmetic ran on
    // the bitvector path but this had been widened to include it, the engine
    // would trust a meaningless result; when arithmetic runs in FPA but this
    // still excludes it, the engine discards a guard it could have imposed and
    // emits a witness that cannot replay. The second is what happened: enabling
    // FPA arithmetic without updating this measured as "no better", because the
    // constraint was still being thrown away.
    let arith = matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem
    );
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    ) || (arith && encode::fp_arith())
}

pub struct SmtBmc {
    /// Encode float arithmetic in the FloatingPoint theory for this instance.
    ///
    /// FPA makes float arithmetic exact, which is what lets a float-guarded
    /// obligation be decided at all — but it also makes the formulas hard
    /// enough that the solver answers `unknown` where it previously answered
    /// `unsat`, so applying it everywhere loses far more proofs than it wins
    /// (measured: -62 across the corpus).
    ///
    /// The cost falls on obligations that never depended on float precision —
    /// a NullDeref does not care about rounding. So the portfolio runs the
    /// cheap encoding first and a second instance with this set afterwards,
    /// which can only affect obligations the first pass left open. Escalation
    /// is paid for only where it can help.
    pub fp_arith: bool,
    factory: Box<dyn SolverFactory>,
    max_depth: u32,
    /// Multiplier on this instance's work bounds — `MAX_FORKS`,
    /// `MAX_SOLVER_CALLS`, `MAX_BLOCK_VISITS`.
    ///
    /// This engine's resumable precision parameter, and per-instance rather
    /// than the process-global `budget_scale()` because resuming means raising
    /// it. Depth would be the textbook choice, and it is the wrong one here:
    /// sampling the tasks that truncate shows `handle_branch_fork` hitting
    /// `MAX_FORKS` long before `max_depth` binds, so deepening on depth would
    /// re-run an identical exploration and stop in an identical place.
    scale: u64,
    done: bool,
    /// Constrain nondet char to ASCII (0-127). Prevents witnesses with
    /// non-ASCII chars that our Character method encodings can't model,
    /// but limits falsification to the ASCII subset.
    pub ascii_only: bool,
    /// Queries this engine posted and has not yet consumed answers for.
    asked: Vec<u32>,
}

impl SmtBmc {
    pub fn new(factory: Box<dyn SolverFactory>, max_depth: u32) -> Self {
        SmtBmc {
            fp_arith: encode::fp_arith_default(),
            factory,
            max_depth,
            scale: budget_scale(),
            done: false,
            ascii_only: false,
            asked: Vec::new(),
        }
    }
}

impl SmtBmc {
    /// Collect interval hints from the blackboard for the entry method.
    fn collect_ai_hints(
        bb: &Blackboard,
        entry: &MethodKey,
    ) -> HashMap<(BlockId, VarId), (i64, i64)> {
        bb.interval_hints_for_method(entry)
    }
}

impl Engine for SmtBmc {
    fn id(&self) -> EngineId {
        // Distinct ids so engine attribution shows which pass decided what.
        if self.fp_arith {
            EngineId("smt-bmc-fpa")
        } else {
            EngineId("smt-bmc")
        }
    }

    fn direction(&self) -> Direction {
        Direction::Under
    }

    /// Two things, both published by other engines and both acted on inside
    /// `step`: answers to the questions this engine posts about unmodelled
    /// calls, and the interval hints `interval-ai` publishes, which prune
    /// infeasible regions before a single solver call is made.
    ///
    /// Deliberately not `STATUS`. A closed obligation is one fewer thing to
    /// check, but it does not make any path this engine could not explore
    /// explorable, so waking on it would buy a re-exploration and nothing else.
    fn interest(&self) -> Interest {
        Interest::LEMMA.union(Interest::PRECISION)
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, budget: Budget) -> Progress {
        // What this pass costs, which is the best available estimate of what a
        // deeper one would cost. Read by `should_resume_deeper` at the end.
        let step_started = std::time::Instant::now();
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        // The FPA pass exists to decide what the cheap pass could not, so if
        // nothing is open there is nothing for it to decide. Without this it
        // re-explores every method with the expensive encoding and merely
        // re-publishes discharges the first pass already made — which cost the
        // whole float category on no-runtime-exception (166 -> 114) while
        // changing no verdict.
        // The FPA pass exists to decide what the bitvector pass could not —
        // and, crucially, to revisit what the bitvector pass decided *wrongly*.
        // Asking `open()` misses the second case entirely: a violation derived
        // from `bvmul` on two IEEE-754 bit patterns closes the obligation, so
        // the pass that models the multiply properly skips the one task that
        // needed it. `open_for` returns those obligations too, because this
        // pass models exactly what the other one approximated.
        if self.fp_arith && bb.open_for(Approximations::FLOAT_ARITH).is_empty() {
            debug!("smt-bmc-fpa: nothing open or float-approximated, skipping the escalation pass");
            return Progress::Exhausted;
        }

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };

        // This instance's float encoding, for the duration of its step. The
        // portfolio runs a cheap bitvector pass first and an FPA pass after, so
        // the setting has to be per-instance rather than process-global.
        encode::set_fp_arith(self.fp_arith);
        // Restored on the way out of every path below.
        struct RestoreFpArith;
        impl Drop for RestoreFpArith {
            fn drop(&mut self) {
                encode::set_fp_arith(encode::fp_arith_default());
            }
        }
        let _restore = RestoreFpArith;

        let mut solver = match self.factory.create() {
            Ok(s) => s,
            Err(e) => {
                warn!("smt-bmc: failed to create solver: {e}");
                return Progress::Exhausted;
            }
        };

        info!(
            "smt-bmc: starting symbolic exploration (max_depth={}) on {entry:?}",
            self.max_depth
        );

        // Answers to questions an earlier pass asked. This is the point of
        // the whole mechanism: a bound on `Math.sin(x)` cannot be *derived*
        // here — SMT-LIB has no `fp.sin` — but it can be *assumed*, and
        // assuming it prunes every path that only exists because the solver
        // was free to claim `sin(x) == 5000`.
        //
        // Only bounds from an over-approximating answerer are usable; the
        // blackboard has already refused anything else at publish, so reaching
        // here means the claim is about every execution.
        let mut known_bounds: HashMap<(MethodKey, VarId), (u64, u64)> = HashMap::new();
        for qid in std::mem::take(&mut self.asked) {
            let Some(q) = bb.query(qid) else { continue };
            let (method, about) = (q.at.method.clone(), q.about.clone());
            for (lemma, approx) in bb.answers(qid) {
                // A lemma derived under an approximation this engine does not
                // make is a fact about a different program — the same rule
                // `open_for` applies to statuses.
                if !approx.is_exact() {
                    continue;
                }
                if let Answer::Bounds { lo, hi } = &lemma.answer {
                    if let (
                        ajave_core::term::Expr::Var(v),
                        ajave_core::term::Expr::Double(l),
                        ajave_core::term::Expr::Double(h),
                    ) = (&about, lo, hi)
                    {
                        debug!("smt-bmc: assuming bound on v{} from {}", v.0, lemma.by);
                        known_bounds.insert((method.clone(), *v), (*l, *h));
                    }
                }
            }
        }
        let learned = known_bounds.len();

        let type_array = solver.fresh_array("type", 32);
        let mut ctx = ExploreCtx {
            solver: solver.as_mut(),
            prog,
            body,
            vars: HashMap::new(),
            str_vars: HashMap::new(),
            fp_vars: HashMap::new(),
            pending_fp: None,
            str_consts: HashMap::new(),
            nondet_terms: Vec::new(),
            var_widths: HashMap::new(),
            violations: Vec::new(),
            depth: 0,
            max_depth: self.max_depth,
            solver_calls: 0,
            exhausted: false,
            deadline: budget.deadline,
            scale: self.scale,
            completeness: Completeness::new(),
            skipped_obligations: HashSet::new(),
            incomplete_methods: HashSet::new(),
            cut_points: BTreeSet::new(),
            frames: Vec::new(),
            approximated: Approximations::EXACT,
            pending_queries: Vec::new(),
            known_bounds,
            statics: HashMap::new(),
            static_str: HashMap::new(),
            static_tainted: HashSet::new(),
            field_arrays: HashMap::new(),
            field_str_arrays: HashMap::new(),
            field_tainted: HashSet::new(),
            array_map: Vec::new(),
            str_array_map: Vec::new(),
            type_array,
            type_ids: HashMap::new(),
            next_type_id: 1,
            tainted: HashSet::new(),
            float_tainted: HashSet::new(),
            path_tainted: false,
            call_depth: 0,
            loop_visits: HashMap::new(),
            block_visits: 0,
            fork_count: 0,
            clinit_done: HashSet::new(),
            concrete_classes: HashMap::new(),
            next_alloc_id: 1,
            inline_return: None,
            inline_return_str: None,
            inline_return_tainted: false,
            inline_throw: None,
            current_block: None,
            path_constraints: Vec::new(),
            parse_cases: Vec::new(),
            inlined_methods: HashSet::new(),
            ascii_only: self.ascii_only,
            ai_hints: Self::collect_ai_hints(bb, entry),
            ai_hints_applied: HashSet::new(),
        };

        if !ctx.ai_hints.is_empty() {
            info!("smt-bmc: loaded {} AI interval hints", ctx.ai_hints.len());
        }

        // Constrain entry method's Ref-typed parameters to be non-null.
        // JVM guarantees main()'s args is non-null; for other entry methods
        // we conservatively assume Ref parameters are non-null since they were
        // provided by a concrete caller.
        ctx.constrain_ref_params_nonnull();

        ctx.explore_block(body.entry, 0);

        let violations = std::mem::take(&mut ctx.violations);
        let violations_empty = violations.is_empty();
        // Collect violated obligation IDs before consuming violations.
        // Keyed by (method, id). `ObligationId` is an index into one `Body`'s
        // obligation list, so id 3 exists in every method that has four
        // obligations — dropping the method here made a violation in one
        // method block discharge of an unrelated obligation in another.
        let violated_oids: HashSet<(MethodKey, ObligationId)> = violations
            .iter()
            .map(|(m, oid, _)| (m.clone(), *oid))
            .collect();
        // Check if a runtime-exception violation could dispatch to an exception
        // handler containing an Assertion. When the BMC finds e.g. ArrayBounds
        // violated, it records the violation but does NOT follow the JVM's
        // exceptional control flow to the catch block. If that handler contains
        // `assert false`, we must not discharge the Assertion obligation.
        let has_exc_handler_with_assertion = {
            let mut found = false;
            if let Some(body) = prog.body(entry) {
                // Collect blocks that are exception handler targets.
                let mut handler_blocks: HashSet<BlockId> = HashSet::new();
                for (_, oid, _) in &violations {
                    // Find which block contains this violated obligation.
                    for block in &body.blocks {
                        let is_violation_block = block
                            .stmts
                            .iter()
                            .any(|s| matches!(s, Stmt::Check(o) if *o == *oid));
                        if is_violation_block && !block.exceptional.is_empty() {
                            // This block has exception edges — the violation
                            // could dispatch to a handler.
                            for edge in &block.exceptional {
                                handler_blocks.insert(edge.target);
                            }
                        }
                    }
                }
                // Check if any handler block (or block reachable from it)
                // contains an Assertion check.
                if !handler_blocks.is_empty() {
                    // BFS from handler blocks to find Assertion checks.
                    let mut visited = handler_blocks.clone();
                    let mut queue: Vec<BlockId> = handler_blocks.into_iter().collect();
                    while let Some(bid) = queue.pop() {
                        let blk = body.block(bid);
                        for stmt in &blk.stmts {
                            if let Stmt::Check(oid) = stmt {
                                if body.obligation(*oid).kind.is_assertion() {
                                    found = true;
                                    break;
                                }
                            }
                        }
                        if found {
                            break;
                        }
                        // Follow successors.
                        match &blk.term {
                            Terminator::Goto(t) => {
                                if visited.insert(*t) {
                                    queue.push(*t);
                                }
                            }
                            Terminator::Branch { then_, else_, .. } => {
                                if visited.insert(*then_) {
                                    queue.push(*then_);
                                }
                                if visited.insert(*else_) {
                                    queue.push(*else_);
                                }
                            }
                            Terminator::Switch { default, cases, .. } => {
                                if visited.insert(*default) {
                                    queue.push(*default);
                                }
                                for (_, t) in cases {
                                    if visited.insert(*t) {
                                        queue.push(*t);
                                    }
                                }
                            }
                            _ => {}
                        }
                        for edge in &blk.exceptional {
                            if visited.insert(edge.target) {
                                queue.push(edge.target);
                            }
                        }
                    }
                }
            }
            found
        };
        debug!(
            "smt-bmc: exploration complete, found {} violation(s), {} solver calls, {} block visits, {} forks, exhausted={}, completeness={:?}, skipped={}",
            violations.len(),
            ctx.solver_calls,
            ctx.block_visits,
            ctx.fork_count,
            ctx.exhausted,
            ctx.completeness,
            ctx.skipped_obligations.len(),
        );

        // What this exploration failed to model. Rides out on every artifact
        // below, so a more faithful engine can ask for these obligations back.
        let approximated = ctx.approximated;

        // Why this pass stopped, captured while `ctx` is still alive. The
        // resumption decision at the end of `step` needs all three, and needs
        // to tell a counter cut from a clock cut — only the first is something
        // a larger bound can answer.
        let all_paths_complete = ctx.completeness.all_paths_complete;
        let was_exhausted = ctx.exhausted;

        // Post the questions raised on the way. A query costs nothing and
        // commits to nothing, so there is no reason to be sparing — but an
        // engine that asks and never returns has wasted the answer, which is
        // what the `Blocked` return below is for.
        let pending = std::mem::take(&mut ctx.pending_queries);
        let asked_now = !pending.is_empty() && asking_enabled();
        if asked_now {
            for (at, about, given) in pending {
                let id = bb.ask(self.id(), at, about, Want::Bounds, given);
                self.asked.push(id);
            }
        }
        if learned > 0 {
            info!("smt-bmc: assumed {learned} bound(s) supplied by another engine");
        }

        let mut advanced = false;
        for (method, oid, witness) in violations {
            let oref = ObligationRef { method, id: oid };
            debug!(
                "smt-bmc: publishing violation at {oref:?}, witness={:?}",
                witness.nondet_sequence
            );
            let published = bb.publish_with(
                self.id(),
                self.direction(),
                approximated,
                Artifact::Status(
                    oref,
                    Status::Violated {
                        by: self.id(),
                        witness,
                    },
                ),
            );
            if published.is_ok() {
                advanced = true;
            }
        }

        // Per-obligation discharge: an obligation can be discharged if the
        // exploration was complete enough AND this specific obligation has no
        // violation and was not skipped. This is strictly more powerful than
        // the old "violations_empty" global gate — a violation on obligation A
        // no longer prevents discharging obligation B.
        if log::log_enabled!(log::Level::Debug) {
            // `open_or_unconfirmed` allocates, so it must not run when the
            // level is off.
            debug!(
                "smt-bmc: discharge gate exhausted={} budget_left={} all_paths_complete={} open_or_unconfirmed={}",
                ctx.exhausted,
                ctx.budget_left(),
                ctx.completeness.all_paths_complete,
                bb.open_or_unconfirmed().len(),
            );
        }
        // Which obligations a truncation could actually have hidden. Empty when
        // nothing was cut, in which case this is exactly the old global gate.
        let at_risk = if ctx.completeness.all_paths_complete {
            HashSet::new()
        } else {
            obligations_at_risk(prog, &ctx.cut_points)
        };
        if log::log_enabled!(log::Level::Debug) && !ctx.completeness.all_paths_complete {
            debug!(
                "smt-bmc: cut_points={:?} at_risk={} open={}",
                ctx.cut_points
                    .iter()
                    .map(|(m, b)| format!("{}#bb{}", m.name, b.0))
                    .collect::<Vec<_>>(),
                at_risk.len(),
                bb.open_or_unconfirmed().len(),
            );
        }
        if !ctx.exhausted && ctx.budget_left() {
            // Was: `if all_paths_complete`, a whole-run boolean that stopped
            // every obligation in the program from being considered as soon as
            // anything anywhere was cut short. The per-obligation test below
            // is the same claim made about the obligation actually at hand.
            //
            // Safety net: if a cut was recorded but produced no at-risk set,
            // something is unaccounted for and the old global behaviour stands.
            let cuts_accounted = ctx.completeness.all_paths_complete || !at_risk.is_empty();
            if cuts_accounted {
                // Include obligations whose only status is an unconfirmed
                // violation: an exhaustive exploration that found nothing is
                // real evidence, and it should not be discarded merely because
                // an under-approximating engine published a candidate first.
                let open_list = bb.open_or_unconfirmed();
                log::trace!("smt-bmc: per-obligation discharge check: entry={entry:?}, inlined={:?}, open={:?}, skipped={:?}, violated={:?}",
                    ctx.inlined_methods, open_list, ctx.skipped_obligations, violated_oids);
                let assertion_only = bb.is_assertion_only();
                for oref in open_list {
                    let method_explored =
                        &oref.method == entry || ctx.inlined_methods.contains(&oref.method);
                    // If a runtime-exception violation could dispatch to an
                    // exception handler containing an Assertion, don't discharge
                    // that Assertion (BMC doesn't explore exception dispatch paths).
                    if has_exc_handler_with_assertion && &oref.method == entry {
                        if let Some(b) = prog.body(&oref.method) {
                            if b.obligation(oref.id).kind.is_assertion() {
                                continue;
                            }
                        }
                    }
                    let blocker = if at_risk.contains(&(oref.method.clone(), oref.id)) {
                        "all_paths_complete"
                    } else if !ctx.completeness.can_discharge(
                        &oref.method,
                        entry,
                        method_explored,
                        assertion_only,
                    ) {
                        ctx.completeness
                            .discharge_blocker(&oref.method, entry, method_explored, assertion_only)
                            .unwrap_or("completeness")
                    } else if ctx
                        .skipped_obligations
                        .contains(&(oref.method.clone(), oref.id))
                    {
                        "skipped_obligation"
                    } else if violated_oids.contains(&(oref.method.clone(), oref.id)) {
                        "violated"
                    } else {
                        ""
                    };
                    if !blocker.is_empty() {
                        debug!("smt-bmc: BLOCKER {blocker} for {oref:?}");
                    }
                    if blocker.is_empty() {
                        debug!("smt-bmc: discharging {oref:?} (exhaustive exploration)");
                        let _ = bb.publish_with(
                            self.id(),
                            Direction::Over,
                            approximated,
                            Artifact::Status(
                                oref,
                                Status::Discharged {
                                    by: self.id(),
                                    proof: ProofKind::Exhaustive,
                                },
                            ),
                        );
                        advanced = true;
                    }
                }
            } else if log::log_enabled!(log::Level::Debug) {
                let open_methods: std::collections::BTreeSet<String> = bb
                    .open_or_unconfirmed()
                    .iter()
                    .map(|o| o.method.to_string())
                    .collect();
                let trunc: std::collections::BTreeSet<String> = ctx
                    .incomplete_methods
                    .iter()
                    .map(|m| m.to_string())
                    .collect();
                let elsewhere = open_methods.difference(&trunc).count();
                debug!(
                    "smt-bmc: BLOCKER all_paths_complete for every obligation (outer gate); \
                     open in {} method(s), truncated in {} method(s), {} open method(s) \
                     were never truncated",
                    open_methods.len(),
                    trunc.len(),
                    elsewhere
                );
            }
            if may_publish_bounded(
                ctx.exhausted,
                ctx.budget_left(),
                ctx.completeness.all_paths_complete,
                violations_empty,
            ) {
                // Bounded publishing only when no violations at all
                // (conservative: bounded status is only useful when clean).
                // Also skip obligations that had a tainted-path violation
                // suppressed — their bounded status is unsound because the
                // solver DID find a satisfying assignment for the error path.
                // Was `&oref.method == entry`, which is both too narrow and
                // too loose.
                //
                // Too narrow: the BMC inlines callees and checks their
                // obligations, so a bounded result exists for them too — and
                // withholding it is why `k-induction` and `imc` report "nothing
                // to work on" on tasks where the BMC plainly did bounded work.
                // A 125-task sample found 13 such tasks, 8 of them expected
                // TRUE.
                //
                // Too loose: it published for *every* open entry obligation
                // whenever the run truncated anywhere, including obligations
                // the truncation could have hidden. `Bounded { k }` says the
                // search covered this obligation to depth k, and a consumer
                // acts on that — `k-induction` discharges outright when the
                // reachable code is loop-free. An obligation on a path we never
                // explored has no bounded result to report, and saying it does
                // is the producer/consumer disagreement `CLAUDE.md` records for
                // this exact artifact.
                //
                // `at_risk` is already computed above and answers precisely
                // that question, per obligation rather than per run.
                for oref in bb.open() {
                    let key = (oref.method.clone(), oref.id);
                    if !ctx.skipped_obligations.contains(&key) && !at_risk.contains(&key) {
                        let _ = bb.publish_with(
                            self.id(),
                            self.direction(),
                            approximated,
                            Artifact::Status(oref, Status::Bounded { k: self.max_depth }),
                        );
                        advanced = true;
                    }
                }
            }
        }

        // Having asked something, come back to act on the answer.
        //
        // This used to be the one place the portfolio was re-entrant, and it
        // was hand-rolled: clear `done`, latch `may_reenter` so it could happen
        // at most once, and return `Stalled` — which the old scheduler read as
        // "run again next round" regardless of whether anybody had answered. So
        // the common case was a second full exploration against an unchanged
        // board.
        //
        // `Blocked` plus `Interest::LEMMA` says the same thing to a scheduler
        // that can act on it: re-enter when an answer lands, and not before.
        // The latch goes with it — what bounded the re-entry was never the
        // count, it was that a `Lemma` arrives at most once per `Query`.
        //
        // `open_for`, not `open`. An unconstrained `Math.sin` lets the solver
        // claim `sin(x) > 2`, so this pass may have *closed* the very
        // obligation the answers would settle — which is the same trap the FPA
        // pass fell into, and the reason `open_for` exists. Gating on `open()`
        // here meant the engine never returned in exactly the case that
        // motivated asking.
        if asked_now && !bb.open_for(Approximations::UNMODELLED_CALL).is_empty() {
            self.done = false;
            debug!(
                "smt-bmc: asked {} question(s); will return when they are answered",
                self.asked.len()
            );
            return Progress::Blocked;
        }

        // Resume at a higher work bound if the counters, and not the clock,
        // are what stopped this pass.
        //
        // The restart re-explores the prefix it already covered, which is the
        // ordinary cost of iterative deepening and is why the bound doubles
        // rather than creeping: the shallow work is repeated a bounded number
        // of times. Carrying the frontier across the yield instead would avoid
        // it, and would mean rewriting a nineteen-site recursion whose solver
        // `push`/`pop` pairs span the recursion — the dangling-push bug class
        // `CLAUDE.md` names. An integer is the cheaper honest mechanism.
        if should_resume_deeper(
            all_paths_complete,
            was_exhausted,
            self.scale,
            !bb.open_for(approximated).is_empty(),
            step_started.elapsed(),
            budget
                .deadline
                .map(|d| d.saturating_duration_since(std::time::Instant::now())),
        ) {
            self.scale *= 2;
            self.done = false;
            debug!(
                "smt-bmc: counters bound this pass, not the clock; \
                 resuming at scale {}",
                self.scale
            );
            return Progress::Suspended;
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Blocked
        }
    }
}

struct ExploreCtx<'a> {
    solver: &'a mut dyn Solver,
    prog: &'a Program,
    body: &'a Body,
    vars: HashMap<VarId, Term>,
    str_vars: HashMap<VarId, Term>,
    /// FP term produced by the most recent float arithmetic, awaiting
    /// attachment to the destination variable by the assignment site.
    pending_fp: Option<Term>,
    /// FP-sorted terms for float/double variables, mirroring `str_vars`.
    ///
    /// `vars` holds every variable as a bitvector, which for a float is its
    /// raw IEEE-754 bit pattern — `bvadd` on that is not addition. Real
    /// floating-point reasoning needs terms in the FloatingPoint sort, so
    /// float variables carry a second term here and arithmetic uses it.
    fp_vars: HashMap<VarId, Term>,
    /// Tracks constant string values for variables (for precise compareTo).
    str_consts: HashMap<VarId, String>,
    nondet_terms: Vec<(usize, Term, u32, Ty, Option<Term>)>,
    violations: Vec<(MethodKey, ObligationId, Witness)>,
    depth: u32,
    max_depth: u32,
    solver_calls: u32,
    exhausted: bool,
    /// Wall-clock slice for this exploration, from `Budget::deadline`.
    deadline: Option<std::time::Instant>,
    /// Multiplier on the work bounds for this pass. See `SmtBmc::scale`.
    scale: u64,
    completeness: Completeness,
    /// Obligations whose check could not be trusted, keyed by
    /// **(method, id)**. See `violated_oids` for why the method is part of
    /// the key.
    skipped_obligations: HashSet<(MethodKey, ObligationId)>,
    /// Methods in which exploration was truncated. See `mark_incomplete`.
    incomplete_methods: HashSet<MethodKey>,
    /// Program points where exploration was cut short, as (method, block).
    ///
    /// A truncation cannot affect an obligation it cannot reach, so recording
    /// *where* each cut happened is what lets `all_paths_complete` — a
    /// whole-run boolean, and the outer gate on all discharge — become a
    /// per-obligation fact. Every frame on the call stack at the time is
    /// recorded too: a cut deep inside a callee means the caller never
    /// returned, so its continuation is unexplored as well.
    cut_points: BTreeSet<(MethodKey, BlockId)>,
    /// Call sites of the frames currently being explored, innermost last.
    frames: Vec<(MethodKey, BlockId)>,
    /// Questions raised during exploration, posted to the blackboard once it
    /// finishes.
    ///
    /// Collected rather than published inline because `ExploreCtx` does not
    /// hold the blackboard — the same reason `violations` is a field. Each is
    /// `(program point, about, given)`.
    pending_queries: Vec<(
        ProgramPoint,
        ajave_core::term::Expr,
        Vec<ajave_core::term::Expr>,
    )>,
    /// Bounds another engine has already established for a variable, as
    /// `(method, var) -> (lo bits, hi bits)`.
    ///
    /// Read from lemmas at the start of a pass and asserted as the variable is
    /// created, which is what turns an answer into pruning.
    known_bounds: HashMap<(MethodKey, VarId), (u64, u64)>,
    /// What this exploration did not model faithfully.
    ///
    /// Set by `encode_binop` when it encodes a float arithmetic operator on
    /// the bitvector path — which is what the cheap pass does by default. Rides
    /// out on every artifact this exploration publishes, so the FPA pass can
    /// ask for exactly those obligations back. See `Approximations`.
    approximated: Approximations,

    // ── Heap model ──────────────────────────────────────────────────────
    statics: HashMap<FK, Term>,
    static_str: HashMap<FK, Term>,
    static_tainted: HashSet<FK>,
    field_arrays: HashMap<FK, Term>,
    field_str_arrays: HashMap<FK, Term>,
    field_tainted: HashSet<FK>,
    array_map: Vec<(Term, Term, Term)>,
    /// String contents of arrays, as `(reference, (Array BV32 String))`.
    ///
    /// The bitvector `array_map` above holds a 32-bit element per index, which
    /// models an `int[]` and the *reference* of a `String[]` element, and says
    /// nothing about the characters. Strings were tracked through fields
    /// (`field_str_arrays`) and not through arrays, so `a[0] = s; t = a[0];`
    /// lost `s`'s contents and every later `String` method on `t` became
    /// unmodelled -- which taints the path and blocks discharge. Measured as
    /// the reason 12 of 12 blocked securibench valid-assert tasks were stuck.
    str_array_map: Vec<(Term, Term)>,
    type_array: Term,
    type_ids: HashMap<String, i64>,
    next_type_id: i64,

    // ── Width tracking ──────────────────────────────────────────────────
    var_widths: HashMap<VarId, u32>,

    // ── Taint ───────────────────────────────────────────────────────────
    tainted: HashSet<VarId>,
    float_tainted: HashSet<VarId>,
    path_tainted: bool,

    // ── Concrete type tracking ─────────────────────────────────────────
    /// Maps VarId → class name for variables assigned via `Rvalue::New`.
    /// Used for exception dispatch (matching thrown type to handler).
    concrete_classes: HashMap<VarId, String>,

    // ── Exploration state ───────────────────────────────────────────────
    call_depth: u32,
    loop_visits: HashMap<(String, u32), u32>,
    block_visits: u64,
    fork_count: u32,
    clinit_done: HashSet<String>,
    next_alloc_id: i64,
    inline_return: Option<Term>,
    inline_return_str: Option<Term>,
    inline_return_tainted: bool,
    /// Set when an inlined callee throws an exception that has no local handler.
    /// (thrown_ref_term, concrete_class_name)
    inline_throw: Option<(Term, String)>,
    /// Current block being explored (for exception edge checks).
    current_block: Option<BlockId>,
    path_constraints: Vec<Term>,
    /// Alternative constraint sets, one entry per modelled `parse*` call.
    ///
    /// Each inner `Vec` holds the mutually exclusive cases for one call (a
    /// non-negative parse, and a negative one). They are *not* path
    /// constraints: asserting them would exclude strings Java accepts. They
    /// are tried, one combination at a time, only to obtain a witness that
    /// replays -- see `check_sat_with_path_and_witness`.
    parse_cases: Vec<Vec<Term>>,
    inlined_methods: HashSet<MethodKey>,
    ascii_only: bool,
    /// Interval bounds from AI, keyed by (block, var). Sound over-approximation:
    /// asserting these in the solver prunes infeasible regions of the search space.
    ai_hints: HashMap<(BlockId, VarId), (i64, i64)>,
    /// Variables whose AI hints have already been asserted (avoid re-asserting).
    ai_hints_applied: HashSet<(BlockId, VarId)>,
}

/// Snapshot of mutable state for save/restore across forks and diamond merges.
#[derive(Clone)]
struct SavedState {
    vars: HashMap<VarId, Term>,
    str_vars: HashMap<VarId, Term>,
    /// FP-sorted terms for float/double variables, mirroring `str_vars`.
    ///
    /// `vars` holds every variable as a bitvector, which for a float is its
    /// raw IEEE-754 bit pattern — `bvadd` on that is not addition. Real
    /// floating-point reasoning needs terms in the FloatingPoint sort, so
    /// float variables carry a second term here and arithmetic uses it.
    fp_vars: HashMap<VarId, Term>,
    str_consts: HashMap<VarId, String>,
    nondet_terms: Vec<(usize, Term, u32, Ty, Option<Term>)>,
    var_widths: HashMap<VarId, u32>,
    tainted: HashSet<VarId>,
    float_tainted: HashSet<VarId>,
    path_tainted: bool,
    statics: HashMap<FK, Term>,
    static_str: HashMap<FK, Term>,
    static_tainted: HashSet<FK>,
    field_arrays: HashMap<FK, Term>,
    field_str_arrays: HashMap<FK, Term>,
    field_tainted: HashSet<FK>,
    array_map: Vec<(Term, Term, Term)>,
    str_array_map: Vec<(Term, Term)>,
    type_array: Term,
    loop_visits: HashMap<(String, u32), u32>,
    pc_len: usize,
}

/// Small utility methods on ExploreCtx: budget, width, taint, field helpers.
impl<'a> ExploreCtx<'a> {
    /// Whether this step's wall-clock slice is spent, as distinct from its
    /// work counters. Resumption can answer the second and not the first.
    fn clock_expired(&self) -> bool {
        self.deadline
            .is_some_and(|d| std::time::Instant::now() >= d)
    }

    fn budget_left(&self) -> bool {
        let k = self.scale;
        // The wall-clock slice comes first: the counters below bound *work*,
        // and one solver call can take a minute regardless of how few calls
        // have been made. Measured over 20 tasks that hit the 60s budget, this
        // engine held the process on 18 of 18 -- every engine behind it never
        // ran.
        if self.clock_expired() {
            return false;
        }
        !self.exhausted
            && (self.solver_calls as u64) < MAX_SOLVER_CALLS as u64 * k
            && self.violations.len() < MAX_VIOLATIONS
            && self.block_visits < MAX_BLOCK_VISITS * k
            && (self.fork_count as u64) < MAX_FORKS as u64 * k
    }

    /// Budget check that **records** the resulting truncation.
    ///
    /// Returns true when the budget is spent, and marks the exploration
    /// incomplete when it does. Every site that abandons part of the path space
    /// must go through this rather than `budget_left()`.
    ///
    /// This exists because the invariant was maintained in one place and
    /// violated in nine. `Completeness::can_discharge()` trusts
    /// `all_paths_complete` to publish `proof: Exhaustive`, so a site that
    /// stopped exploring while leaving the flag set let BMC claim a proof over
    /// paths it never examined — an obligation on an unexplored branch is never
    /// shown violated, so it looks safe. That is a wrong TRUE at -16, and
    /// `Pan_exceptionprone` was one: a 61-obligation method that exhausts
    /// MAX_FORKS, truncates, and then discharges an unconditional
    /// ArrayIndexOutOfBounds it had not looked at.
    ///
    /// Prefer this over `!self.budget_left()` in new code. The two remaining
    /// direct readers are checks that do not truncate.
    fn budget_exhausted(&mut self) -> bool {
        if self.budget_left() {
            return false;
        }
        self.completeness.all_paths_complete = false;
        true
    }

    fn width_of_var(&self, vid: VarId) -> u32 {
        match self.body.var(vid).ty {
            Ty::Long | Ty::Double => 64,
            _ => 32,
        }
    }

    fn width_of_ty(&self, ty: &Ty) -> u32 {
        match ty {
            Ty::Long | Ty::Double => 64,
            _ => 32,
        }
    }

    fn rvalue_result_width(&self, rv: &Rvalue) -> u32 {
        match rv {
            Rvalue::Use(op) | Rvalue::Neg(op) => self.width_of_operand(op),
            Rvalue::Bin(_, a, _) => self.width_of_operand(a),
            Rvalue::Nondet(ty, _) | Rvalue::Havoc(ty, _) | Rvalue::Cast(ty, _, _) => {
                self.width_of_ty(ty)
            }
            Rvalue::Cmp(_, _, _) | Rvalue::InstanceOf { .. } | Rvalue::ArrayLength(_) => 32,
            Rvalue::GetStatic(fk) | Rvalue::GetField { field: fk, .. } => {
                Self::field_elem_width(&fk.desc)
            }
            Rvalue::ArrayLoad { .. } => 32, // element arrays are 32-bit
            Rvalue::New(_) | Rvalue::NewArray { .. } => 32,
            Rvalue::Call { target, .. } => Self::ret_width_from_desc(&target.desc),
        }
    }

    fn width_of_operand(&self, op: &Operand) -> u32 {
        match op {
            Operand::Var(v) => {
                // Prefer tracked width (actual assignment) over VarInfo.ty
                // (which can be stale due to JVM local slot reuse).
                if let Some(&w) = self.var_widths.get(v) {
                    w
                } else {
                    self.width_of_var(*v)
                }
            }
            Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => 64,
            _ => 32,
        }
    }

    fn get_var(&mut self, vid: VarId) -> Term {
        if let Some(&t) = self.vars.get(&vid) {
            return t;
        }
        let w = self.width_of_var(vid);
        let t = self.solver.fresh_bv(&format!("uninit_v{}", vid.0), w);
        self.vars.insert(vid, t);
        t
    }

    fn operand_tainted(&self, op: &Operand) -> bool {
        matches!(op, Operand::Var(v) if self.tainted.contains(v))
    }

    fn operand_is_float(&self, op: &Operand) -> bool {
        match op {
            Operand::Const(c) => matches!(c.ty(), Ty::Float | Ty::Double),
            Operand::Var(v) => self
                .body
                .vars
                .get(v.0 as usize)
                .map(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
                .unwrap_or(false),
        }
    }

    fn operand_float_tainted(&self, op: &Operand) -> bool {
        matches!(op, Operand::Var(v) if self.float_tainted.contains(v))
    }

    fn field_key_raw(fk: &FieldKey) -> FK {
        FK {
            class: fk.class.clone(),
            name: fk.name.clone(),
            desc: fk.desc.clone(),
        }
    }

    fn field_key_resolved(&self, fk: &FieldKey) -> FK {
        let resolved_class = self.prog.resolve_field_class(&fk.class, &fk.name, &fk.desc);
        FK {
            class: resolved_class,
            name: fk.name.clone(),
            desc: fk.desc.clone(),
        }
    }

    fn rvalue_tainted(&mut self, rv: &Rvalue) -> bool {
        match rv {
            Rvalue::GetStatic(fk) => {
                self.ensure_clinit(&fk.class);
                let k = Self::field_key_raw(fk);
                if self.statics.contains_key(&k) {
                    self.static_tainted.contains(&k)
                } else if self.is_program_class(&fk.class) {
                    false
                } else {
                    !(fk.desc.starts_with('L') || fk.desc.starts_with('['))
                }
            }
            Rvalue::GetField { field, .. } => {
                let k = self.field_key_resolved(field);
                self.field_tainted.contains(&k)
            }
            Rvalue::ArrayLoad { arr, idx } => {
                self.operand_tainted(arr) || self.operand_tainted(idx)
            }
            Rvalue::ArrayLength(arr) => self.operand_tainted(arr),
            Rvalue::NewArray { len, .. } => self.operand_tainted(len),
            Rvalue::InstanceOf { obj, .. } => self.operand_tainted(obj),
            Rvalue::New(_) => false,
            Rvalue::Call {
                target,
                args,
                is_virtual,
            } => {
                if ajave_models::STR_OWNERS.contains(&target.class.as_str()) {
                    let unmodelled = !self.str_call_modelled(target, args);
                    if unmodelled {
                        log::debug!(
                            "smt-bmc: TAINT-SOURCE str {}.{}{}",
                            target.class,
                            target.name,
                            target.desc
                        );
                    }
                    return unmodelled;
                }
                if self.math_call_modelled(target) {
                    return false;
                }
                if self.can_inline(target, *is_virtual) {
                    return false;
                }
                log::debug!(
                    "smt-bmc: TAINT-SOURCE call {}.{}{}",
                    target.class,
                    target.name,
                    target.desc
                );
                true
            }
            Rvalue::Use(o) => self.operand_tainted(o),
            Rvalue::Neg(o) => {
                self.operand_tainted(o) || self.operand_is_float(o) || self.operand_float_tainted(o)
            }
            Rvalue::Cast(_, _, o) => {
                self.operand_tainted(o) || self.operand_is_float(o) || self.operand_float_tainted(o)
            }
            // Float arithmetic and comparison are encoded in the SMT
            // FloatingPoint theory, so a float operand no longer implies an
            // imprecise result. Only operators outside that encoding — and
            // pre-existing taint — still contaminate.
            Rvalue::Bin(op, a, b) => {
                let float_operand = self.operand_is_float(a) || self.operand_is_float(b);
                let modelled = float_operand && fp_binop_modelled(*op);
                self.operand_tainted(a)
                    || self.operand_tainted(b)
                    || (float_operand && !modelled)
                    || (!modelled
                        && (self.operand_float_tainted(a) || self.operand_float_tainted(b)))
            }
            // Float cmp (FloatL/FloatG) is precisely modeled via BV totalOrder,
            // so the result is NOT tainted by float operands. Only propagate
            // actual taint from havoc/unmodeled sources.
            Rvalue::Cmp(kind, a, b) => {
                let base_tainted = self.operand_tainted(a) || self.operand_tainted(b);
                match kind {
                    CmpKind::FloatL | CmpKind::FloatG => base_tainted,
                    CmpKind::Long => base_tainted,
                }
            }
            Rvalue::Nondet(..) => false,
            Rvalue::Havoc(_, _) => true,
        }
    }

    fn rvalue_float_tainted(&self, rv: &Rvalue) -> bool {
        // Modelled float arithmetic produces an exactly-represented result,
        // so it does not spread float taint.
        if let Rvalue::Bin(op, a, b) = rv {
            if (self.operand_is_float(a) || self.operand_is_float(b)) && fp_binop_modelled(*op) {
                return self.operand_float_tainted(a) && self.operand_float_tainted(b) && false;
            }
        }
        match rv {
            Rvalue::Use(o) | Rvalue::Neg(o) => {
                self.operand_float_tainted(o) || self.operand_is_float(o)
            }
            Rvalue::Cast(_, _, o) => self.operand_float_tainted(o) || self.operand_is_float(o),
            Rvalue::Bin(_, a, b) => {
                self.operand_float_tainted(a)
                    || self.operand_float_tainted(b)
                    || self.operand_is_float(a)
                    || self.operand_is_float(b)
            }
            // Cmp result is int, not float — float taint stops here.
            // If operands came from imprecise float arithmetic, they are already
            // in the `tainted` set, so rvalue_tainted's Cmp case catches them.
            Rvalue::Cmp(..) => false,
            Rvalue::GetStatic(fk) => {
                matches!(fk.desc.as_bytes().first(), Some(b'F') | Some(b'D'))
            }
            Rvalue::GetField { field, .. } => {
                matches!(field.desc.as_bytes().first(), Some(b'F') | Some(b'D'))
            }
            _ => false,
        }
    }

    fn is_program_class(&self, class: &str) -> bool {
        self.prog.bodies.keys().any(|k| k.class == class)
    }

    fn field_elem_width(desc: &str) -> u32 {
        match desc.as_bytes().first() {
            Some(b'J') | Some(b'D') => 64,
            _ => 32,
        }
    }

    /// Width of the return type parsed from a JVM method descriptor like "(II)J".
    fn ret_width_from_desc(desc: &str) -> u32 {
        let after_paren = desc.split(')').nth(1).unwrap_or("V");
        match after_paren.as_bytes().first() {
            Some(b'J') | Some(b'D') => 64,
            _ => 32,
        }
    }

    /// Whether the method descriptor returns `Ljava/lang/String;`.
    fn returns_string(desc: &str) -> bool {
        desc.ends_with(")Ljava/lang/String;")
    }

    fn get_field_array(&mut self, k: &FK, elem_width: u32) -> Term {
        if let Some(&arr) = self.field_arrays.get(k) {
            return arr;
        }
        let arr = if self.is_program_class(&k.class) {
            let zero = self.solver.bv_const(0, elem_width);
            self.solver.const_array(zero, elem_width)
        } else {
            self.solver.fresh_array(
                &format!("f_{}_{}", k.class.replace('/', "_"), k.name),
                elem_width,
            )
        };
        self.field_arrays.insert(k.clone(), arr);
        arr
    }

    fn get_field_str_array(&mut self, k: &FK) -> Term {
        if let Some(&arr) = self.field_str_arrays.get(k) {
            return arr;
        }
        let arr = if self.is_program_class(&k.class) {
            let empty = self.solver.str_const("");
            self.solver.const_str_array(empty)
        } else {
            self.solver
                .fresh_str_array(&format!("fs_{}_{}", k.class.replace('/', "_"), k.name))
        };
        self.field_str_arrays.insert(k.clone(), arr);
        arr
    }

    fn get_type_id(&mut self, class: &str) -> i64 {
        if let Some(&id) = self.type_ids.get(class) {
            return id;
        }
        let id = self.next_type_id;
        self.next_type_id += 1;
        self.type_ids.insert(class.to_string(), id);
        id
    }

    fn subtype_ids(&mut self, class: &str) -> Vec<i64> {
        let all_classes: Vec<String> = self.type_ids.keys().cloned().collect();
        let mut result = Vec::new();
        let target_id = self.get_type_id(class);
        result.push(target_id);
        for c in &all_classes {
            if c != class {
                // Only include c as a subtype if its hierarchy is known.
                // Unknown classes get is_subtype() == true (conservative for
                // over-approx) but that's wrong for instanceof where we need
                // the actual answer. Skip unknown hierarchies.
                // Exception: array types ([Lfoo;) have their own covariance
                // rules handled by is_subtype() even without supers entries.
                if !c.starts_with('[') && !self.prog.supers.contains_key(c.as_str()) {
                    continue;
                }
                if self.prog.is_subtype(c, class) {
                    let id = self.get_type_id(c);
                    if !result.contains(&id) {
                        result.push(id);
                    }
                }
            }
        }
        result
    }

    fn constrain_ref_params_nonnull(&mut self) {
        let desc = self.body.key.desc.clone();
        let params = Self::parse_param_slots(&desc);
        for (vid_idx, info) in self.body.vars.iter().enumerate() {
            if let ajave_ir::VarKind::Local(slot) = info.kind {
                if info.ty == ajave_ir::Ty::Ref {
                    if let Some(class) = params
                        .iter()
                        .find(|(s, _)| *s == slot as usize)
                        .map(|(_, c)| c.clone())
                    {
                        let vid = ajave_ir::VarId(vid_idx as u32);
                        let t = self.get_var(vid);
                        self.assert_nonzero(t);
                        // Store the declared type so instanceof checks work
                        let type_id = self.get_type_id(&class);
                        let tid_term = self.solver.bv_const(type_id, 32);
                        let ta = self.solver.array_store(self.type_array, t, tid_term);
                        self.type_array = ta;
                    }
                }
            }
        }
    }

    /// Parse method descriptor, returning (slot_index, class_name) for Ref params.
    fn parse_param_slots(desc: &str) -> Vec<(usize, String)> {
        let inner = desc.trim_start_matches('(');
        let bytes = inner.as_bytes();
        let mut pos = 0;
        let mut slot = 0;
        let mut result = Vec::new();
        while pos < bytes.len() && bytes[pos] != b')' {
            let start = pos;
            match bytes[pos] {
                b'J' | b'D' => {
                    pos += 1;
                    slot += 2;
                }
                b'L' => {
                    pos += 1;
                    let class_start = pos;
                    while pos < bytes.len() && bytes[pos] != b';' {
                        pos += 1;
                    }
                    let class = std::str::from_utf8(&bytes[class_start..pos])
                        .unwrap_or("")
                        .to_string();
                    pos += 1;
                    result.push((slot, class));
                    slot += 1;
                }
                b'[' => {
                    // Array type: [L...; or [I etc — the full descriptor is the class
                    let arr_start = start;
                    while pos < bytes.len() && bytes[pos] == b'[' {
                        pos += 1;
                    }
                    if pos < bytes.len() && bytes[pos] == b'L' {
                        while pos < bytes.len() && bytes[pos] != b';' {
                            pos += 1;
                        }
                        pos += 1;
                    } else if pos < bytes.len() {
                        pos += 1;
                    }
                    let class = std::str::from_utf8(&bytes[arr_start..pos])
                        .unwrap_or("")
                        .to_string();
                    result.push((slot, class));
                    slot += 1;
                }
                _ => {
                    pos += 1;
                    slot += 1;
                }
            }
        }
        result
    }

    /// Assert AI interval hints for variables at the given block.
    /// Only applies in the entry method body (call_depth == 0), since hints
    /// are keyed by block ID within the entry method only.
    fn apply_ai_hints(&mut self, block_id: BlockId) {
        if self.ai_hints.is_empty() || self.call_depth > 0 {
            return;
        }
        // Collect applicable hints for this block.
        let mut hints: Vec<(VarId, i64, i64)> = self
            .ai_hints
            .iter()
            .filter(|((bid, _), _)| *bid == block_id)
            .filter(|(key, _)| !self.ai_hints_applied.contains(key))
            .map(|((_, vid), (lo, hi))| (*vid, *lo, *hi))
            .collect();
        // `ai_hints` is a HashMap, and Rust seeds its hasher randomly per
        // process — so without this the bound constraints are asserted in a
        // different order on every run. The formula stays logically the same,
        // but its shape changes, the solver returns a different (still valid)
        // model, and the resulting witness may or may not reproduce on a real
        // JVM. That is a verdict flipping between FALSE and UNKNOWN across
        // identical runs (#66).
        hints.sort();

        for (vid, lo, hi) in hints {
            // Only constrain variables we already have a term for
            if let Some(&t) = self.vars.get(&vid) {
                let w = self.width_of_var(vid);
                // Only apply to 32-bit integer variables (AI domain is i32)
                if w == 32 {
                    let lo_t = self.solver.bv_const(lo, w);
                    let hi_t = self.solver.bv_const(hi, w);
                    let ge = self.solver.bvsge(t, lo_t);
                    let le = self.solver.bvsle(t, hi_t);
                    let bound = self.solver.and(ge, le);
                    self.path_constraints.push(bound);
                    self.ai_hints_applied.insert((block_id, vid));
                    log::trace!(
                        "smt-bmc: applied AI hint v{} ∈ [{}, {}] at bb{}",
                        vid.0,
                        lo,
                        hi,
                        block_id.0
                    );
                }
            }
        }
    }

    fn assert_nonzero(&mut self, t: Term) {
        let zero = self.solver.bv_const(0, 32);
        let eq = self.solver.bveq(t, zero);
        let neq = self.solver.not(eq);
        self.solver.assert(neq);
    }

    fn nonzero_constraint(&mut self, t: Term) -> Term {
        let zero = self.solver.bv_const(0, 32);
        let eq = self.solver.bveq(t, zero);
        self.solver.not(eq)
    }

    fn zero_constraint(&mut self, t: Term) -> Term {
        let zero = self.solver.bv_const(0, 32);
        self.solver.bveq(t, zero)
    }

    fn check_sat_with_path(&mut self) -> SatResult {
        self.solver_calls += 1;
        if (self.solver_calls as u64) > MAX_SOLVER_CALLS as u64 * self.scale {
            self.exhausted = true;
            return SatResult::Unknown;
        }
        self.solver.push();
        for &pc in &self.path_constraints {
            self.solver.assert(pc);
        }
        let res = self.solver.check_sat();
        self.solver.pop();
        res
    }

    /// Check satisfiability with path constraints and an extra condition.
    /// If SAT, extracts a witness before popping the solver scope.
    /// Returns (result, optional witness).
    fn check_sat_with_path_and_witness(&mut self, extra: Term) -> (SatResult, Option<Witness>) {
        self.solver_calls += 1;
        if (self.solver_calls as u64) > MAX_SOLVER_CALLS as u64 * self.scale {
            self.exhausted = true;
            return (SatResult::Unknown, None);
        }
        // Try the parse cases first, then fall back to the unconstrained
        // query.
        //
        // A `parse*` result is otherwise a fresh bitvector unrelated to its
        // string, so the solver may claim `parseInt(s) == 7` while leaving `s`
        // free -- and the witness it prints ("A") throws
        // `NumberFormatException` on replay. Asserting one case binds the two
        // together and yields a string that really parses to the value.
        //
        // Two properties make this safe:
        //
        // * The cases are **tried, never required**. If none is satisfiable we
        //   fall back to the plain query below, so no path Java can reach is
        //   ever excluded. `Unsat` is therefore only ever concluded from the
        //   unconstrained query, which is what keeps discharge sound and is
        //   why this needs no completeness flag.
        // * The result is monotone: a case that works replaces an
        //   unreplayable witness with a replayable one, and a case that does
        //   not leaves behaviour exactly as it was.
        //
        // Cases are asserted one combination at a time rather than disjoined.
        // Measured 2026-09-06: identical terms are 0.01s when asserted and
        // time out at 45s inside an `(or ...)`, because Z3's string solver
        // does not case-split over string constraints (#90).
        for combo in self.parse_case_combinations() {
            self.solver.push();
            for &pc in &self.path_constraints {
                self.solver.assert(pc);
            }
            self.solver.assert(extra);
            for &c in &combo {
                self.solver.assert(c);
            }
            let res = self.solver.check_sat();
            if res == SatResult::Sat {
                let w = self.extract_witness();
                self.solver.pop();
                return (SatResult::Sat, Some(w));
            }
            self.solver.pop();
        }

        self.solver.push();
        for &pc in &self.path_constraints {
            self.solver.assert(pc);
        }
        self.solver.assert(extra);
        let res = self.solver.check_sat();
        let witness = if res == SatResult::Sat {
            Some(self.extract_witness())
        } else {
            None
        };
        self.solver.pop();
        (res, witness)
    }

    /// One combination per parse call, capped.
    ///
    /// The cross product is exponential in the number of parse calls, so it is
    /// abandoned past `MAX_PARSE_COMBINATIONS`; the fallback query still runs,
    /// which is exactly today's behaviour.
    fn parse_case_combinations(&self) -> Vec<Vec<Term>> {
        if self.parse_cases.is_empty() {
            return Vec::new();
        }
        let total: usize = self
            .parse_cases
            .iter()
            .try_fold(1usize, |acc, c| acc.checked_mul(c.len().max(1)))
            .unwrap_or(usize::MAX);
        if total > MAX_PARSE_COMBINATIONS {
            return Vec::new();
        }
        let mut out: Vec<Vec<Term>> = vec![Vec::new()];
        for alts in &self.parse_cases {
            let mut next = Vec::with_capacity(out.len() * alts.len());
            for base in &out {
                for &a in alts {
                    let mut v = base.clone();
                    v.push(a);
                    next.push(v);
                }
            }
            out = next;
        }
        out
    }

    fn extract_witness(&mut self) -> Witness {
        let info: Vec<(Term, u32, Ty, Option<Term>)> = self
            .nondet_terms
            .iter()
            .map(|(_, t, w, ty, st)| (*t, *w, *ty, *st))
            .collect();
        let mut seq = Vec::new();
        let mut entries = Vec::new();
        for (t, w, ty, str_term) in &info {
            let val = self.solver.get_value_i64(*t).unwrap_or(0);
            let raw = if *w <= 32 { val as i32 as i64 } else { val };
            seq.push(raw);
            let (value, method) = match ty {
                Ty::Long => (NondetValue::Long(raw), "nondetLong"),
                Ty::Str => {
                    let s = str_term
                        .and_then(|st| self.solver.get_value_string(st))
                        .unwrap_or_default();
                    (NondetValue::Str(s), "nondetString")
                }
                _ => (NondetValue::Int(raw as i32), "nondetInt"),
            };
            entries.push(NondetEntry {
                value,
                nondet_method: method,
                line: None,
            });
        }
        Witness {
            nondet_sequence: seq,
            entries,
            // Sequential engine: no interleaving to record.
            schedule: Vec::new(),
            choices: Vec::new(),
        }
    }
}

#[cfg(test)]
mod bounded_publish_tests {
    use super::*;
    use ajave_ir::{Block, Body, Obligation, ObligationKind, Terminator, VarInfo, VarKind};

    fn key(name: &str) -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: name.into(),
            desc: "()V".into(),
        }
    }

    /// Two blocks in sequence, with the obligation in the second.
    ///
    ///     bb0 -> bb1
    ///             check #0
    ///
    /// A cut at bb0 can reach bb1, so the obligation is at risk. A cut at bb1
    /// is *after* nothing, but the obligation lives in bb1 itself, so it is
    /// still at risk. The interesting case is a cut in a block that cannot
    /// reach the obligation at all.
    fn two_blocks(extra_block: bool) -> (Program, MethodKey) {
        let mk = key("main");
        let mut blocks = vec![
            Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts: vec![],
                term: Terminator::Goto(BlockId(1)),
                exceptional: vec![],
            },
            Block {
                id: BlockId(1),
                bytecode_offset: 1,
                stmts: vec![Stmt::Check(ObligationId(0))],
                term: Terminator::Return(None),
                exceptional: vec![],
            },
        ];
        if extra_block {
            // bb2 is a dead end reachable from nothing that reaches bb1.
            blocks.push(Block {
                id: BlockId(2),
                bytecode_offset: 2,
                stmts: vec![],
                term: Terminator::Return(None),
                exceptional: vec![],
            });
        }
        let mut prog = Program::default();
        prog.bodies.insert(
            mk.clone(),
            Body {
                is_static: true,
                key: mk.clone(),
                entry: BlockId(0),
                vars: vec![VarInfo {
                    kind: VarKind::Local(0),
                    ty: Ty::Int,
                }],
                obligations: vec![Obligation {
                    id: ObligationId(0),
                    kind: ObligationKind::Assertion,
                    cond: Operand::Const(Const::Int(0)),
                    guarded: false,
                    bytecode_offset: 1,
                    line: None,
                }],
                blocks,
            },
        );
        prog.entry = Some(mk.clone());
        (prog, mk)
    }

    /// The soundness argument behind the `Bounded { k }` publish rule.
    ///
    /// `Bounded { k }` says the search covered *this obligation* to depth k,
    /// and `k-induction` acts on that — it discharges outright when the
    /// reachable code is loop-free. An obligation sitting past a point where
    /// exploration stopped has no bounded result to report, and claiming one
    /// is the producer/consumer disagreement `CLAUDE.md` records for this
    /// artifact.
    ///
    /// The rule this replaced published for every open obligation in the entry
    /// method whenever the run truncated *anywhere*, which is exactly the
    /// claim this test says must not be made.
    #[test]
    fn an_obligation_past_a_cut_has_no_bounded_result_to_report() {
        let (prog, mk) = two_blocks(false);
        let mut cuts = BTreeSet::new();
        cuts.insert((mk.clone(), BlockId(0)));

        let at_risk = obligations_at_risk(&prog, &cuts);
        assert!(
            at_risk.contains(&(mk.clone(), ObligationId(0))),
            "exploration stopped at bb0, which reaches the obligation in bb1"
        );
    }

    /// The other half: a truncation somewhere that cannot reach the obligation
    /// does not taint it. Without this the rule would be sound and useless —
    /// any cut anywhere would suppress every bounded result, which is what the
    /// whole-run `all_paths_complete` gate used to do.
    #[test]
    fn a_cut_that_cannot_reach_the_obligation_leaves_it_reportable() {
        let (prog, mk) = two_blocks(true);
        let mut cuts = BTreeSet::new();
        cuts.insert((mk.clone(), BlockId(2)));

        let at_risk = obligations_at_risk(&prog, &cuts);
        assert!(
            !at_risk.contains(&(mk.clone(), ObligationId(0))),
            "bb2 is a dead end; nothing it could have explored reaches bb1"
        );
    }

    /// The -16 this rule exists to prevent.
    ///
    /// A run that stops on the wall clock has `all_paths_complete == false`
    /// and, on a clean program, no violations — the two conditions the old
    /// nesting-based guard tested. If the enclosing `budget_left()` check is
    /// ever refactored away, every open obligation is handed a
    /// `Bounded { k }` claiming a search depth the run never reached, and
    /// `k-induction` converts the loop-free ones straight into discharges.
    #[test]
    fn bounded_is_not_published_when_the_slice_expired() {
        assert!(
            !may_publish_bounded(false, false, false, true),
            "a run that stopped on the clock reached no depth to report"
        );
        assert!(
            !may_publish_bounded(true, true, false, true),
            "an explicitly exhausted run reached no depth to report either"
        );
    }

    /// The other half: the rule has to still fire for the case it is for, or
    /// it would be sound and useless — `k-induction` and `imc` both starve
    /// without `Bounded`.
    #[test]
    fn bounded_is_published_when_the_run_stopped_on_depth() {
        assert!(
            may_publish_bounded(false, true, false, true),
            "budget remaining and paths incomplete means depth was the cut"
        );
    }

    /// A complete search is discharged outright, and a search with a violation
    /// is not evidence of anything a consumer may use.
    #[test]
    fn bounded_says_nothing_about_a_complete_or_a_violated_run() {
        assert!(!may_publish_bounded(false, true, true, true));
        assert!(!may_publish_bounded(false, true, false, false));
    }

    use std::time::Duration;

    const SPENT: Duration = Duration::from_secs(10);

    /// The guard that makes resumption affordable. A deeper pass costs at least
    /// what the last one did — the bound doubles *and* the restart repeats the
    /// prefix — so starting one with less than that on the clock produces a
    /// second truncated result and reports nothing for the time.
    ///
    /// The first version asked only whether the clock had already expired,
    /// which is a much weaker question. On the smoke set that cost 6x to 20x on
    /// individual tasks for a single point.
    #[test]
    fn a_pass_is_not_resumed_without_time_to_finish_it() {
        assert!(!should_resume_deeper(
            false,
            false,
            1,
            true,
            SPENT,
            Some(Duration::from_secs(15))
        ));
        assert!(should_resume_deeper(
            false,
            false,
            1,
            true,
            SPENT,
            Some(Duration::from_secs(25))
        ));
    }

    /// A complete search has nothing left to find, whatever the bound.
    #[test]
    fn a_complete_pass_is_not_resumed() {
        assert!(!should_resume_deeper(true, false, 1, true, SPENT, None));
    }

    /// Nothing open means nothing to resume *for*. Without this the engine
    /// would spend the tail of every solved task re-exploring it.
    #[test]
    fn a_pass_with_nothing_open_is_not_resumed() {
        assert!(!should_resume_deeper(false, false, 1, false, SPENT, None));
    }

    /// The case resumption exists for: counters bound the pass, something is
    /// still open, and there is time to do better.
    #[test]
    fn a_counter_cut_with_work_left_and_time_left_is_resumed() {
        assert!(should_resume_deeper(
            false,
            false,
            1,
            true,
            SPENT,
            Some(Duration::from_secs(60))
        ));
    }

    /// The `Progress::Suspended` contract: the parameter is bounded, so the
    /// engine reaches `Exhausted` after finitely many entries even with no
    /// deadline to stop it. Doubling from the default reaches the ceiling in
    /// three steps.
    #[test]
    fn the_work_bound_rises_finitely_so_the_engine_terminates() {
        let mut scale = 1u64;
        let mut resumes = 0;
        while should_resume_deeper(false, false, scale, true, SPENT, None) {
            scale *= 2;
            resumes += 1;
            assert!(resumes < 64, "the bound must not rise forever");
        }
        assert_eq!(resumes, 3);
        assert_eq!(scale, SCALE_CEILING);
    }
}
