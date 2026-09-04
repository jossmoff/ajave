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

use log::{debug, info, warn};
use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_core::smt::{SatResult, Solver, SolverFactory, Term};
use ajave_ir::verdict::{NondetEntry, NondetValue, Witness};
use ajave_ir::*;
use ajave_models;

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
        FK { class: class.into(), name: name.into(), desc: desc.into() }
    }
}

/// Maximum number of solver check-sat calls per run to prevent hangs.
const MAX_SOLVER_CALLS: u32 = 10_000;

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
            return self.has_unresolved_in_try.then_some("has_unresolved_in_try");
        }
        if method_explored {
            if assertion_only && !self.has_unresolved_in_try && !self.has_depth_limited_havoc && !self.has_tainted_paths {
                return None;
            }
            if assertion_only {
                if self.has_unresolved_in_try { return Some("has_unresolved_in_try"); }
                if self.has_depth_limited_havoc { return Some("has_depth_limited_havoc"); }
                if self.has_tainted_paths { return Some("has_tainted_paths"); }
            }
            return (!self.all_calls_resolved).then_some("all_calls_resolved");
        }
        if !self.all_paths_complete { return Some("all_paths_complete"); }
        (!self.all_calls_resolved).then_some("all_calls_resolved")
    }

    /// Can we discharge an obligation for `method` given this completeness state?
    ///
    /// For NRE (assertion_only=false), havoced calls to methods that could
    /// throw RuntimeException block discharge — the exception isn't modelled
    /// as an obligation and could cause an undetected runtime exception.
    fn can_discharge(&self, method: &MethodKey, entry: &MethodKey, method_explored: bool, assertion_only: bool) -> bool {
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
            if assertion_only && !self.has_unresolved_in_try && !self.has_depth_limited_havoc && !self.has_tainted_paths {
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
        Terminator::Return(_) | Terminator::Halt
        | Terminator::Throw(_) | Terminator::Diverge(_) => vec![],
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
    done: bool,
    /// Constrain nondet char to ASCII (0-127). Prevents witnesses with
    /// non-ASCII chars that our Character method encodings can't model,
    /// but limits falsification to the ASCII subset.
    pub ascii_only: bool,
}

impl SmtBmc {
    pub fn new(factory: Box<dyn SolverFactory>, max_depth: u32) -> Self {
        SmtBmc {
            fp_arith: encode::fp_arith_default(),
            factory,
            max_depth,
            done: false,
            ascii_only: false,
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

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
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
            completeness: Completeness::new(),
            skipped_obligations: HashSet::new(),
            incomplete_methods: HashSet::new(),
            cut_points: BTreeSet::new(),
            frames: Vec::new(),
            approximated: Approximations::EXACT,
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
                        let is_violation_block = block.stmts.iter().any(|s| {
                            matches!(s, Stmt::Check(o) if *o == *oid)
                        });
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
                        if found { break; }
                        // Follow successors.
                        match &blk.term {
                            Terminator::Goto(t) => {
                                if visited.insert(*t) { queue.push(*t); }
                            }
                            Terminator::Branch { then_, else_, .. } => {
                                if visited.insert(*then_) { queue.push(*then_); }
                                if visited.insert(*else_) { queue.push(*else_); }
                            }
                            Terminator::Switch { default, cases, .. } => {
                                if visited.insert(*default) { queue.push(*default); }
                                for (_, t) in cases {
                                    if visited.insert(*t) { queue.push(*t); }
                                }
                            }
                            _ => {}
                        }
                        for edge in &blk.exceptional {
                            if visited.insert(edge.target) { queue.push(edge.target); }
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

        let mut advanced = false;
        for (method, oid, witness) in violations {
            let oref = ObligationRef {
                method,
                id: oid,
            };
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
                ctx.cut_points.iter().map(|(m, b)| format!("{}#bb{}", m.name, b.0)).collect::<Vec<_>>(),
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
            let cuts_accounted =
                ctx.completeness.all_paths_complete || !at_risk.is_empty();
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
                    let method_explored = &oref.method == entry || ctx.inlined_methods.contains(&oref.method);
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
                    } else if !ctx.completeness.can_discharge(&oref.method, entry, method_explored, assertion_only) {
                        ctx.completeness
                            .discharge_blocker(&oref.method, entry, method_explored, assertion_only)
                            .unwrap_or("completeness")
                    } else if ctx.skipped_obligations.contains(&(oref.method.clone(), oref.id)) {
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
                let trunc: std::collections::BTreeSet<String> =
                    ctx.incomplete_methods.iter().map(|m| m.to_string()).collect();
                let elsewhere = open_methods.difference(&trunc).count();
                debug!(
                    "smt-bmc: BLOCKER all_paths_complete for every obligation (outer gate); \
                     open in {} method(s), truncated in {} method(s), {} open method(s) \
                     were never truncated",
                    open_methods.len(), trunc.len(), elsewhere
                );
            }
            if !ctx.completeness.all_paths_complete && violations_empty {
                // Bounded publishing only when no violations at all
                // (conservative: bounded status is only useful when clean).
                // Also skip obligations that had a tainted-path violation
                // suppressed — their bounded status is unsound because the
                // solver DID find a satisfying assignment for the error path.
                for oref in bb.open() {
                    if &oref.method == entry
                        && !ctx.skipped_obligations.contains(&(oref.method.clone(), oref.id))
                    {
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

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
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
    fn budget_left(&self) -> bool {
        let k = budget_scale();
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
            Rvalue::Nondet(ty, _) | Rvalue::Havoc(ty, _) | Rvalue::Cast(ty, _, _) => self.width_of_ty(ty),
            Rvalue::Cmp(_, _, _) | Rvalue::InstanceOf { .. } | Rvalue::ArrayLength(_) => 32,
            Rvalue::GetStatic(fk) | Rvalue::GetField { field: fk, .. } => Self::field_elem_width(&fk.desc),
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
            Operand::Var(v) => {
                self.body.vars.get(v.0 as usize)
                    .map(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
                    .unwrap_or(false)
            }
        }
    }

    fn operand_float_tainted(&self, op: &Operand) -> bool {
        matches!(op, Operand::Var(v) if self.float_tainted.contains(v))
    }

    fn field_key_raw(fk: &FieldKey) -> FK {
        FK { class: fk.class.clone(), name: fk.name.clone(), desc: fk.desc.clone() }
    }

    fn field_key_resolved(&self, fk: &FieldKey) -> FK {
        let resolved_class = self.prog.resolve_field_class(&fk.class, &fk.name, &fk.desc);
        FK { class: resolved_class, name: fk.name.clone(), desc: fk.desc.clone() }
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
            Rvalue::Call { target, args, is_virtual } => {
                if ajave_models::STR_OWNERS.contains(&target.class.as_str()) {
                    let unmodelled = !self.str_call_modelled(target, args);
                    if unmodelled {
                        log::debug!("smt-bmc: TAINT-SOURCE str {}.{}{}", target.class, target.name, target.desc);
                    }
                    return unmodelled;
                }
                if self.math_call_modelled(target) {
                    return false;
                }
                if self.can_inline(target, *is_virtual) {
                    return false;
                }
                log::debug!("smt-bmc: TAINT-SOURCE call {}.{}{}", target.class, target.name, target.desc);
                true
            }
            Rvalue::Use(o) => self.operand_tainted(o),
            Rvalue::Neg(o) => {
                self.operand_tainted(o)
                    || self.operand_is_float(o) || self.operand_float_tainted(o)
            }
            Rvalue::Cast(_, _, o) => {
                self.operand_tainted(o)
                    || self.operand_is_float(o) || self.operand_float_tainted(o)
            }
            // Float arithmetic and comparison are encoded in the SMT
            // FloatingPoint theory, so a float operand no longer implies an
            // imprecise result. Only operators outside that encoding — and
            // pre-existing taint — still contaminate.
            Rvalue::Bin(op, a, b) => {
                let float_operand = self.operand_is_float(a) || self.operand_is_float(b);
                let modelled = float_operand && fp_binop_modelled(*op);
                self.operand_tainted(a) || self.operand_tainted(b)
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
            if (self.operand_is_float(a) || self.operand_is_float(b))
                && fp_binop_modelled(*op)
            {
                return self.operand_float_tainted(a) && self.operand_float_tainted(b)
                    && false;
            }
        }
        match rv {
            Rvalue::Use(o) | Rvalue::Neg(o) => {
                self.operand_float_tainted(o) || self.operand_is_float(o)
            }
            Rvalue::Cast(_, _, o) => {
                self.operand_float_tainted(o) || self.operand_is_float(o)
            }
            Rvalue::Bin(_, a, b) => {
                self.operand_float_tainted(a) || self.operand_float_tainted(b)
                    || self.operand_is_float(a) || self.operand_is_float(b)
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
            self.solver.fresh_array(&format!("f_{}_{}", k.class.replace('/', "_"), k.name), elem_width)
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
            self.solver.fresh_str_array(&format!("fs_{}_{}", k.class.replace('/', "_"), k.name))
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
                    if let Some(class) = params.iter().find(|(s, _)| *s == slot as usize).map(|(_, c)| c.clone()) {
                        let vid = ajave_ir::VarId(vid_idx as u32);
                        let t = self.get_var(vid);
                        self.assert_nonzero(t);
                        // Store the declared type so instanceof checks work
                        let type_id = self.get_type_id(&class) as i64;
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
                b'J' | b'D' => { pos += 1; slot += 2; }
                b'L' => {
                    pos += 1;
                    let class_start = pos;
                    while pos < bytes.len() && bytes[pos] != b';' { pos += 1; }
                    let class = std::str::from_utf8(&bytes[class_start..pos]).unwrap_or("").to_string();
                    pos += 1;
                    result.push((slot, class));
                    slot += 1;
                }
                b'[' => {
                    // Array type: [L...; or [I etc — the full descriptor is the class
                    let arr_start = start;
                    while pos < bytes.len() && bytes[pos] == b'[' { pos += 1; }
                    if pos < bytes.len() && bytes[pos] == b'L' {
                        while pos < bytes.len() && bytes[pos] != b';' { pos += 1; }
                        pos += 1;
                    } else if pos < bytes.len() {
                        pos += 1;
                    }
                    let class = std::str::from_utf8(&bytes[arr_start..pos]).unwrap_or("").to_string();
                    result.push((slot, class));
                    slot += 1;
                }
                _ => { pos += 1; slot += 1; }
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
                        vid.0, lo, hi, block_id.0
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
        if (self.solver_calls as u64) > MAX_SOLVER_CALLS as u64 * budget_scale() {
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
        if (self.solver_calls as u64) > MAX_SOLVER_CALLS as u64 * budget_scale() {
            self.exhausted = true;
            return (SatResult::Unknown, None);
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
