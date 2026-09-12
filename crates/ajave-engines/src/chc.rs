//! CHC (Constrained Horn Clauses) engine — inter-procedural.
//!
//! Translates the program to a set of Horn clauses in SMT-LIB2 CHC format
//! and shells out to Z3 (Spacer). Direction: Over.
//!
//! Key feature: **inter-procedural encoding** with method summary relations.
//! Each method with a body gets a summary relation `mN_summary(params..., ret)`.
//! Call sites invoke the callee's summary, producing recursive Horn clauses
//! for recursive programs. Z3's Spacer computes fixpoints over these.
//!
//! Uses LIA (linear integer arithmetic) for the inter-procedural encoding
//! because Spacer's fixpoint engine works best with integers. Falls back to
//! BV for the single-method encoding when there are no inter-procedural calls.

use crate::body_analysis::body_uses_float_types;
use crate::smt_text::{self, LiaTheory, SmtTheory};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::Write as IoWrite;
use std::process::{Command, Stdio};

use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_ir::*;
use log::{debug, info, trace, warn};

pub struct ChcEngine {
    solver_binary: String,
    done: bool,
    /// Multiplier on the per-query solver bound. This engine's resumable
    /// precision parameter — see `CHC_TIMEOUT_SCALE_CEILING`.
    timeout_scale: u32,
}

impl Default for ChcEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl ChcEngine {
    pub fn new() -> Self {
        let binary = std::env::var("ROAST_CHC_SOLVER").unwrap_or_else(|_| "z3".to_string());
        ChcEngine {
            solver_binary: binary,
            done: false,
            timeout_scale: 1,
        }
    }

    pub fn available(&self) -> bool {
        Command::new(&self.solver_binary)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok()
    }
}

impl Engine for ChcEngine {
    fn id(&self) -> EngineId {
        EngineId("chc")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    /// A shrinking open set is its only lever — an obligation another engine
    /// closed is one fewer clause in the query, and that is sometimes the
    /// difference between `unknown` and `unsat`.
    fn interest(&self) -> Interest {
        Interest::STATUS
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        // `open_or_unconfirmed`, not `open`: a violation from an
        // under-approximating engine is a *candidate* until JVM replay
        // confirms it, and `open()` hides those obligations from every
        // over-approximating engine. Whichever engine published first then
        // won outright, so a spurious candidate permanently blocked the
        // proof that would have refuted it. `proved_safe` records the
        // discharge either way, and `verdict_excluding` turns it into a
        // TRUE only once the violation is actually refuted.
        let open = bb.open_or_unconfirmed();
        if open.is_empty() {
            debug!("chc: nothing open; nothing to prove");
            return Progress::Exhausted;
        }
        debug!("chc: reached with {} open obligation(s)", open.len());

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };

        if !body.is_fully_lifted() {
            return Progress::Blocked;
        }

        // CHC's LIA encoding only models integer arithmetic, not heap/arrays.
        // Skip if any reachable method uses arrays, field access, or unresolved
        // calls to library methods — proving those safe requires heap/string
        // modeling that LIA doesn't have.
        let reachable_methods = prog.reachable_from_entry();
        // Exception handlers are a reason to decline, and this is the guard
        // that makes the two unlocks below sound.
        //
        // The CHC encoding follows normal control flow only: it does not model
        // the exceptional edge out of a throwing operation. For an obligation
        // on the *normal* path that is harmless — not throwing means reaching
        // more assertions and having to prove more of them, which is strictly
        // harder.
        //
        // For an obligation inside a *handler* it is exactly backwards. If the
        // real call throws, the handler runs and its assertion is checked; our
        // model never throws, so the handler is unreachable, the obligation is
        // never examined, and the program is declared safe. That is a wrong
        // TRUE at -16, and `argv-tasks/HttpTransport_false` is one:
        //
        //     try  { assert (object != null); }
        //     catch (Exception e) { assert (e.getMessage().equals("FAKE...")); }
        //
        // The heap and unresolved-call declines below used to hide this, by
        // refusing every program that could throw from those sources. Removing
        // them without this guard turned a precision limit into a soundness
        // bug — a correct guard overridden by a wrong argument about which
        // direction the approximation ran.
        // No handler decline any more: exceptional edges are encoded above.
        // The guard that used to sit here refused every program with a
        // `catch`, which was correct for an encoding that could not reach
        // handler obligations, and cost 157 of 580 records.

        // Heap reads are *not* a reason to decline.
        //
        // `lia_rvalue` already sends `GetField`, `GetStatic`, `ArrayLoad`,
        // `ArrayLength`, `NewArray` and `InstanceOf` to a fresh unconstrained
        // variable, and ignores `PutField`/`ArrayStore`. For an engine that
        // only ever *proves*, that is sound in the right direction: an
        // unconstrained read admits more states than the real one, so the
        // relations over-approximate reachability, and a model showing `error`
        // unreachable over a superset shows it unreachable over the truth.
        // The failure mode is a proof that does not go through, never a wrong
        // one.
        //
        // Declining instead cost almost the whole corpus: CHC encoded a
        // program on **2 of 60** sampled valid-assert tasks, because one
        // `GetStatic` in any reachable method — including one the obligation
        // cannot reach — refused the lot. It is the cheapest engine in the
        // portfolio at ~36ms per decision and it was being asked almost
        // nothing.
        //
        // Float arithmetic below is a different case and still declines: a
        // float encoded as its integer bit pattern computes something that is
        // not floating-point arithmetic at all, which is wrong rather than
        // merely coarse.
        let _ = body_uses_heap_ops;
        // Floats have no integer encoding. `lia_operand` turns a float constant
        // into its raw bit pattern and the arithmetic below then treats it as
        // an integer, which computes something that is not floating-point
        // addition at all -- the same defect recorded for the BMC in
        // `smt_bmc/encode.rs`. Overflow guards do not help: the values were
        // never integers to begin with.
        //
        // Declining the whole program is heavier than it needs to be: havocing
        // just the float-valued rvalues would be sound and would keep the
        // programs whose assertion is about integers and whose `double` is
        // incidental. That is 37 of the 142 unproven TRUE tasks. Not done yet.
        let uses_float = reachable_methods
            .iter()
            .any(|mk| prog.body(mk).is_some_and(body_uses_float_types));
        if uses_float && !prog_has_resolvable_calls(prog, entry) {
            info!("chc: skipping — float/double arithmetic, and no LIA encoding applies");
            return Progress::Blocked;
        }
        // Skip if any reachable method has calls to non-Verifier library methods
        // without bodies. These become havoced (unconstrained) in the LIA encoding,
        // which is unsound for discharge — the real method may throw exceptions or
        // return values that violate assertions. Verifier.nondet* calls are safe
        // because CHC models them as unconstrained inputs (correct semantics).
        let has_unresolved = reachable_methods.iter().any(|mk| {
            prog.body(mk).is_some_and(|b| {
                b.blocks.iter().any(|blk| {
                    blk.stmts.iter().any(|s| {
                        if let Stmt::Assign(_, Rvalue::Call { target, .. }) = s {
                            prog.body(target).is_none()
                                && target.class != "org/sosy_lab/sv_benchmarks/Verifier"
                        } else {
                            false
                        }
                    })
                })
            })
        });
        // Same argument as the heap, and the same direction.
        //
        // An unresolved call's return value is already `fresh.fresh()` in
        // `lia_rvalue`, i.e. unconstrained, which admits every value the real
        // method could return and more. For an engine that only proves, that
        // over-approximates.
        //
        // The old comment worried the real method "may throw exceptions": if it
        // does, the assertion downstream is never reached, so our
        // non-throwing model reaches *more* assertions and has to prove *more*
        // of them. Strictly harder, therefore sound. And CHC only attempts
        // Assertion obligations, so the exception itself is not the property.
        //
        // Worth 10 tasks in the same 125-task sample the heap change was worth
        // 18 in — measured, not assumed.
        let _ = has_unresolved;

        // Assertion obligations in any *reachable* method, not just the entry.
        //
        // The filter used to be `oref.method == *entry`, which quietly
        // discarded every assertion living in a helper. `MinePump`'s tasks put
        // theirs in `Specification1..5`, so CHC reached them with five open
        // obligations and encoded none -- the single commonest reason it did
        // nothing, measured across the unproven-TRUE set.
        //
        // Sound, and in fact stronger than needed: a method's precondition is
        // unconstrained here, so the assertion is proved for *every* argument
        // tuple rather than only those its callers can produce. That may fail
        // where a caller-sensitive proof would succeed, which is a precision
        // limit, not a correctness one.
        let reachable_set: std::collections::BTreeSet<MethodKey> =
            reachable_methods.iter().cloned().collect();
        let obs: Vec<ObligationRef> = open
            .iter()
            .filter(|oref| reachable_set.contains(&oref.method))
            // Every obligation kind, not just `Assertion`.
            //
            // Restricting to assertions made CHC structurally absent from the
            // no-runtime-exception property, whose obligations are all
            // `NullDeref`, `ArrayBounds`, `ClassCast` and `ExplicitThrow`.
            // Measured over the 180 unproven NRE tasks that need a proof: CHC
            // reached 94 of them and encoded *nothing*, and the solver ran
            // zero times across the whole set. That is 360 points the engine
            // was never asked about.
            //
            // The encoding already carries what a `NullDeref` proof needs:
            // `New`/`NewArray` are constrained `> 0` (JLS 15.9.4, an
            // allocation is never null) and a created array's length `>= 0`
            // (JLS 15.10.1). An obligation whose condition comes from an
            // allocation is therefore provable; one whose condition comes from
            // a havoced read is not, and fails in the safe direction --
            // `cond == 0` stays satisfiable, so `error` is reachable, the
            // query is `unsat`, and nothing is discharged.
            //
            // That is the general argument for admitting every kind: an
            // obligation this encoding cannot model contributes a condition
            // over unconstrained values, which can only *add* reachable error
            // states. The failure mode is a proof that does not go through.
            .cloned()
            .collect();

        // The single-method encoder and the solver still speak plain ids.
        let obs_ids: Vec<ObligationId> = obs.iter().map(|o| o.id).collect();

        if obs.is_empty() {
            debug!(
                "chc: nothing to encode — {} open obligation(s), none an Assertion in {:?}; \
                 kinds present: {:?}",
                open.len(),
                entry,
                open.iter()
                    .filter_map(|o| prog.body(&o.method).map(|b| (
                        o.method.name.clone(),
                        format!("{:?}", b.obligation(o.id).kind)
                    )))
                    .collect::<std::collections::BTreeSet<_>>()
            );
            return Progress::Exhausted;
        }

        info!("chc: encoding {} obligation(s) for {:?}", obs.len(), entry);

        // Use inter-procedural encoding when the program has calls to methods with bodies.
        let has_interproc_calls = prog_has_resolvable_calls(prog, entry);
        // Candidate invariants from the board.
        //
        // Only from an over-approximating producer that approximated nothing:
        // a bound derived under an approximation is a fact about a different
        // program, and assuming it here would be assuming it about ours. That
        // is exactly what `Approximations` was added to express, and the check
        // is cheap enough that there is no reason to skip it.
        let mut invariants: BlockInvariants = HashMap::new();
        for inv in bb.invariants_for(entry) {
            if let Some((v, lo, hi)) = interval_of(&inv.formula) {
                invariants
                    .entry((inv.at.method.clone(), inv.at.block))
                    .or_default()
                    .push((v.0 as usize, lo, hi));
            }
        }
        if !invariants.is_empty() {
            info!(
                "chc: seeding {} block(s) with interval invariants from another engine",
                invariants.len()
            );
        }

        let smt2 = if has_interproc_calls {
            info!("chc: using inter-procedural LIA encoding");
            drop_empty_quantifiers(&encode_chc_interproc(prog, entry, &obs, &invariants))
        } else {
            info!("chc: using single-method BV encoding");
            drop_empty_quantifiers(&encode_chc_single(body, &obs_ids))
        };

        debug!("chc: generated {} bytes of CHC encoding", smt2.len());
        if let Ok(path) = std::env::var("AJAVE_CHC_DUMP") {
            let _ = std::fs::write(&path, &smt2);
        }
        trace!("chc: encoding:\n{}", &smt2[..smt2.len().min(4000)]);

        let mut advanced = false;
        let mut last_outcome = ChcOutcome::Unknown;
        match run_chc_solver(
            &self.solver_binary,
            &smt2,
            &obs,
            solver_timeout_secs(&budget, self.timeout_scale),
        ) {
            Ok((results, outcome)) => {
                last_outcome = outcome;
                for (oref, safe) in results {
                    if safe {
                        debug!("chc: discharged {}", oref);
                        let _ = bb.publish_with(
                            self.id(),
                            self.direction(),
                            // The inter-procedural encoding declares every
                            // variable an unbounded `Int`, so nothing wraps.
                            // That is a sound over-approximation for a program
                            // whose property does not depend on overflow, and
                            // simply a different program for one that does.
                            if has_interproc_calls {
                                Approximations::INT_WRAPPING
                            } else {
                                Approximations::EXACT
                            },
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
            }
            Err(e) => {
                warn!("chc: solver failed: {}", e);
            }
        }

        // A `unknown` is a query that ran out of `-T`, and it is the one CHC
        // outcome a second attempt can change. Resuming doubles the bound,
        // which is still clamped by whatever time is actually left — so this
        // spends the tail of a task nobody else wanted rather than taking time
        // from the engines ahead.
        //
        // The headroom test matters as much as the outcome test: doubling the
        // bound means the next query may run twice as long, and starting one
        // that the deadline will cut in the middle spends the time and reports
        // nothing.
        let next_query = std::time::Duration::from_secs(
            (solver_timeout_secs(&budget, self.timeout_scale) * 2) as u64,
        );
        if ajave_core::engine::resumption_enabled()
            && last_outcome == ChcOutcome::Unknown
            && self.timeout_scale < CHC_TIMEOUT_SCALE_CEILING
            && budget.deadline.is_none_or(|d| {
                d.saturating_duration_since(std::time::Instant::now()) >= next_query
            })
        {
            self.timeout_scale *= 2;
            self.done = false;
            debug!(
                "chc: solver gave up inside its bound; resuming at {}x",
                self.timeout_scale
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

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Returns true if the body uses array or heap operations that CHC's LIA
/// encoding cannot model: array load/store/new, field get/put, instanceof.
/// Ceiling on the seconds Spacer may spend on one query.
fn solver_timeout_cap() -> u32 {
    std::env::var("AJAVE_CHC_TIMEOUT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(10)
}

/// Seconds Spacer may spend on one query, given this step's slice.
///
/// The doc comment on the constant this replaced said it was "a slice of the
/// remaining budget rather than the whole of it". It was not — it was a flat
/// ten seconds, and the engine took `_budget` and dropped it. That is the shape
/// `CLAUDE.md` calls out under "comments asserting invariants the code does not
/// maintain", and it is why a task with a 295-second deadline was still running
/// after 400: the deadline only ever bound the two engines that read it.
///
/// The cap still applies. A proof needing longer than that is one the earlier
/// engines have already failed to find, and spending the rest of the task on it
/// costs the answers they would have produced.
/// How far the per-query bound may be raised across resumptions. Bounded
/// because `Progress::Suspended` promises it terminates without a deadline.
const CHC_TIMEOUT_SCALE_CEILING: u32 = 4;

fn solver_timeout_secs(budget: &Budget, scale: u32) -> u32 {
    let cap = solver_timeout_cap() * scale;
    match budget.deadline {
        // At least a second: Spacer given zero would answer nothing at all,
        // and a step that cannot answer should not have been entered.
        Some(d) => cap.min(
            d.saturating_duration_since(std::time::Instant::now())
                .as_secs()
                .max(1) as u32,
        ),
        None => cap,
    }
}

// Nested deliberately: the outer match is on the IR node and the inner on
// its payload, which mirrors the IR's own shape.
#[allow(clippy::collapsible_match)]
fn body_uses_heap_ops(body: &Body) -> bool {
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(_, rv) => match rv {
                    Rvalue::ArrayLoad { .. }
                    | Rvalue::ArrayLength(_)
                    | Rvalue::NewArray { .. }
                    | Rvalue::GetField { .. }
                    | Rvalue::GetStatic(_)
                    | Rvalue::InstanceOf { .. } => return true,
                    _ => {}
                },
                Stmt::PutField { .. } | Stmt::ArrayStore { .. } => return true,
                _ => {}
            }
        }
    }
    false
}

fn prog_has_resolvable_calls(prog: &Program, entry: &MethodKey) -> bool {
    let Some(body) = prog.body(entry) else {
        return false;
    };
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(_, Rvalue::Call { target, .. }) = stmt {
                if prog.body(target).is_some() {
                    return true;
                }
            }
        }
    }
    false
}

/// Parse method descriptor to count parameter slots.
/// Returns the number of JVM local slots consumed by parameters.
fn param_slot_count(desc: &str) -> usize {
    let inner = &desc[1..desc.find(')').unwrap_or(desc.len())];
    let bytes = inner.as_bytes();
    let mut pos = 0;
    let mut slots = 0;
    while pos < bytes.len() {
        match bytes[pos] {
            b'J' | b'D' => {
                slots += 2;
                pos += 1;
            }
            b'L' => {
                slots += 1;
                pos = inner[pos..]
                    .find(';')
                    .map(|p| pos + p + 1)
                    .unwrap_or(bytes.len());
            }
            b'[' => {
                slots += 1;
                pos += 1;
                // skip element type
                while pos < bytes.len() && bytes[pos] == b'[' {
                    pos += 1;
                }
                if pos < bytes.len() {
                    if bytes[pos] == b'L' {
                        pos = inner[pos..]
                            .find(';')
                            .map(|p| pos + p + 1)
                            .unwrap_or(bytes.len());
                    } else {
                        pos += 1;
                    }
                }
            }
            _ => {
                slots += 1;
                pos += 1;
            }
        }
    }
    slots
}

/// Find which VarIds correspond to method parameters (by Local slot).
/// Returns (var_index, slot) pairs in slot order.
fn find_param_var_indices(body: &Body, mk: &MethodKey) -> Vec<usize> {
    // From ACC_STATIC, recorded by the lifter. This used to be hardcoded
    // `true` with "assume all methods are static (jayhorn benchmarks are
    // static)", so for an instance method -- where slot 0 holds `this` and
    // parameters start at slot 1 -- every parameter bound one slot early and
    // the summary relation related the wrong variables. An assumption shaped by
    // one benchmark family, compiled into an engine, is what the overfitting
    // rules forbid.
    let is_static = body.is_static;
    let total_param_slots = param_slot_count(&mk.desc);
    let first_slot: u16 = if is_static { 0 } else { 1 };

    let mut params: Vec<(usize, u16)> = Vec::new();
    for (i, vi) in body.vars.iter().enumerate() {
        if let VarKind::Local(slot) = vi.kind {
            if (slot as usize) < total_param_slots + (first_slot as usize) {
                params.push((i, slot));
            }
        }
    }
    params.sort_by_key(|&(_, slot)| slot);
    params.dedup_by_key(|p| p.1);
    params.iter().map(|&(i, _)| i).collect()
}

/// Read `lo <= v && v <= hi` back out of a published claim.
///
/// A consumer that cannot parse a claim must skip it, never guess — the same
/// rule `Blackboard::interval_hints_for_method` follows. Anything but this
/// exact shape returns `None` and is ignored.
fn interval_of(e: &ajave_core::term::Expr) -> Option<(VarId, i64, i64)> {
    use ajave_core::term::{Expr, Op};
    let Expr::Bin(Op::And, lo_e, hi_e) = e else {
        return None;
    };
    let (Expr::Bin(Op::Le, l, lv), Expr::Bin(Op::Le, hv, h)) = (lo_e.as_ref(), hi_e.as_ref())
    else {
        return None;
    };
    let (Expr::Int(lo), Expr::Var(v1), Expr::Var(v2), Expr::Int(hi)) =
        (l.as_ref(), lv.as_ref(), hv.as_ref(), h.as_ref())
    else {
        return None;
    };
    if v1 != v2 {
        return None;
    }
    Some((*v1, *lo, *hi))
}

/// Is this already a name or literal, so naming it again would only add noise?
fn is_atom(expr: &str) -> bool {
    !expr.starts_with('(')
}

/// Universally quantified helper variables introduced by the encoding.
struct FreshGen {
    counter: u32,
    extra_forall: Vec<String>,
}

impl FreshGen {
    fn new() -> Self {
        FreshGen {
            counter: 0,
            extra_forall: Vec::new(),
        }
    }

    /// A fresh binder. LIA declares everything `Int`.
    fn fresh(&mut self) -> String {
        let name = format!("_f{}", self.counter);
        self.counter += 1;
        self.extra_forall.push(format!("({} Int)", name));
        name
    }

    /// Record a binder for a fresh value the shared theory produced.
    ///
    /// `LiaTheory::encode_fresh` names unconstrained values from a
    /// process-wide counter, so they never collide, but nothing declares them.
    /// Each has to become a binder or the clause is ill-sorted -- and they are
    /// how div/rem, narrowing casts and the bitwise operators are represented,
    /// so they are not rare.
    fn note(&mut self, expr: &str) {
        if !expr.starts_with("chc_fresh") {
            return;
        }
        let binder = format!("({} Int)", expr);
        if !self.extra_forall.contains(&binder) {
            self.extra_forall.push(binder);
        }
    }

    fn forall_str(&self) -> String {
        self.extra_forall.join(" ")
    }
}

/// Return type descriptor character from method descriptor.
fn return_type_char(desc: &str) -> char {
    let after = desc.split(')').nth(1).unwrap_or("V");
    after.chars().next().unwrap_or('V')
}

// ---------------------------------------------------------------------------
// LIA operand/rvalue encoding for inter-procedural CHC
// (with overflow guards for soundness)
// ---------------------------------------------------------------------------

// The JVM's integral ranges (JLS 4.2.1). These are what the range constraints
// in `block_app_src` assert about every integral variable, and what the
// overflow side-conditions compare against.
//
// They were declared and never read for a long time, which `CLAUDE.md` records
// as its example of a comment stating a soundness argument that the code did
// not maintain. Referencing them here is the point: the values in the encoding
// and the values in the guard are now the same symbols.
/// Interval bounds another engine published, per block: `(var index, lo, hi)`.
///
/// Keyed by `(MethodKey, BlockId)` and not by `BlockId` alone -- a `BlockId`
/// indexes into one `Body`, and `CLAUDE.md` records what keying a
/// longer-lived collection by it alone cost the last time.
type BlockInvariants = HashMap<(MethodKey, BlockId), Vec<(usize, i64, i64)>>;

const INT_MIN: i64 = -2147483648;
const INT_MAX: i64 = 2147483647;
const LONG_MIN: i64 = i64::MIN;
const LONG_MAX: i64 = i64::MAX;

fn lia_int(value: i32) -> String {
    if value < 0 {
        format!("(- {})", -(value as i64))
    } else {
        value.to_string()
    }
}

fn lia_long(value: i64) -> String {
    if value < 0 {
        format!("(- {})", -(value as i128))
    } else {
        value.to_string()
    }
}

fn lia_operand(op: &Operand, var_map: &HashMap<usize, String>) -> String {
    match op {
        Operand::Var(v) => var_map
            .get(&(v.0 as usize))
            .cloned()
            .unwrap_or_else(|| format!("v{}", v.0)),
        Operand::Const(Const::Int(n)) => lia_int(*n),
        Operand::Const(Const::Long(n)) => lia_long(*n),
        Operand::Const(Const::Null) => "0".to_string(),
        Operand::Const(Const::Str(_)) => "1".to_string(),
        Operand::Const(Const::Float(f)) => lia_int(f.to_bits() as i32),
        Operand::Const(Const::Double(d)) => lia_long(d.to_bits() as i64),
        Operand::Const(_) => "0".to_string(),
    }
}
/// Whether an rvalue's *result* or any operand it computes over is
/// floating-point. Only the arithmetic forms matter: a `Use` of a float merely
/// copies a value that was itself havoced where it was produced, and the
/// unmodelled forms already havoc.
fn rvalue_is_float(rv: &Rvalue, is_float: &dyn Fn(&Operand) -> bool) -> bool {
    match rv {
        Rvalue::Bin(_, a, b) => is_float(a) || is_float(b),
        Rvalue::Neg(o) => is_float(o),
        Rvalue::Cmp(_, a, b) => is_float(a) || is_float(b),
        Rvalue::Cast(to, from, _) => matches!(
            (to, from),
            (Ty::Float | Ty::Double, _) | (_, Ty::Float | Ty::Double)
        ),
        _ => false,
    }
}

fn lia_rvalue(
    rv: &Rvalue,
    var_map: &HashMap<usize, String>,
    fresh: &mut FreshGen,
    is_wide: &dyn Fn(&Operand) -> bool,
    is_float: &dyn Fn(&Operand) -> bool,
    overflow: &mut Vec<String>,
    theory: &LiaTheory,
) -> String {
    // Floating-point values have no integer encoding. Computing on their bit
    // patterns is not floating-point arithmetic -- it is a different function
    // that happens to be total, which is wrong rather than coarse. Havoc is the
    // sound answer for an over-approximating engine, and it is what this file
    // already does for `Div`, `Rem` and the shifts.
    if rvalue_is_float(rv, is_float) {
        log::debug!("chc-imprecision: float-valued rvalue");
        return fresh.fresh();
    }
    match rv {
        Rvalue::Use(o) => lia_operand(o, var_map),
        Rvalue::Nondet(..) | Rvalue::Havoc(_, _) => {
            log::debug!("chc-imprecision: Nondet/Havoc");
            fresh.fresh()
        }
        Rvalue::Bin(op, a, b) => {
            // LIA has no bitwise or shift operators, and its `div`/`mod` are
            // Euclidean where Java's truncate toward zero. `encode_binop`
            // treats being asked for one of those as unreachable, because
            // `Encoder` filters them first -- and this function does not go
            // through `Encoder`.
            //
            // That invariant held only because an unrelated gate kept these
            // bodies away from CHC entirely. Widening which obligations CHC
            // sees (open_or_unconfirmed) reached a body containing `%` and
            // panicked. An unconstrained value is the sound answer for an
            // over-approximating engine: it contains the real one, so any
            // proof over it holds of the program.
            if !theory.models_binop(op) {
                // Bitwise operators on boolean-valued operands are exactly
                // expressible in LIA, and that covers most of their uses here:
                // the lifter lowers `&&`, `||` and `^` on booleans to the
                // bitwise opcodes, so the operands are 0 or 1.
                //
                // Measured across 16 failing tasks: `And` was the joint-largest
                // source of unconstrained values (104 occurrences), and an
                // unconstrained value in a guard makes the guarded block
                // reachable -- which is how blocks holding `assert false`
                // became reachable and the encoding admitted a counterexample
                // that the program does not have.
                //
                // Shape: exact when both operands are in {0,1}, unconstrained
                // otherwise. The `ite` keeps that in one expression, so no
                // side-channel for constraints is needed, and the fallback
                // branch is exactly what this returned before.
                if matches!(op, BinOp::And | BinOp::Or | BinOp::Xor) {
                    let l = lia_operand(a, var_map);
                    let r = lia_operand(b, var_map);
                    let free = fresh.fresh();
                    let both_bool = format!("(and (>= {l} 0) (<= {l} 1) (>= {r} 0) (<= {r} 1))");
                    let exact = match op {
                        BinOp::And => format!("(ite (and (= {l} 1) (= {r} 1)) 1 0)"),
                        BinOp::Or => format!("(ite (or (= {l} 1) (= {r} 1)) 1 0)"),
                        _ => format!("(ite (= {l} {r}) 0 1)"),
                    };
                    return format!("(ite {both_bool} {exact} {free})");
                }
                log::debug!("chc-imprecision: binop {:?}", op);
                return fresh.fresh();
            }
            let l = lia_operand(a, var_map);
            let r = lia_operand(b, var_map);
            let e = theory.encode_binop(op, &l, &r);
            if smt_text::overflowing(op) {
                overflow.push(smt_text::lia_overflow_cond(&e, is_wide(a) || is_wide(b)));
            }
            e
        }
        Rvalue::Neg(o) => {
            let v = lia_operand(o, var_map);
            let e = theory.encode_neg(&v);
            // Negating INT_MIN overflows.
            overflow.push(smt_text::lia_overflow_cond(&e, is_wide(o)));
            e
        }
        Rvalue::Cast(to, from, o) => {
            // Narrowing truncates, which LIA cannot express; same reasoning as
            // the operators above.
            if !theory.models_cast(to, from) {
                log::debug!("chc-imprecision: cast {:?}->{:?}", from, to);
                return fresh.fresh();
            }
            let v = lia_operand(o, var_map);
            theory.encode_cast(to, from, &v)
        }
        Rvalue::Cmp(_, a, b) => {
            let l = lia_operand(a, var_map);
            let r = lia_operand(b, var_map);
            format!("(ite (< {} {}) (- 1) (ite (= {} {}) 0 1))", l, r, l, r)
        }
        Rvalue::New(_) => fresh.fresh(),
        other => {
            log::debug!(
                "chc-imprecision: rvalue {}",
                match other {
                    Rvalue::GetStatic(_) => "GetStatic",
                    Rvalue::GetField { .. } => "GetField",
                    Rvalue::ArrayLoad { .. } => "ArrayLoad",
                    Rvalue::ArrayLength(_) => "ArrayLength",
                    Rvalue::NewArray { .. } => "NewArray",
                    Rvalue::InstanceOf { .. } => "InstanceOf",
                    Rvalue::Call { .. } => "Call",
                    _ => "other",
                }
            );
            fresh.fresh()
        }
    }
}

// ---------------------------------------------------------------------------
// Inter-procedural CHC encoding (LIA + overflow guards)
//
// Uses LIA (fast for Spacer fixpoint) but adds overflow-to-error guards
// on method summaries: if any summary returns a value outside 32-bit range,
// error is forced reachable. This makes the encoding sound: CHC can only
// prove safety if no integer overflow occurs on any reachable path.
// ---------------------------------------------------------------------------

fn encode_chc_interproc(
    prog: &Program,
    entry: &MethodKey,
    obligations: &[ObligationRef],
    // Interval bounds another engine established, as (method, block) -> [(var, lo, hi)].
    //
    // Candidate invariants, in the Horn-solver sense: facts that are true of
    // every reachable state and that Spacer would otherwise have to rediscover.
    // They are the most valuable thing you can hand a Horn solver, and until
    // today they lived in a `HashMap` only the BMC could read.
    //
    // SOUNDNESS. Adding a fact to a clause body makes the relation *smaller*,
    // and in this encoding `sat` means safe — so a **false** "invariant" could
    // exclude a genuinely reachable error state and claim safety. That is a
    // wrong TRUE at -16, which is why only bounds from an over-approximating
    // producer that approximated nothing are accepted; see the caller.
    invariants: &BlockInvariants,
) -> String {
    let mut out = String::new();
    out.push_str("(set-logic HORN)\n\n");
    // The same theory the IMC encoder uses. Sharing it is what keeps the two
    // from drifting: div/rem and narrowing casts are unconstrained in one place,
    // and the overflow condition below comes from one place too.
    let theory = LiaTheory::new("chc_");

    let reachable: Vec<MethodKey> = prog
        .reachable_from_entry()
        .into_iter()
        .filter(|mk| prog.body(mk).is_some())
        .filter(|mk| mk.name != "<clinit>" && mk.name != "<init>")
        .collect();

    let mut all_methods: Vec<MethodKey> = vec![entry.clone()];
    for mk in &reachable {
        if mk != entry && !all_methods.contains(mk) {
            all_methods.push(mk.clone());
        }
    }

    let method_ids: HashMap<MethodKey, String> = all_methods
        .iter()
        .enumerate()
        .map(|(i, mk)| (mk.clone(), format!("m{}", i)))
        .collect();

    let method_params: HashMap<MethodKey, Vec<usize>> = all_methods
        .iter()
        .filter_map(|mk| {
            prog.body(mk)
                .map(|body| (mk.clone(), find_param_var_indices(body, mk)))
        })
        .collect();

    // Declare summary relations for non-void methods.
    for mk in &all_methods {
        let mid = &method_ids[mk];
        let ret_ch = return_type_char(&mk.desc);
        if ret_ch == 'V' {
            continue;
        }
        let params = method_params.get(mk).map(|v| v.len()).unwrap_or(0);
        let sig = (0..params + 1).map(|_| "Int").collect::<Vec<_>>().join(" ");
        out.push_str(&format!(
            "; summary for {}\n(declare-fun {}_s ({}) Bool)\n",
            mk, mid, sig
        ));
    }

    // Declare block relations for each method, over the variables that block
    // actually needs on entry rather than every variable in the method.
    //
    // Spacer has to synthesise an interpretation for each predicate and the
    // difficulty grows sharply with arity, so passing dead state is not merely
    // wasteful. Measured on a five-line recursive program whose summary is
    // `f(n) >= 0`: 14-ary block predicates timed out, the same program over
    // its two live variables is `sat` in 0.01s.
    //
    // `liveness` documents why an imprecise live set cannot cause a wrong
    // verdict -- an omitted variable becomes an unconstrained binder in the
    // successor, which over-approximates.
    let live: HashMap<MethodKey, BTreeMap<BlockId, BTreeSet<usize>>> = all_methods
        .iter()
        .filter_map(|mk| {
            prog.body(mk)
                .map(|b| (mk.clone(), crate::liveness::live_in(b)))
        })
        .collect();
    // Parameters count as live in every block, whatever liveness says.
    //
    // The summary clause for a method concludes `m_s(params, ret)` at each
    // return site, so the parameters have to still be in scope there -- but a
    // parameter read only at the top of the method is dead by the time control
    // reaches a `return`. Dropping it made the summary quantify the parameter
    // universally, so `f` was described as able to return v4+1 for *any*
    // argument. That is an over-approximation and therefore sound, which is
    // exactly why it showed up as an unprovable safe program rather than a
    // wrong answer -- but it destroys the summary, which is the whole point of
    // the inter-procedural encoding.
    // Ghost state: a reference-typed variable `i` may carry a shadow integer
    // at slot `n_vars + i` holding the length of the array it refers to. See
    // `GHOST LENGTHS` below for why this is a variable rather than a predicate
    // or an uninterpreted function.
    let ghost_of = |n_vars: usize, i: usize| -> usize { n_vars + i };

    // Only the references whose length is actually read.
    //
    // Every predicate argument costs the solver, and sharply: this file
    // already records a five-line program that times out with 14-ary block
    // predicates and is `sat` in 0.01s over its two live variables. Giving a
    // shadow to *every* reference doubled the state and cost 9 points on
    // valid-assert -- 7 more timeouts -- while gaining nothing there, because
    // an assertion is rarely about an array bound.
    //
    // So the set is seeded from the operands of `ArrayLength` and closed
    // backwards through copies: if `a.length` is read and `a = b`, then `b`
    // needs the shadow too, or the length does not survive the assignment
    // chain the lifter produces between a `new` and its use.
    let ghost_vars: HashMap<MethodKey, BTreeSet<usize>> = all_methods
        .iter()
        .filter_map(|mk| prog.body(mk).map(|b| (mk.clone(), b)))
        .map(|(mk, b)| {
            let mut want: BTreeSet<usize> = BTreeSet::new();
            for blk in &b.blocks {
                for st in &blk.stmts {
                    if let Stmt::Assign(_, Rvalue::ArrayLength(Operand::Var(v))) = st {
                        want.insert(v.0 as usize);
                    }
                }
            }
            // Copies propagate the need backwards; iterate to a fixpoint
            // because the chain can run through several blocks.
            loop {
                let before = want.len();
                for blk in &b.blocks {
                    for st in &blk.stmts {
                        if let Stmt::Assign(d, Rvalue::Use(Operand::Var(src))) = st {
                            if want.contains(&(d.0 as usize)) {
                                want.insert(src.0 as usize);
                            }
                        }
                    }
                }
                if want.len() == before {
                    break;
                }
            }
            (mk, want)
        })
        .collect();

    let live_at = |mk: &MethodKey, bid: u32| -> Vec<usize> {
        let mut set: BTreeSet<usize> = live
            .get(mk)
            .and_then(|m| m.get(&BlockId(bid)))
            .cloned()
            .unwrap_or_default();
        if let Some(ps) = method_params.get(mk) {
            set.extend(ps.iter().copied());
        }
        // A live reference drags its ghost length along: the length has to be
        // in the block predicate, or it cannot survive the edge into a loop
        // body, which is exactly where array bounds are proved.
        if let Some(b) = prog.body(mk) {
            let n = b.vars.len();
            let want = ghost_vars.get(mk);
            let refs: Vec<usize> = set
                .iter()
                .filter(|i| b.vars.get(**i).is_some_and(|vi| vi.ty == Ty::Ref))
                .filter(|i| want.is_some_and(|w| w.contains(*i)))
                .map(|i| ghost_of(n, *i))
                .collect();
            set.extend(refs);
        }
        set.into_iter().collect()
    };

    // No space invariants. This encoder used to abstract the heap with one
    // uninterpreted predicate per shape -- `phi_arr(ref, idx, val)`,
    // `phi_obj(ref, field, val)`, `phi_static(field, val)`,
    // `phi_len(ref, len)` -- after JayHorn (Kahsai/Kersten/Ruemmer/Schaef,
    // LPAR-21). A read became `assume phi(..)`, a write `assert phi(..)`, and
    // the Horn solver had to infer the invariant.
    //
    // **It was unsound, in exactly the way its own comment described.** A
    // predicate appearing in a clause *body* is chosen by the solver, and
    // nothing forces it to be large. Choosing it empty makes every
    // `assume phi(..)` unsatisfiable, so the read path dies, everything
    // downstream becomes unreachable, and the program is declared safe.
    //
    // The guard was `heap_is_closed`: every reachable method lifted, no
    // unresolved call, no havoced reference. That is not the right condition
    // and could not be, because closure of the *program* says nothing about
    // whether the *invariant* is adequately constrained. Measured, it held on
    // 28 of 169 tasks, proved none of them, and produced wrong TRUEs on
    // `MinePump/spec1-5_product45` and `java-ranger-regression/TCAS_prop1`.
    //
    // Those two were invisible until the malformed entry fact below was fixed:
    // Z3 had been refusing every such query with `unknown`. That is the third
    // time in this file that repairing a well-formedness bug revealed a
    // soundness one -- `CLAUDE.md` calls it "unsoundness masked by an
    // unrelated conservative gate".
    //
    // The one case that carried the argument for space invariants was array
    // *length*, and it is now a ghost variable (see `GHOST LENGTHS`) --
    // ordinary threaded state rather than a solver-chosen interpretation, so
    // it cannot make a read infeasible, and it needs no closure condition.
    // Field and array *contents* are unconstrained reads again: less precise,
    // and honest.

    for mk in &all_methods {
        let Some(body) = prog.body(mk) else { continue };
        let mid = &method_ids[mk];

        out.push_str(&format!("; blocks for {}\n", mk));
        for block in &body.blocks {
            let sig = live_at(mk, block.id.0)
                .iter()
                .map(|_| "Int")
                .collect::<Vec<_>>()
                .join(" ");
            out.push_str(&format!(
                "(declare-fun {}_b{} ({}) Bool)\n",
                mid, block.id.0, sig
            ));
        }
    }

    out.push_str("\n(declare-fun error () Bool)\n\n");

    // Note: LIA is an over-approximation for overflow-free programs.
    // The CHC engine only proves safety (Over direction), and can only
    // discharge obligations that BMC couldn't resolve. For programs where
    // overflow is the bug, BMC will find the violation. For programs where
    // the property holds regardless of overflow, LIA safety ⊇ BV safety.
    // Conservative: we only discharge when the entry method's nondet
    // inputs are bounded by explicit branch guards before recursive calls.

    // Encode each method.
    for mk in &all_methods {
        let Some(body) = prog.body(mk) else { continue };
        let mid = method_ids[mk].clone();
        let n_vars = body.vars.len();
        let param_indices = method_params.get(mk).cloned().unwrap_or_default();
        let ret_ch = return_type_char(&mk.desc);
        // Obligations are no longer entry-only, so this is kept only for the
        // summary/return clauses that still distinguish the entry method.
        let _is_entry = mk == entry;

        // Slots `0..n_vars` are the program's variables; `n_vars..2*n_vars`
        // are the ghost lengths, one per variable, used only for the
        // reference-typed ones. Indexing them at a fixed offset keeps the
        // mapping between a reference and its length a single addition.
        let total_slots = 2 * n_vars;
        let src_vars: Vec<String> = (0..total_slots).map(|i| format!("v{}", i)).collect();
        let dst_vars: Vec<String> = (0..total_slots).map(|i| format!("w{}", i)).collect();

        let forall_src: String = src_vars
            .iter()
            .map(|v| format!("({} Int)", v))
            .collect::<Vec<_>>()
            .join(" ");

        // Every clause body that mentions a source block goes through here, so
        // conjoining the block's invariant once reaches all of them.
        // A block whose live set is empty declares a 0-ary predicate, and
        // SMT-LIB spells that as a bare name -- `(p )` is a parse error.
        let app_of = |mid: &str, bid: u32, args: &str| -> String {
            if args.is_empty() {
                format!("{}_b{}", mid, bid)
            } else {
                format!("({}_b{} {})", mid, bid, args)
            }
        };
        let block_app_src = |bid: u32| -> String {
            let args = live_at(mk, bid)
                .iter()
                .map(|i| src_vars[*i].clone())
                .collect::<Vec<_>>()
                .join(" ");
            let app = app_of(&mid, bid, &args);

            // Every integral variable is within its JVM type's range.
            //
            // The encoding uses unbounded `Int`, and without this the solver
            // is free to believe an `int` holds 2^40 -- which makes the
            // overflow side-conditions reachable and every proof fail. That is
            // sound (it only ever refuses to prove) but it refuses almost
            // everything: measured on a bounded recursive program, dropping
            // the overflow clauses turned a timeout into `sat`, and this is
            // the honest way to get the same effect. JLS 4.2.1 fixes the
            // ranges, so this asserts nothing the JVM does not guarantee.
            let mut parts = vec![app];
            for i in live_at(mk, bid) {
                let Some(vi) = body.vars.get(i) else { continue };
                match vi.ty {
                    Ty::Int => {
                        parts.push(format!("(<= (- {}) v{})", -INT_MIN, i));
                        parts.push(format!("(<= v{} {})", i, INT_MAX));
                    }
                    Ty::Long => {
                        parts.push(format!("(<= (- {}) v{})", LONG_MIN.unsigned_abs(), i));
                        parts.push(format!("(<= v{} {})", i, LONG_MAX));
                    }
                    // References are abstract ids, strings are not integers,
                    // and floats are not modelled by this theory; none of them
                    // carries a JLS integer range.
                    Ty::Float | Ty::Double | Ty::Ref | Ty::Str => {}
                }
            }
            // Ghost lengths are outside `body.vars`, so the loop above skips
            // them. An array's length is a non-negative `int` (JLS 10.7)
            // whatever else we know, and saying so is what lets a bound like
            // `i < a.length` rule out a negative index.
            for i in live_at(mk, bid) {
                if i >= n_vars {
                    parts.push(format!("(<= 0 v{})", i));
                    parts.push(format!("(<= v{} {})", i, INT_MAX));
                }
            }

            let Some(bounds) = invariants.get(&(mk.clone(), BlockId(bid))) else {
                return if parts.len() == 1 {
                    parts.pop().unwrap()
                } else {
                    format!("(and {})", parts.join(" "))
                };
            };
            for (idx, lo, hi) in bounds {
                if *idx >= n_vars {
                    continue;
                }
                // Bounds outside i32 are the interval domain's infinities in
                // disguise; they say nothing and only bloat the encoding.
                let (Ok(lo32), Ok(hi32)) = (i32::try_from(*lo), i32::try_from(*hi)) else {
                    continue;
                };
                parts.push(format!("(<= {} v{})", lia_int(lo32), idx));
                parts.push(format!("(<= v{} {})", idx, lia_int(hi32)));
            }
            if parts.len() == 1 {
                parts.pop().unwrap()
            } else {
                format!("(and {})", parts.join(" "))
            }
        };
        let block_app_dst = |bid: u32| -> String {
            let args = live_at(mk, bid)
                .iter()
                .map(|i| dst_vars[*i].clone())
                .collect::<Vec<_>>()
                .join(" ");
            app_of(&mid, bid, &args)
        };

        // The entry fact: any state satisfying the side conditions reaches
        // the entry block.
        //
        // This was emitted as `(assert (forall (..) (and (m_b0 ..) ranges)))`
        // -- a bare conjunction with the predicate inside it, which is not a
        // Horn rule. Z3 rewrites such an assertion into a rule with a
        // *negative* predicate and then refuses the entire query:
        //
        //     (:reason-unknown "Rule contains negative predicate <null>:
        //      P!!1(#0) :- not m1_b0(#0).")
        //
        // So every program with a resolvable callee produced one malformed
        // clause per method and the whole file came back `unknown` -- the
        // second time a well-formedness bug has been masquerading as solver
        // weakness in this encoder, after the free constants. The side
        // conditions belong in the antecedent, where they constrain the entry
        // state instead of being asserted as global truths.
        let entry_body = {
            let full = block_app_src(body.entry.0);
            let app = app_of(&mid, body.entry.0, &{
                live_at(mk, body.entry.0)
                    .iter()
                    .map(|i| src_vars[*i].clone())
                    .collect::<Vec<_>>()
                    .join(" ")
            });
            if full == app {
                app
            } else {
                // `block_app_src` returns `(and <app> <conds>..)`; the
                // antecedent is everything except the application.
                let inner = full
                    .strip_prefix("(and ")
                    .and_then(|t| t.strip_suffix(')'))
                    .unwrap_or_default()
                    .replacen(&app, "", 1);
                let conds = inner.trim();
                if conds.is_empty() {
                    app
                } else {
                    format!("(=> (and {}) {})", conds, app)
                }
            }
        };
        out.push_str(&format!(
            "; === {} ===\n(assert (forall ({}) {}))\n",
            mk, forall_src, entry_body
        ));

        for block in &body.blocks {
            let mut fresh = FreshGen::new();
            let mut constraints: Vec<String> = Vec::new();
            // Overflow conditions from this block's arithmetic; any one of them
            // makes `error` reachable.
            let mut overflow: Vec<String> = Vec::new();
            // `(= name expr)` for each named intermediate value.
            let mut bindings: Vec<String> = Vec::new();
            let is_wide = |op: &Operand| -> bool {
                match op {
                    Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => true,
                    Operand::Var(v) => body
                        .vars
                        .get(v.0 as usize)
                        .map(|vi| vi.ty.is_wide())
                        .unwrap_or(false),
                    _ => false,
                }
            };
            let is_float = |op: &Operand| -> bool {
                match op {
                    Operand::Const(Const::Float(_)) | Operand::Const(Const::Double(_)) => true,
                    Operand::Var(v) => body
                        .vars
                        .get(v.0 as usize)
                        .is_some_and(|vi| matches!(vi.ty, Ty::Float | Ty::Double)),
                    _ => false,
                }
            };
            let mut var_map: HashMap<usize, String> = HashMap::new();
            let mut call_constraints: Vec<String> = Vec::new();

            for i in 0..total_slots {
                var_map.insert(i, format!("v{}", i));
            }

            for stmt in &block.stmts {
                match stmt {
                    Stmt::Assign(vid, rv) => {
                        // Assigning a reference invalidates its ghost length.
                        //
                        // This default runs *before* the arms below, which
                        // override it where they know better -- `NewArray`
                        // records the creation dimension, a copy carries the
                        // source's length across. Everything else leaves the
                        // length unconstrained, which is the honest answer for
                        // an array we did not see created.
                        //
                        // Getting this wrong is a soundness bug, not a
                        // precision one: without it a variable reassigned from
                        // `new int[10]` to something unknown would keep
                        // reporting 10, and a bounds check against a stale
                        // length is exactly a wrong TRUE.
                        if body
                            .vars
                            .get(vid.0 as usize)
                            .is_some_and(|vi| vi.ty == Ty::Ref)
                        {
                            let g = ghost_of(n_vars, vid.0 as usize);
                            let f = fresh.fresh();
                            // Any array's length is a non-negative `int`
                            // (JLS 10.7), even one we know nothing else about.
                            constraints.push(format!("(>= {} 0)", f));
                            constraints.push(format!("(<= {} {})", f, INT_MAX));
                            var_map.insert(g, f);
                        }
                        // A copy carries the length with it.
                        if let Rvalue::Use(Operand::Var(src)) = rv {
                            if body
                                .vars
                                .get(vid.0 as usize)
                                .is_some_and(|vi| vi.ty == Ty::Ref)
                            {
                                let sg = ghost_of(n_vars, src.0 as usize);
                                if let Some(sv) = var_map.get(&sg).cloned() {
                                    log::debug!(
                                        "chc-ghost: copy v{} <- v{} ({})",
                                        vid.0,
                                        src.0,
                                        sv
                                    );
                                    var_map.insert(ghost_of(n_vars, vid.0 as usize), sv);
                                }
                            }
                        }
                        match rv {
                            Rvalue::Call { target, args, .. } => {
                                let callee_ret_ch = return_type_char(&target.desc);
                                if let Some(callee_mid) = method_ids.get(target) {
                                    if callee_ret_ch != 'V' {
                                        let callee_params =
                                            method_params.get(target).cloned().unwrap_or_default();
                                        let mut call_args: Vec<String> = Vec::new();
                                        for (i, arg) in args.iter().enumerate() {
                                            if i < callee_params.len() {
                                                call_args.push(lia_operand(arg, &var_map));
                                            }
                                        }
                                        while call_args.len() < callee_params.len() {
                                            call_args.push("0".to_string());
                                        }

                                        let ret_var = fresh.fresh();
                                        call_args.push(ret_var.clone());
                                        call_constraints.push(format!(
                                            "({}_s {})",
                                            callee_mid,
                                            call_args.join(" ")
                                        ));
                                        var_map.insert(vid.0 as usize, ret_var);
                                    }
                                } else {
                                    if callee_ret_ch != 'V' {
                                        let v = fresh.fresh();
                                        var_map.insert(vid.0 as usize, v);
                                    }
                                }
                            }
                            // Allocation yields a non-null reference.
                            //
                            // JLS 15.9.4: evaluating a class instance creation
                            // expression either completes abruptly or produces a
                            // reference to a *new* object. It is never null.
                            // Likewise JLS 15.10.2 for array creation.
                            //
                            // Without this the reference is unconstrained, so the
                            // solver may take it to be 0, and any space invariant
                            // it flows into admits null. `aastore_aaload1` fills an
                            // array with `new A()` and asserts every element is
                            // non-null: unprovable until allocation says so.
                            //
                            // The lifter represents null as 0, so "non-null" is
                            // `> 0`. Asserting a fact the JVM guarantees narrows no
                            // reachable behaviour, so this cannot hide a violation.
                            Rvalue::New(_) | Rvalue::NewArray { .. } => {
                                let r = fresh.fresh();
                                constraints.push(format!("(> {} 0)", r));
                                if let Rvalue::NewArray { len, .. } = rv {
                                    // JLS 15.10.1: a negative dimension throws
                                    // `NegativeArraySizeException`, so a *created*
                                    // array has a non-negative length.
                                    let l = lia_operand(len, &var_map);
                                    constraints.push(format!("(>= {} 0)", l));
                                    // JLS 10.7: `length` *is* the creation
                                    // dimension, and it is final. Record it in the
                                    // reference's ghost slot, where every later
                                    // block can still read it.
                                    var_map.insert(ghost_of(n_vars, vid.0 as usize), l.clone());
                                }
                                var_map.insert(vid.0 as usize, r);
                            }
                            // GHOST LENGTHS.
                            //
                            // `array.length` reads the reference's ghost slot as a
                            // *term*. It assumes nothing, which is the whole point.
                            //
                            // This replaces a `phi_len(ref, len)` predicate, and
                            // the difference is a soundness one rather than a
                            // matter of taste. An uninterpreted predicate in a
                            // clause *body* is chosen by the solver, and it may
                            // choose one that is empty -- then `assume phi_len(a,
                            // v)` is unsatisfiable, the read path dies, the
                            // obligation becomes unreachable and the program is
                            // declared safe. That is the vacuity `heap_is_closed`
                            // exists to prevent, and it is why the whole space
                            // invariant is gated on a closure condition that holds
                            // for 28 of 169 tasks.
                            //
                            // An uninterpreted *function* `arrlen : Int -> Int`
                            // has exactly the same defect: the solver picks its
                            // interpretation too, and `arrlen = \_. 0` falsifies
                            // every `(= v (arrlen a))` assumption.
                            //
                            // A ghost variable has neither problem. It is ordinary
                            // universally quantified state, threaded across edges
                            // like any other variable, so nothing the solver
                            // chooses can make a read infeasible. It needs no
                            // closure condition, and an array we never saw created
                            // simply has an unconstrained length -- the correct
                            // over-approximation.
                            Rvalue::ArrayLength(Operand::Var(arr)) => {
                                log::debug!("chc-ghost: ArrayLength(v{}) -> ghost", arr.0);
                                let g = ghost_of(n_vars, arr.0 as usize);
                                let v = var_map
                                    .get(&g)
                                    .cloned()
                                    .unwrap_or_else(|| format!("v{}", g));
                                var_map.insert(vid.0 as usize, v);
                            }
                            // Heap reads: a fresh value constrained by the space
                            // invariant, rather than an unconstrained one.
                            _ => {
                                let expr = lia_rvalue(
                                    rv,
                                    &var_map,
                                    &mut fresh,
                                    &is_wide,
                                    &is_float,
                                    &mut overflow,
                                    &theory,
                                );
                                fresh.note(&expr);
                                // Name the value instead of substituting its text.
                                //
                                // `var_map` used to hold the *expression* for each
                                // variable, so `x = a + b; y = x * x;` became
                                // `(* (+ a b) (+ a b))` and a chain of assignments
                                // duplicated whole subtrees. Fibonacci encoded to
                                // 24 KB and Ackermann to 48 KB, which is a formula
                                // shaped by textual sharing rather than by the
                                // program. Binding makes it linear in statements.
                                let expr = if is_atom(&expr) {
                                    expr
                                } else {
                                    let name = fresh.fresh();
                                    bindings.push(format!("(= {} {})", name, expr));
                                    name
                                };
                                var_map.insert(vid.0 as usize, expr);
                            }
                        }
                    }
                    Stmt::Assume(op) => {
                        let expr = lia_operand(op, &var_map);
                        constraints.push(format!("(not (= {} 0))", expr));
                    }
                    // Heap writes: the space invariant must admit the stored
                    // value, which is what forces the solver to make it strong
                    // enough to be useful at the matching reads.
                    Stmt::Check(oid)
                        if obligations.iter().any(|o| o.method == *mk && o.id == *oid) =>
                    {
                        let ob = body.obligation(*oid);
                        let cond_expr = lia_operand(&ob.cond, &var_map);
                        let mut conds = constraints.clone();
                        // The definitions of every named intermediate value.
                        //
                        // `var_map` holds a *name* per variable and `bindings`
                        // holds the `(= name expr)` that defines it. This
                        // clause omitted them, so the obligation's condition
                        // -- and the whole chain it is computed from -- was
                        // unconstrained in the one clause that decides whether
                        // the obligation is violated.
                        //
                        // `(= cond 0)` was therefore satisfiable for *any*
                        // obligation whose condition is a named value, which
                        // is all of the interesting ones: an array bounds
                        // check is `idx >= 0 & idx < len`, three names deep.
                        // `error` was reachable in every such program and the
                        // query came back `unsat` -- read as "the encoding
                        // admits a spurious counterexample", which it did, but
                        // for this reason rather than an imprecise heap.
                        //
                        // Every other clause built in this function extends
                        // with `bindings`; this one did not, and that seam is
                        // the whole defect.
                        conds.extend(bindings.iter().cloned());
                        conds.extend(call_constraints.iter().cloned());
                        conds.push(format!("(= {} 0)", cond_expr));
                        conds.push(block_app_src(block.id.0));

                        let body_expr = and_expr(&conds);
                        let q = add_extra_forall_lia(&forall_src, &fresh);
                        let head_s = "error".to_string();
                        let q = tighten_forall(&q, &body_expr, &head_s);
                        out.push_str(&clause(&q, &body_expr, &head_s));

                        // Past the assertion, its condition holds: the failing
                        // case has already been routed to `error`.
                        constraints.push(format!("(not (= {} 0))", cond_expr));
                    }
                    // Every other `Check` constrains the normal path.
                    //
                    // A `Check` is the lifter's record of a condition the JVM
                    // tests before continuing -- a null receiver, an array
                    // index, a division by zero. If it fails, execution does
                    // *not* proceed to the next statement; it takes the
                    // exceptional edge. So the continuation may assume it.
                    //
                    // These were ignored entirely, and that is what made
                    // unreachable code look reachable. `jbmc-regression/
                    // synchronized` is three lines of it:
                    //
                    //     final Object o = null;
                    //     try { synchronized (o) {} assert false; }
                    //     catch (NullPointerException e) { return; }
                    //
                    // `monitorenter` on null throws (JVMS 6.5), so the assert
                    // is dead. Without the assumption the encoding walks
                    // straight past the check into the assert, derives `error`,
                    // and the task is unprovable -- which is exactly the
                    // spurious counterexample Eldarica reported as `unsat`
                    // where Spacer only said `unknown`.
                    //
                    // Exact rather than approximate: the failing case is not
                    // discarded, it is reachable through the exceptional edge
                    // this encoding already emits.
                    // A failing check throws, so the *normal* successor is
                    // only taken when the condition holds -- assuming it here
                    // cuts spurious paths.
                    //
                    // Sound only in the entry method. This encoding is
                    // relational: a callee becomes a summary `m_s(args, ret)`,
                    // and a call site is an application of it. An assumption
                    // made inside a callee therefore does not constrain a
                    // path, it narrows the summary's *domain* -- it becomes an
                    // unstated preconditon. Every call site that cannot
                    // establish it then has an unsatisfiable application, so
                    // the successor of the call silently disappears and
                    // everything downstream is vacuously safe.
                    //
                    // Measured on `objects/objects14`: assuming a NullDeref
                    // inside a callee gave the summary the precondition
                    // `receiver != 0`, while the caller's inferred invariant
                    // had `v1 = 0`. The edge out of the call died, `main`'s
                    // blocks b3..b11 became empty, and a reachable
                    // `assert false` was proved TRUE (-16).
                    //
                    // The entry method has no caller and no summary, so the
                    // assumption constrains a path there and nothing else.
                    Stmt::Check(oid) if *mk == *entry => {
                        let ob = body.obligation(*oid);
                        let cond_expr = lia_operand(&ob.cond, &var_map);
                        constraints.push(format!("(not (= {} 0))", cond_expr));
                    }
                    // NOTE: the inter-procedural encoder deliberately does
                    // *not* assume a non-query `Check`'s condition here, though
                    // the bitvector encoder does.
                    //
                    // Doing so scored a wrong TRUE (-16) on `objects/objects14`,
                    // whose object comes from `Verifier.nondetObject`. Measured
                    // by isolation: with the assumption the task is proved
                    // TRUE, without it the task is UNKNOWN and nothing else
                    // regresses. The exact interaction is not yet understood --
                    // the LIA path carries havoc-derived values, seeded
                    // interval invariants and summary applications through the
                    // same `constraints` list, and one of those combinations
                    // makes the assumption exclude a reachable state.
                    //
                    // Left out until that is explained. An unexplained
                    // soundness win is a wrong answer waiting for a different
                    // benchmark.
                    _ => {}
                }
            }

            // Any overflow on a reachable path makes `error` reachable, so
            // proving `error` unreachable proves the program does not overflow
            // *and* satisfies its obligations. On an overflow-free path LIA and
            // Java's wrapping arithmetic agree, which is what makes the whole
            // encoding sound (#77).
            if !overflow.is_empty() {
                let mut conds = constraints.clone();
                conds.extend(bindings.iter().cloned());
                // Deliberately *not* `call_constraints`.
                //
                // An overflow happens while evaluating an argument, before the
                // call it feeds. Requiring the callee's summary to hold as
                // well makes the guard unsatisfiable exactly when it matters:
                // in `addition(m + 1, n - 1)` the guard's body contained
                // `(m1_s (+ v2 1) (- v0 1) _f2)` alongside the condition
                // `(+ v2 1) > INT_MAX`, and the summary is only ever
                // established for in-range arguments. So the one state that
                // should reach `error` was the one state the summary could not
                // describe, the guard never fired, and
                // `jayhorn-recursive/UnsatAddition02` -- whose FALSE depends
                // entirely on `m + n` wrapping -- was proved TRUE.
                //
                // Dropping them is sound in the safe direction: without the
                // summary the call's result is an unconstrained value, so
                // `error` becomes *more* reachable, never less.
                conds.push(if overflow.len() == 1 {
                    overflow[0].clone()
                } else {
                    format!("(or {})", overflow.join(" "))
                });
                conds.push(block_app_src(block.id.0));
                let body_expr = and_expr(&conds);
                let q = add_extra_forall_lia(&forall_src, &fresh);
                out.push_str(&format!(
                    "; overflow guard for {} bb{}\n(assert (forall ({}) (=> {} error)))\n",
                    mk, block.id.0, q, body_expr
                ));
            }

            let mut assign_conds: Vec<String> = Vec::new();
            for i in 0..total_slots {
                let val = var_map
                    .get(&i)
                    .cloned()
                    .unwrap_or_else(|| format!("v{}", i));
                let dst = format!("w{}", i);
                if val != dst {
                    assign_conds.push(format!("(= {} {})", dst, val));
                }
            }

            let forall_both: String = src_vars
                .iter()
                .chain(dst_vars.iter())
                .map(|v| format!("({} Int)", v))
                .collect::<Vec<_>>()
                .join(" ");

            let mk_trans = |target_bid: u32, extra: &[String], out: &mut String| {
                let mut all = constraints.clone();
                all.extend(bindings.iter().cloned());
                all.extend(call_constraints.iter().cloned());
                all.extend_from_slice(extra);
                all.extend(assign_conds.iter().cloned());
                all.push(block_app_src(block.id.0));

                let body_expr = and_expr(&all);
                let q = add_extra_forall_lia(&forall_both, &fresh);
                let body_s = body_expr;
                let head_s = block_app_dst(target_bid);
                let q = tighten_forall(&q, &body_s, &head_s);
                out.push_str(&clause(&q, &body_s, &head_s));
            };

            // Facts about objects created in this block. Like heap writes,
            // these are conclusions rather than assumptions: reaching the
            // block establishes them.

            // Exceptional edges, so that an obligation inside a `catch` is
            // reachable in the encoding.
            //
            // Previously this encoding followed normal control flow only, so a
            // handler was unreachable, its obligations were never examined,
            // and the program was declared safe -- a wrong TRUE, which
            // `argv-tasks/HttpTransport_false` scored. The engine then
            // *declined* every program with a handler, which is correct but
            // cost it 157 of 580 records in the 2026-09-06 survey: by far its
            // biggest limitation.
            //
            // JayHorn's answer is to remove exceptional flow before encoding
            // (methods return a value/exception pair and callers branch on
            // it). The same effect, expressed directly in the clauses: the
            // handler is reachable from *anywhere* in the guarded block.
            //
            // Soundness. A throw can occur at any point in the block, so the
            // real program reaches the handler in some state we cannot pin
            // down. This clause allows the handler to be entered from the
            // block's entry state with locals preserved -- JVMS 2.6.1, the
            // frame's local variables survive -- and the operand stack free,
            // since it is discarded and replaced by the exception object. The
            // set of handler states we admit is therefore a *superset* of the
            // reachable ones, which is the safe direction for an engine that
            // may only discharge: proving the obligation over more states
            // proves it over fewer.
            //
            // The block's own assignments are deliberately *not* included. The
            // throw may precede any of them.
            for edge in &block.exceptional {
                let mut all = vec![block_app_src(block.id.0)];
                for (i, vi) in body.vars.iter().enumerate() {
                    if matches!(vi.kind, VarKind::Local(_)) {
                        all.push(format!("(= w{} v{})", i, i));
                    }
                }
                let body_expr = and_expr(&all);
                let q = add_extra_forall_lia(&forall_both, &fresh);
                let body_s = body_expr;
                let head_s = block_app_dst(edge.target.0);
                let q = tighten_forall(&q, &body_s, &head_s);
                out.push_str(&clause(&q, &body_s, &head_s));
            }

            match &block.term {
                Terminator::Goto(t) => {
                    mk_trans(t.0, &[], &mut out);
                }
                Terminator::Branch { cond, then_, else_ } => {
                    let ce = lia_operand(cond, &var_map);
                    let nz = format!("(not (= {} 0))", ce);
                    let z = format!("(= {} 0)", ce);
                    mk_trans(then_.0, &[nz], &mut out);
                    mk_trans(else_.0, &[z], &mut out);
                }
                Terminator::Switch {
                    value,
                    cases,
                    default,
                } => {
                    let ve = lia_operand(value, &var_map);
                    let mut neg = Vec::new();
                    for (cv, target) in cases {
                        let cv_s = lia_int(*cv);
                        let eq = format!("(= {} {})", ve, cv_s);
                        mk_trans(target.0, std::slice::from_ref(&eq), &mut out);
                        neg.push(format!("(not {})", eq));
                    }
                    mk_trans(default.0, &neg, &mut out);
                }
                Terminator::Return(Some(op)) if ret_ch != 'V' => {
                    let ret_expr = lia_operand(op, &var_map);
                    let mut summary_args: Vec<String> = param_indices
                        .iter()
                        .map(|&pi| {
                            var_map
                                .get(&pi)
                                .cloned()
                                .unwrap_or_else(|| format!("v{}", pi))
                        })
                        .collect();
                    summary_args.push(ret_expr);

                    let mut all = constraints.clone();
                    // The binding equalities, without which the returned value
                    // is a free variable.
                    //
                    // `bind` names each computed value `_fN` and records
                    // `(= _fN expr)` here; every other clause kind already
                    // conjoins them and this one did not, so
                    // `return fib(n-1) + fib(n-2)` produced
                    // `(=> (m1_b6 ...) (m1_s v0 _f0))` with `_f0` unconstrained
                    // -- fibonacci returning an arbitrary integer. The base
                    // cases returned literals and so looked fine, which is why
                    // the encoding still passed every structural check.
                    //
                    // Over-approximating, so it cost precision rather than
                    // soundness: with the summary free, no property of a return
                    // value is provable, and CHC could not discharge anything
                    // recursive at all.
                    all.extend(bindings.iter().cloned());
                    all.extend(call_constraints.iter().cloned());
                    all.push(block_app_src(block.id.0));

                    let body_expr = and_expr(&all);
                    let q = add_extra_forall_lia(&forall_src, &fresh);
                    out.push_str(&format!(
                        "(assert (forall ({}) (=> {} ({}_s {}))))\n",
                        q,
                        body_expr,
                        mid,
                        summary_args.join(" ")
                    ));
                }
                _ => {}
            }
        }
        out.push('\n');
    }

    out.push_str("(assert (not error))\n");
    out.push_str("(check-sat)\n");

    out
}

fn and_expr(conds: &[String]) -> String {
    match conds.len() {
        0 => "true".to_string(),
        1 => conds[0].clone(),
        _ => format!("(and {})", conds.join(" ")),
    }
}

fn add_extra_forall_lia(base: &str, fresh: &FreshGen) -> String {
    if fresh.extra_forall.is_empty() {
        base.to_string()
    } else {
        format!("{} {}", base, fresh.forall_str())
    }
}

/// Keep only the binders the clause actually mentions.
///
/// Every clause used to quantify over *all* source and destination variables
/// of the method whether or not it referred to them. Measured on
/// `algorithms/BellmanFord-FunSat01`: **234 binders per clause**, 120 clauses,
/// 312 KB of text, and Spacer returned `unknown` in 90ms -- it gave up rather
/// than worked. For comparison `aastore_aaload1` is 39 KB and solves in 0.03s.
///
/// An unused binder is logically harmless -- the clause means exactly the same
/// thing -- but it is not free: the solver carries every quantified variable
/// through its reasoning about the clause.
///
/// Matching is on whole tokens. `v1` must not match inside `v10`, so a binder
/// is kept only when its name appears bounded by a non-identifier character.
/// Wrap a clause in `forall` only when there is something to quantify.
///
/// SMT-LIB rejects `(forall () ...)` -- "invalid quantifier, list of sorted
/// variables is empty" -- and the error aborts the *whole file*, so one such
/// clause silently costs every proof in it. That is what tightening the binder
/// lists introduced: once unused binders are dropped, a clause over only
/// constants has none left.
/// Quantify fresh values inside the clauses that use them.
///
/// Takes the finished text and, for each `(assert (forall (BINDERS) BODY))`,
/// adds a binder for every fresh name the clause mentions. A clause with no
/// binders at all gains a `forall`; `drop_empty_quantifiers` then has nothing
/// to remove from it.
fn bind_free_constants(smt2: &str, fresh: &[(String, u32)]) -> String {
    if fresh.is_empty() {
        return smt2.to_string();
    }
    smt2.lines()
        .map(|line| {
            if !line.starts_with("(assert ") {
                return line.to_string();
            }
            let used: Vec<String> = fresh
                .iter()
                .filter(|(n, _)| mentions(line, n))
                .map(|(n, w)| format!("({} (_ BitVec {}))", n, w))
                .collect();
            if used.is_empty() {
                return line.to_string();
            }
            let extra = used.join(" ");
            match line.find("(forall (") {
                // Splice into the existing binder list.
                Some(at) => {
                    let open = at + "(forall (".len();
                    format!("{}{} {}", &line[..open], extra, &line[open..])
                }
                // No quantifier yet: wrap the whole assertion in one.
                None => {
                    let inner = line.trim_start_matches("(assert ").trim_end_matches(')');
                    format!("(assert (forall ({}) {}))", extra, inner)
                }
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Remove degenerate `(forall () ...)` wrappers from a finished encoding.
///
/// SMT-LIB rejects an empty binder list, and the error aborts the **whole
/// file** -- so a single such clause silently costs every proof in it. They
/// appear wherever a method has no live variables at a program point, which
/// MinePump has several of, and they became common once binder lists were
/// tightened to the variables a clause actually mentions.
///
/// Done as a pass over the finished text rather than at each of the ten
/// emission sites, so a site added later cannot reintroduce it.
fn drop_empty_quantifiers(smt2: &str) -> String {
    smt2.replace("(forall () ", "(__NOQ__ ")
        .lines()
        .map(|l| {
            if !l.contains("(__NOQ__ ") {
                return l.to_string();
            }
            // `(assert (__NOQ__ X))` is just `(assert X)`: drop the wrapper
            // and the parenthesis it opened.
            let unwrapped = l.replace("(__NOQ__ ", "");
            match unwrapped.strip_suffix("))") {
                Some(rest) => format!("{rest})"),
                None => unwrapped,
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn clause(binders: &str, body: &str, head: &str) -> String {
    if binders.trim().is_empty() {
        format!("(assert (=> {} {}))\n", body, head)
    } else {
        format!("(assert (forall ({}) (=> {} {})))\n", binders, body, head)
    }
}

fn tighten_forall(binders: &str, clause_body: &str, clause_head: &str) -> String {
    let mut kept = Vec::new();
    for decl in binders.split(") (") {
        let name = decl
            .trim_start_matches('(')
            .split_whitespace()
            .next()
            .unwrap_or("");
        if name.is_empty() {
            continue;
        }
        if mentions(clause_body, name) || mentions(clause_head, name) {
            kept.push(format!("({} Int)", name));
        }
    }
    kept.join(" ")
}

/// Does `text` contain `name` as a whole token?
fn mentions(text: &str, name: &str) -> bool {
    let bytes = text.as_bytes();
    let mut from = 0;
    while let Some(rel) = text[from..].find(name) {
        let at = from + rel;
        let before_ok = at == 0 || !is_ident_byte(bytes[at - 1]);
        let after = at + name.len();
        let after_ok = after >= bytes.len() || !is_ident_byte(bytes[after]);
        if before_ok && after_ok {
            return true;
        }
        from = at + 1;
    }
    false
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

// ---------------------------------------------------------------------------
// Single-method BV encoding (original, for non-recursive programs)
// ---------------------------------------------------------------------------

fn width_of(ty: &Ty) -> u32 {
    match ty {
        Ty::Long | Ty::Double => 64,
        _ => 32,
    }
}

fn encode_chc_single(body: &Body, obligations: &[ObligationId]) -> String {
    use crate::smt_text::{self, BitvectorTheory, SmtTheory};

    let mut out = String::new();
    out.push_str("(set-logic HORN)\n");

    let mut var_widths: Vec<(usize, u32)> = body
        .vars
        .iter()
        .enumerate()
        .map(|(i, vi)| (i, width_of(&vi.ty)))
        .collect();
    let width_map: HashMap<usize, u32> = var_widths.iter().cloned().collect();
    let mut fresh_decls: Vec<(String, u32)> = Vec::new();
    let n_vars = var_widths.len();

    // GHOST LENGTHS, in the bitvector encoder too.
    //
    // Same mechanism and same reasons as the inter-procedural encoder: a
    // shadow integer per reference whose length is read, so `a.length` is a
    // term rather than an unconstrained value.
    //
    // This has to be written twice because these are two separate encoders,
    // and leaving it out of this one is what kept `jbmc-regression/array1`
    // unprovable after the other was fixed. The bitvector path is selected
    // when nothing resolvable is called -- which is the *common* case for the
    // small array benchmarks, so the gap covered most of what the work was
    // supposed to fix.
    let mut ghost_want: BTreeSet<usize> = BTreeSet::new();
    for blk in &body.blocks {
        for st in &blk.stmts {
            if let Stmt::Assign(_, Rvalue::ArrayLength(Operand::Var(v))) = st {
                ghost_want.insert(v.0 as usize);
            }
        }
    }
    loop {
        let before = ghost_want.len();
        for blk in &body.blocks {
            for st in &blk.stmts {
                if let Stmt::Assign(d, Rvalue::Use(Operand::Var(src))) = st {
                    if ghost_want.contains(&(d.0 as usize)) {
                        ghost_want.insert(src.0 as usize);
                    }
                }
            }
        }
        if ghost_want.len() == before {
            break;
        }
    }
    let ghost_want: Vec<usize> = ghost_want
        .into_iter()
        .filter(|i| body.vars.get(*i).is_some_and(|vi| vi.ty == Ty::Ref))
        .collect();
    let ghost_of = |i: usize| -> usize { n_vars + i };
    for i in &ghost_want {
        var_widths.push((ghost_of(*i), 32));
    }
    let var_indices = &var_widths;

    for block in &body.blocks {
        let sig: String = var_indices
            .iter()
            .map(|(_, w)| format!("(_ BitVec {})", w))
            .collect::<Vec<_>>()
            .join(" ");
        out.push_str(&format!(
            "(declare-fun block_{} ({}) Bool)\n",
            block.id.0, sig
        ));
    }
    out.push_str("(declare-fun error () Bool)\n");

    let src_vars: Vec<String> = var_indices.iter().map(|(i, _)| format!("v{}", i)).collect();
    let dst_vars: Vec<String> = var_indices
        .iter()
        .map(|(i, _)| format!("v{}p", i))
        .collect();

    // Binder names come from the *slot id*, not the position. Ghost slots are
    // appended at `n_vars + var`, so those two stopped agreeing the moment the
    // slot space grew past the program's own variables.
    let forall_src: String = var_indices
        .iter()
        .map(|(i, w)| format!("(v{} (_ BitVec {}))", i, w))
        .collect::<Vec<_>>()
        .join(" ");
    let forall_both: String = {
        let src = var_indices
            .iter()
            .map(|(i, w)| format!("(v{} (_ BitVec {}))", i, w));
        let dst = var_indices
            .iter()
            .map(|(i, w)| format!("(v{}p (_ BitVec {}))", i, w));
        src.chain(dst).collect::<Vec<_>>().join(" ")
    };

    let block_app = |bid: u32| -> String {
        let args = src_vars.join(" ");
        format!("(block_{} {})", bid, args)
    };
    let block_app_dst = |bid: u32| -> String {
        let args = dst_vars.join(" ");
        format!("(block_{} {})", bid, args)
    };

    out.push_str(&format!(
        "(assert (forall ({}) {}))\n",
        forall_src,
        block_app(body.entry.0)
    ));

    for block in &body.blocks {
        let mut constraints: Vec<String> = Vec::new();
        let mut var_map: HashMap<usize, String> = HashMap::new();

        for (i, _) in var_indices.iter() {
            var_map.insert(*i, format!("v{}", i));
        }
        let mut enc = smt_text::Encoder::new(&BitvectorTheory, "bvf_");
        let is_wide = |op: &Operand| -> bool {
            match op {
                Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => true,
                Operand::Var(v) => body
                    .vars
                    .get(v.0 as usize)
                    .map(|vi| vi.ty.is_wide())
                    .unwrap_or(false),
                _ => false,
            }
        };

        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(vid, rv) => {
                    // Ghost length maintenance, mirroring the LIA encoder.
                    //
                    // Assigning a reference invalidates its shadow; `NewArray`
                    // then records the creation dimension (JLS 10.7) and a
                    // copy carries the source's across. A stale length is a
                    // wrong bounds proof, so the invalidation is the part that
                    // has to be right.
                    if body
                        .vars
                        .get(vid.0 as usize)
                        .is_some_and(|vi| vi.ty == Ty::Ref)
                        && ghost_want.contains(&(vid.0 as usize))
                    {
                        let g = ghost_of(vid.0 as usize);
                        match rv {
                            Rvalue::NewArray { len, .. } => {
                                let l = smt_text::encode_operand(&BitvectorTheory, len, &var_map);
                                var_map.insert(g, l);
                            }
                            Rvalue::Use(Operand::Var(src))
                                if ghost_want.contains(&(src.0 as usize)) =>
                            {
                                let sg = ghost_of(src.0 as usize);
                                if let Some(sv) = var_map.get(&sg).cloned() {
                                    var_map.insert(g, sv);
                                }
                            }
                            _ => {
                                let f = format!("bvg_{}_{}", block.id.0, g);
                                if !fresh_decls.iter().any(|(n, _)| n == &f) {
                                    fresh_decls.push((f.clone(), 32));
                                }
                                var_map.insert(g, f);
                            }
                        }
                    }
                    // `array.length` reads the shadow as a term.
                    if let Rvalue::ArrayLength(Operand::Var(arr)) = rv {
                        if ghost_want.contains(&(arr.0 as usize)) {
                            let g = ghost_of(arr.0 as usize);
                            let v = var_map
                                .get(&g)
                                .cloned()
                                .unwrap_or_else(|| format!("v{}", g));
                            var_map.insert(vid.0 as usize, v);
                            continue;
                        }
                    }
                    // The encoder reports its own binders, so the old
                    // recover-by-string-prefix on "bv_fresh" is gone.
                    let expr = enc.rvalue(rv, &var_map, &is_wide);
                    for (name, _) in enc.binders.drain(..) {
                        let w = width_map.get(&(vid.0 as usize)).copied().unwrap_or(32);
                        if !fresh_decls.iter().any(|(n, _)| n == &name) {
                            fresh_decls.push((name, w));
                        }
                    }
                    var_map.insert(vid.0 as usize, expr);
                }
                Stmt::Assume(op) => {
                    let expr = smt_text::encode_operand(&BitvectorTheory, op, &var_map);
                    constraints.push(BitvectorTheory.encode_nonzero(&expr));
                }
                Stmt::Check(oid) if obligations.contains(oid) => {
                    let ob = body.obligation(*oid);
                    let cond_expr = smt_text::encode_operand(&BitvectorTheory, &ob.cond, &var_map);
                    let mut error_conds = constraints.clone();
                    error_conds.push(BitvectorTheory.encode_is_zero(&cond_expr));
                    error_conds.push(block_app(block.id.0));

                    let body_expr = if error_conds.len() == 1 {
                        error_conds[0].clone()
                    } else {
                        format!("(and {})", error_conds.join(" "))
                    };

                    out.push_str(&format!(
                        "(assert (forall ({}) (=> {} error)))\n",
                        forall_src, body_expr
                    ));

                    // Past the assertion its condition holds; the failing case
                    // is already routed to `error`.
                    constraints.push(BitvectorTheory.encode_nonzero(&cond_expr));
                }
                // Every other `Check` constrains the normal path.
                //
                // The same fix as in the inter-procedural encoder, and it has
                // to be made twice because these are two separate encoders --
                // small programs with no resolvable calls take this bitvector
                // path, which is why fixing only the LIA one left
                // `jbmc-regression/synchronized` unprovable.
                //
                // A `Check` records a condition the JVM tests before
                // continuing. If it fails, control takes the exceptional edge
                // rather than the next statement, so the continuation may
                // assume it. Exact, not approximate.
                Stmt::Check(oid) => {
                    let ob = body.obligation(*oid);
                    let cond_expr = smt_text::encode_operand(&BitvectorTheory, &ob.cond, &var_map);
                    constraints.push(BitvectorTheory.encode_nonzero(&cond_expr));
                }
                _ => {}
            }
        }

        let mut assign_constraints: Vec<String> = Vec::new();
        // Every slot, not just the program's own variables: the ghost lengths
        // live above `n_vars` and have to cross the edge like anything else,
        // or the length does not survive into the loop body where the bound is
        // actually proved.
        for (i, _) in var_indices.iter() {
            let Some(val) = var_map.get(i) else { continue };
            if *val != format!("v{}p", i) {
                assign_constraints.push(format!("(= v{}p {})", i, val));
            }
        }

        let mk_trans = |target_bid: u32, extra_conds: &[String]| -> String {
            let mut all_conds = constraints.clone();
            all_conds.extend_from_slice(extra_conds);
            all_conds.extend(assign_constraints.iter().cloned());
            all_conds.push(block_app(block.id.0));

            let body_expr = if all_conds.is_empty() {
                block_app(block.id.0)
            } else {
                format!("(and {})", all_conds.join(" "))
            };

            format!(
                "(assert (forall ({}) (=> {} {})))\n",
                forall_both,
                body_expr,
                block_app_dst(target_bid)
            )
        };

        // Exceptional edges, exactly as the inter-procedural encoder emits
        // them -- and for the same reason, which had to be learned twice.
        //
        // Following normal control flow only makes a handler unreachable, so
        // an obligation *inside* a handler is never examined and the program
        // is declared safe. That is a wrong TRUE at -16. The decline that used
        // to guard it was removed once the LIA encoder gained exceptional
        // edges, but this is a second, separate encoder and it did not have
        // them -- so the guard was removed for a path that still needed it.
        // `ArrayIndexOutOfBoundsException1..3` and `ClassCastException1` all
        // assert inside a `catch` and were all proved TRUE.
        //
        // Soundness is the same argument as the LIA case: a throw may occur
        // anywhere in the block, so the handler is entered from the block's
        // *entry* state with locals preserved (JVMS 2.6.1) and the operand
        // stack free. The block's own assignments are deliberately excluded,
        // since the throw may precede any of them. That admits a superset of
        // the real handler states, which is the safe direction for an engine
        // that may only discharge.
        for edge in &block.exceptional {
            let mut all = vec![block_app(block.id.0)];
            for (i, vi) in body.vars.iter().enumerate() {
                if matches!(vi.kind, VarKind::Local(_)) {
                    all.push(format!("(= v{}p v{})", i, i));
                }
            }
            out.push_str(&format!(
                "(assert (forall ({}) (=> (and {}) {})))\n",
                forall_both,
                all.join(" "),
                block_app_dst(edge.target.0)
            ));
        }

        match &block.term {
            Terminator::Goto(t) => {
                out.push_str(&mk_trans(t.0, &[]));
            }
            Terminator::Branch { cond, then_, else_ } => {
                let cond_expr = smt_text::encode_operand(&BitvectorTheory, cond, &var_map);
                let nz = BitvectorTheory.encode_nonzero(&cond_expr);
                let z = BitvectorTheory.encode_is_zero(&cond_expr);
                out.push_str(&mk_trans(then_.0, &[nz]));
                out.push_str(&mk_trans(else_.0, &[z]));
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let val_expr = smt_text::encode_operand(&BitvectorTheory, value, &var_map);
                let mut neg_cases = Vec::new();
                for (cv, target) in cases {
                    let cv_encoded = BitvectorTheory.encode_int(*cv);
                    let eq = format!("(= {} {})", val_expr, cv_encoded);
                    out.push_str(&mk_trans(target.0, std::slice::from_ref(&eq)));
                    neg_cases.push(format!("(not {})", eq));
                }
                out.push_str(&mk_trans(default.0, &neg_cases));
            }
            _ => {}
        }
    }

    // Bind fresh values inside each clause instead of declaring them globally.
    //
    // They used to be emitted as `(declare-fun bvf_f0 () (_ BitVec 32))`, and
    // that is not a Horn clause: every variable in a rule must be universally
    // quantified. Both solvers refuse it, in their own words --
    //
    //   z3:       (:reason-unknown "Uninterpreted 'bvf_f0' in <null>: ...")
    //   Eldarica: "Uninterpreted functions or constants in clauses are not
    //              supported"
    //
    // -- and z3's refusal surfaces as a bare `unknown`, which reads as "could
    // not find an invariant" rather than "would not look". That is why this
    // survived: the engine appeared merely weak. It was rejected outright.
    //
    // The global form is also the wrong semantics. One constant shared across
    // every clause says all havocs in the program yield the *same* unknown
    // value; a per-clause binder says each is independent, which is what a
    // havoc means.
    out = bind_free_constants(&out, &fresh_decls);

    out.push_str("(assert (not error))\n");
    out.push_str("(check-sat)\n");

    out
}

// ---------------------------------------------------------------------------
// Solver interaction
// ---------------------------------------------------------------------------

/// Run the Horn solver and report which obligations it proved safe.
///
/// Takes `ObligationRef`, not `ObligationId`. An id indexes into *one* `Body`,
/// so two methods can each have id 3 -- and since assertions may now live
/// outside the entry method, keying the result by id alone would attribute a
/// discharge to whichever obligation happened to share the number. `CLAUDE.md`
/// records that exact hazard costing 32 points once already.
///
/// A `sat` answer means no obligation in the batch is violated: the encoding
/// routes them all to one `error` predicate, so they are proved together.
/// What Spacer said, as distinct from what we concluded.
///
/// `Unknown` is the arm that matters for scheduling: it is the only outcome a
/// longer query can change, so it is the only one worth resuming for.
/// Collapsing it into "not safe" is what made the engine's timeout constant
/// unfalsifiable — a query that ran out of time and one that proved the error
/// reachable produced the same empty result.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ChcOutcome {
    /// `sat` in CHC mode: the error predicate is unreachable.
    Safe,
    /// `unsat`: the error predicate is derivable. CHC is an Over engine, so
    /// this is not ours to publish as a violation — an over-approximating
    /// counterexample may be spurious.
    Unsafe,
    /// The solver gave up, almost always on `-T`.
    Unknown,
}

fn run_chc_solver(
    binary: &str,
    smt2: &str,
    obligations: &[ObligationRef],
    timeout_secs: u32,
) -> Result<(Vec<(ObligationRef, bool)>, ChcOutcome), String> {
    let mut child = Command::new(binary)
        .args([
            "-in",
            "-smt2",
            // A wall-clock bound on the solver, which had none at all.
            //
            // Nothing exposed that while the heap guard held, because CHC never
            // saw a program hard enough to hang on. It is a latent hazard the
            // guard was hiding, not a consequence of it: any future encoding
            // work makes it reachable immediately.
            &format!("-T:{}", timeout_secs),
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn {}: {}", binary, e))?;

    {
        let stdin = child.stdin.as_mut().ok_or("no stdin")?;
        stdin
            .write_all(smt2.as_bytes())
            .map_err(|e| format!("write failed: {}", e))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("wait failed: {}", e))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let result_line = stdout.trim();

    debug!("chc: solver returned: {}", result_line);
    if !stderr.is_empty() {
        debug!("chc: solver stderr: {}", &stderr[..stderr.len().min(500)]);
    }

    // In CHC mode: `sat` means error is unreachable (safe), `unsat` means reachable (unsafe).
    match result_line {
        "sat" => Ok((
            obligations.iter().map(|o| (o.clone(), true)).collect(),
            ChcOutcome::Safe,
        )),
        "unsat" => Ok((vec![], ChcOutcome::Unsafe)),
        _ => Ok((vec![], ChcOutcome::Unknown)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk(name: &str, desc: &str) -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: name.into(),
            desc: desc.into(),
        }
    }

    fn int_var(slot: u16) -> VarInfo {
        VarInfo {
            kind: VarKind::Local(slot),
            ty: Ty::Int,
        }
    }

    /// ```text
    /// static int inc(int x) { return x + 1; }
    /// static void main()    { int n = nondet(); assert inc(n) > n; }
    /// ```
    ///
    /// `x + 1 > x` is **valid** in linear integer arithmetic and **false** in
    /// Java at `Integer.MAX_VALUE`. The call is what matters: it selects
    /// `encode_chc_interproc`, which used unbounded `Int`.
    fn overflow_program() -> (Program, MethodKey) {
        let inc = mk("inc", "(I)I");
        let main = mk("main", "([Ljava/lang/String;)V");
        let mut prog = Program::default();

        let (x, t) = (VarId(0), VarId(1));
        prog.bodies.insert(
            inc.clone(),
            Body {
                is_static: true,
                key: inc.clone(),
                entry: BlockId(0),
                vars: vec![int_var(0), int_var(1)],
                obligations: vec![],
                blocks: vec![Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![Stmt::Assign(
                        t,
                        Rvalue::Bin(BinOp::Add, Operand::Var(x), Operand::int(1)),
                    )],
                    term: Terminator::Return(Some(Operand::Var(t))),
                    exceptional: vec![],
                }],
            },
        );

        let (n, r, c) = (VarId(0), VarId(1), VarId(2));
        prog.bodies.insert(
            main.clone(),
            Body {
                is_static: true,
                key: main.clone(),
                entry: BlockId(0),
                vars: vec![int_var(0), int_var(1), int_var(2)],
                obligations: vec![Obligation {
                    id: ObligationId(0),
                    kind: ObligationKind::Assertion,
                    cond: Operand::Var(c),
                    bytecode_offset: 0,
                    line: None,
                    guarded: false,
                }],
                blocks: vec![Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![
                        Stmt::Assign(n, Rvalue::Nondet(Ty::Int, None)),
                        Stmt::Assign(
                            r,
                            Rvalue::Call {
                                target: inc.clone(),
                                args: vec![Operand::Var(n)],
                                is_virtual: false,
                            },
                        ),
                        Stmt::Assign(c, Rvalue::Bin(BinOp::Gt, Operand::Var(r), Operand::Var(n))),
                        Stmt::Check(ObligationId(0)),
                    ],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                }],
            },
        );
        prog.entry = Some(main.clone());
        (prog, main)
    }

    pub(super) fn z3_available() -> bool {
        Command::new("which")
            .arg("z3")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }

    /// Both encoders must make an exception handler reachable.
    ///
    /// An encoding that follows normal control flow only leaves a handler
    /// unreachable, so an obligation *inside* the handler is never examined
    /// and the program is declared safe -- a wrong TRUE at -16.
    ///
    /// This has now been paid for twice. `argv-tasks/HttpTransport_false`
    /// bought the decline that used to guard it; when the inter-procedural
    /// encoder gained exceptional edges the decline was removed, but
    /// `encode_chc_single` is a *separate* encoder that did not have them, so
    /// the guard was withdrawn from a path that still needed it.
    /// `ArrayIndexOutOfBoundsException1..3` and `ClassCastException1` -- all of
    /// which assert inside a `catch` -- were then all proved TRUE.
    ///
    /// Hence the assertion over both encoders rather than the one that broke.
    #[test]
    fn both_encoders_make_a_handler_reachable() {
        let main = mk("main", "([Ljava/lang/String;)V");
        let mut prog = Program::default();
        let (n, c) = (VarId(0), VarId(1));
        let handler = BlockId(1);
        let body = Body {
            is_static: true,
            key: main.clone(),
            entry: BlockId(0),
            vars: vec![int_var(0), int_var(1)],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(c),
                bytecode_offset: 0,
                line: None,
                guarded: true,
            }],
            blocks: vec![
                // Guarded block: throws to the handler.
                Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![Stmt::Assign(n, Rvalue::Nondet(Ty::Int, None))],
                    term: Terminator::Return(None),
                    exceptional: vec![ExcEdge {
                        class: None,
                        target: handler,
                    }],
                },
                // The handler, holding `assert false`.
                Block {
                    id: handler,
                    bytecode_offset: 1,
                    stmts: vec![
                        Stmt::Assign(c, Rvalue::Use(Operand::int(0))),
                        Stmt::Check(ObligationId(0)),
                    ],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                },
            ],
        };
        prog.bodies.insert(main.clone(), body.clone());
        prog.entry = Some(main.clone());

        // Mentioning the handler is not enough -- every block gets a
        // `declare-fun` whether or not anything can reach it. What matters is
        // a *clause whose head is the handler*, so this looks for an
        // implication in which the guarded block appears in the body and the
        // handler after it. Asserting mere mention passes with the fix
        // removed, which was checked.
        fn derives_handler(smt2: &str, guarded: &str, handler: &str) -> bool {
            smt2.lines().filter(|l| l.starts_with("(assert")).any(|l| {
                match (l.rfind(guarded), l.rfind(handler)) {
                    (Some(g), Some(h)) => h > g,
                    _ => false,
                }
            })
        }

        let single = encode_chc_single(&body, &[ObligationId(0)]);
        assert!(
            derives_handler(&single, "block_0", "block_1"),
            "bitvector encoder has no clause deriving the handler:\n{single}"
        );

        let obs = [ObligationRef {
            method: main.clone(),
            id: ObligationId(0),
        }];
        let interproc = encode_chc_interproc(&prog, &main, &obs, &HashMap::new());
        assert!(
            derives_handler(&interproc, "m0_b0", "m0_b1"),
            "LIA encoder has no clause deriving the handler:\n{interproc}"
        );
    }

    /// The query clause must define the values its condition is built from.
    ///
    /// `var_map` holds a *name* per variable and `bindings` holds the
    /// `(= name expr)` that defines it. The clause deciding an obligation
    /// omitted `bindings`, so the obligation's condition -- and the whole
    /// chain computing it -- was unconstrained in the one clause that decides
    /// whether the obligation is violated. `(= cond 0)` was satisfiable for
    /// any condition that is a named value, which is all the interesting ones:
    /// an array bounds check is `idx >= 0 & idx < len`, three names deep.
    ///
    /// So `error` was reachable in every such program and the query came back
    /// `unsat`. That was read as "the encoding admits a spurious
    /// counterexample", which it did -- but because of this seam rather than
    /// an imprecise heap, and the mistaken reading is what kept issue #18 open.
    #[test]
    fn the_query_clause_defines_the_values_its_condition_uses() {
        let (prog, main) = overflow_program();
        let obs = [ObligationRef {
            method: main.clone(),
            id: ObligationId(0),
        }];
        let smt2 = encode_chc_interproc(&prog, &main, &obs, &HashMap::new());

        // `main`'s obligation is `c`, defined by `c = inc(n) > n`. The clause
        // whose head is `error` must therefore constrain whatever name `c` is
        // bound to. Counting in the *body* only: the `forall` binder list
        // mentions every variable regardless, so counting the whole clause
        // would pass even with the defect present.
        let err_clause = smt2
            .lines()
            .find(|l| l.starts_with("(assert") && l.trim_end().ends_with("error)))"))
            .expect("an error clause");
        let body = err_clause.split_once("(=> ").expect("an implication").1;
        let cond = body
            .split("(= ")
            .find_map(|seg| {
                let name = seg.split(' ').next()?;
                seg.split_once(" 0)").map(|_| name.to_string())
            })
            .expect("an `(= <cond> 0)` conjunct");
        assert!(
            body.matches(&cond).count() > 1,
            "`{cond}` occurs once in the clause body, so nothing defines it \
             -- `bindings` is missing:\n{err_clause}"
        );
    }

    /// An overflow guard must not depend on the call its value feeds.
    ///
    /// An overflow happens while evaluating an argument, before the call that
    /// consumes it. Conjoining the callee's summary makes the guard
    /// unsatisfiable exactly when it matters: for `addition(m + 1, n - 1)` the
    /// body held `(m1_s (+ v2 1) (- v0 1) _f2)` next to `(+ v2 1) > INT_MAX`,
    /// and a summary is only ever established for in-range arguments. The one
    /// state that should reach `error` was the one state the summary could not
    /// describe.
    ///
    /// `jayhorn-recursive/UnsatAddition02` is the task that paid for it: its
    /// FALSE depends entirely on `m + n` wrapping, and it was proved TRUE.
    /// Which makes this the guard for the property the whole LIA encoding
    /// rests on -- LIA agrees with Java only on overflow-free paths, so an
    /// overflow guard that cannot fire makes every proof here unsound.
    #[test]
    fn an_overflow_guard_does_not_depend_on_the_call_it_feeds() {
        // The overflow must feed a *call*, which is the shape that breaks.
        // `overflow_program`'s `n + 1` is computed inside `inc`, not passed to
        // it, so it does not exercise this and an earlier draft of the test
        // passed with the defect reintroduced.
        let inc = mk("inc", "(I)I");
        let main = mk("main", "([Ljava/lang/String;)V");
        let (mut prog, _) = overflow_program();
        let (n, t, r) = (VarId(0), VarId(1), VarId(2));
        prog.bodies.insert(
            main.clone(),
            Body {
                is_static: true,
                key: main.clone(),
                entry: BlockId(0),
                vars: vec![int_var(0), int_var(1), int_var(2)],
                obligations: vec![Obligation {
                    id: ObligationId(0),
                    kind: ObligationKind::Assertion,
                    cond: Operand::Var(r),
                    bytecode_offset: 0,
                    line: None,
                    guarded: false,
                }],
                blocks: vec![Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![
                        Stmt::Assign(n, Rvalue::Nondet(Ty::Int, None)),
                        // `t = n + 1` can overflow ...
                        Stmt::Assign(t, Rvalue::Bin(BinOp::Add, Operand::Var(n), Operand::int(1))),
                        // ... and is then passed to a call.
                        Stmt::Assign(
                            r,
                            Rvalue::Call {
                                target: inc.clone(),
                                args: vec![Operand::Var(t)],
                                is_virtual: false,
                            },
                        ),
                        Stmt::Check(ObligationId(0)),
                    ],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                }],
            },
        );
        prog.entry = Some(main.clone());

        let obs = [ObligationRef {
            method: main.clone(),
            id: ObligationId(0),
        }];
        let smt2 = encode_chc_interproc(&prog, &main, &obs, &HashMap::new());

        let guards: Vec<&str> = smt2
            .lines()
            .zip(smt2.lines().skip(1))
            .filter(|(c, _)| c.starts_with("; overflow guard"))
            .map(|(_, clause)| clause)
            .collect();
        assert!(!guards.is_empty(), "no overflow guard emitted:\n{smt2}");
        for g in guards {
            assert!(
                !g.contains("_s "),
                "overflow guard conjoins a callee summary, so it cannot fire \
                 on the overflowing argument:\n{g}"
            );
        }
    }

    /// A method's entry fact must be a Horn rule, not a bare conjunction.
    ///
    /// It was emitted as `(assert (forall (..) (and (m_b0 ..) <ranges>)))`.
    /// That is not a rule: Z3 rewrites it into one containing a *negative*
    /// predicate and then refuses the whole query --
    ///
    /// ```text
    /// (:reason-unknown "Rule contains negative predicate <null>:
    ///  P!!1(#0) :- not m1_b0(#0).")
    /// ```
    ///
    /// -- so every program with a resolvable callee produced one malformed
    /// clause per method and came back `unknown`. That is the second
    /// well-formedness bug in this file to masquerade as solver weakness,
    /// after the free constants, and the third to hide a soundness bug behind
    /// itself: fixing it exposed the space invariants as unsound.
    #[test]
    fn a_method_entry_fact_is_an_implication_not_a_conjunction() {
        let (prog, main) = overflow_program();
        let obs = [ObligationRef {
            method: main.clone(),
            id: ObligationId(0),
        }];
        let smt2 = encode_chc_interproc(&prog, &main, &obs, &HashMap::new());

        for line in smt2.lines().filter(|l| l.starts_with("(assert")) {
            // An entry fact is the only assertion with no implication in it.
            if line.contains("=>") {
                continue;
            }
            assert!(
                !line.contains("(and "),
                "entry fact asserts a conjunction containing a predicate, \
                 which is not a Horn rule:\n{line}"
            );
        }
    }

    /// A callee's check must not become a precondition of its summary.
    ///
    /// This encoding is relational: a callee is a summary `m_s(args, ret)` and
    /// a call site applies it. Assuming a check's condition inside a callee
    /// therefore does not cut a path -- it narrows the summary's *domain*. Any
    /// call site that cannot establish the condition then has an unsatisfiable
    /// application, so the successor of the call disappears and everything
    /// after it is vacuously safe.
    ///
    /// `objects/objects14` is the case that paid for this test. A NullDeref
    /// assumed inside a callee gave its summary the precondition
    /// `receiver != 0`; the caller's inferred invariant had `v1 = 0`; the edge
    /// out of the call died; `main`'s blocks b3..b11 became empty; and a
    /// reachable `assert false` was proved TRUE, for -16.
    ///
    /// The entry method has no caller and so has no summary, which is why the
    /// assumption is kept there and only there.
    #[test]
    fn a_callee_check_does_not_become_a_summary_precondition() {
        let inc = mk("inc", "(I)I");
        let main = mk("main", "([Ljava/lang/String;)V");
        let (prog, _) = overflow_program();
        let mut prog = prog;

        // Give the callee a check of its own. Under the bug this contributed
        // `(not (= v0 0))` to every clause of `inc`, and thus to its summary.
        let guard = VarId(2);
        let b = prog.bodies.get_mut(&inc).expect("callee body");
        b.vars.push(int_var(2));
        b.obligations.push(Obligation {
            id: ObligationId(0),
            kind: ObligationKind::NullDeref,
            cond: Operand::Var(guard),
            bytecode_offset: 0,
            line: None,
            guarded: false,
        });
        b.blocks[0].stmts.push(Stmt::Check(ObligationId(0)));

        let obs = [ObligationRef {
            method: main.clone(),
            id: ObligationId(0),
        }];
        let smt2 = encode_chc_interproc(&prog, &main, &obs, &HashMap::new());

        // Isolate the callee's clauses -- the entry method legitimately
        // carries assumptions, so a whole-file search would not discriminate.
        let callee_clauses: Vec<&str> = smt2
            .lines()
            .filter(|l| l.contains("(inc_") || l.contains("m1_"))
            .collect();
        let assumed = callee_clauses
            .iter()
            .filter(|l| l.contains("(not (= v2 0))"))
            .count();
        assert_eq!(
            assumed,
            0,
            "callee check leaked into its summary as a precondition:\n{}",
            callee_clauses.join("\n")
        );
    }

    /// The regression this file's bitvector port exists for (#77).
    ///
    /// The engine cannot demonstrate it end to end: `bb.open()` only offers CHC
    /// what earlier engines left open, and the BMC finds this overflow
    /// immediately, so CHC never sees the obligation. The gating is the only
    /// reason the wrong answer was never emitted. Testing the encoder directly
    /// is the only way to hold the line.
    #[test]
    fn interprocedural_encoding_does_not_prove_an_overflowing_property() {
        if !z3_available() {
            eprintln!("no z3 on PATH; skipping");
            return;
        }
        let (prog, main) = overflow_program();
        // No seeded invariants: this test is about the overflow encoding, and
        // an empty map is the "nothing known" case the engine starts from.
        let no_invariants = HashMap::new();
        let obs = [ObligationRef {
            method: main.clone(),
            id: ObligationId(0),
        }];
        let smt2 = encode_chc_interproc(&prog, &main, &obs, &no_invariants);
        assert!(
            smt2.contains("; overflow"),
            "the inter-procedural encoding must route 32-bit overflow to \
             `error`; without that, unbounded Int makes `x + 1 > x` valid, \
             which it is not in Java"
        );
        let refs = [ObligationRef {
            method: main.clone(),
            id: ObligationId(0),
        }];
        let proved = run_chc_solver("z3", &smt2, &refs, solver_timeout_cap())
            .map(|(p, _)| p)
            .unwrap_or_default();
        assert!(
            proved.is_empty(),
            "CHC proved `inc(n) > n`, which fails at Integer.MAX_VALUE. That is \
             valid in linear integer arithmetic and false in Java (#77)."
        );
    }
}

#[cfg(test)]
mod lia_unmodelled_operator_tests {
    use super::*;
    use ajave_ir::{BinOp, Operand, Rvalue, Ty, VarId};

    fn encode(rv: &Rvalue) -> String {
        let theory = LiaTheory::new("t_");
        let mut fresh = FreshGen::new();
        let var_map: HashMap<usize, String> = HashMap::new();
        let is_wide = |_: &Operand| false;
        let mut overflow = Vec::new();
        let is_float = |_: &Operand| false;
        lia_rvalue(
            rv,
            &var_map,
            &mut fresh,
            &is_wide,
            &is_float,
            &mut overflow,
            &theory,
        )
    }

    /// LIA has no bitwise or shift operators, and its `div`/`mod` are Euclidean
    /// where Java's truncate toward zero. `LiaTheory::encode_binop` treats
    /// being asked for one as unreachable, because `Encoder` filters them
    /// first — and `lia_rvalue` does not go through `Encoder`.
    ///
    /// That invariant held only because an unrelated gate kept such bodies away
    /// from CHC. Widening which obligations CHC sees (`open_or_unconfirmed`)
    /// reached a body containing `%` and panicked on `UnsatEvenOdd01`.
    /// Havocing is the sound answer for an over-approximating engine: an
    /// unconstrained value contains the real one, so a proof over it holds of
    /// the program.
    #[test]
    fn an_operator_lia_cannot_model_is_havoced_not_encoded() {
        for op in [BinOp::Div, BinOp::Rem, BinOp::Shl, BinOp::Shr, BinOp::UShr] {
            let e = encode(&Rvalue::Bin(op, Operand::int(7), Operand::int(3)));
            assert!(e.starts_with("_f"), "{op:?} must be havoced, got {e}");
        }
    }

    /// Float arithmetic is havoced, not computed on bit patterns.
    ///
    /// `lia_operand` turns a float constant into its raw bits, so encoding
    /// `Add` over them computes integer addition of two bit patterns -- a
    /// different function that happens to be total. That is wrong rather than
    /// coarse, and it is the defect already recorded for the BMC in
    /// `smt_bmc/encode.rs`.
    ///
    /// The engine used to decline any program with a float-typed variable
    /// anywhere in any reachable method, which is sound but refused 37 of the
    /// 142 unproven TRUE tasks -- including every one whose assertion is about
    /// integers and whose `double` is incidental. Havocing is the sound answer
    /// for an over-approximating engine: an unconstrained value contains the
    /// real one, so a proof over it holds of the program.
    #[test]
    fn float_arithmetic_is_havoced_not_computed_on_bit_patterns() {
        let theory = LiaTheory::new("t_");
        let is_wide = |_: &Operand| false;
        // Only the float operands are declared float; everything else is not,
        // so a `true`-returning stub could not be what makes this pass.
        let is_float = |op: &Operand| {
            matches!(
                op,
                Operand::Const(Const::Float(_)) | Operand::Const(Const::Double(_))
            )
        };
        let f = || Operand::Const(Const::Float(1.5));

        for rv in [
            Rvalue::Bin(BinOp::Add, f(), f()),
            Rvalue::Bin(BinOp::Mul, f(), Operand::int(2)),
            Rvalue::Neg(f()),
            Rvalue::Cmp(CmpKind::FloatG, f(), f()),
            Rvalue::Cast(Ty::Int, Ty::Float, f()),
        ] {
            let mut fresh = FreshGen::new();
            let mut overflow = Vec::new();
            let e = lia_rvalue(
                &rv,
                &HashMap::new(),
                &mut fresh,
                &is_wide,
                &is_float,
                &mut overflow,
                &theory,
            );
            assert!(e.starts_with("_f"), "{rv:?} must be havoced, got {e}");
            assert!(
                overflow.is_empty(),
                "{rv:?} must not contribute an integer overflow guard, got {overflow:?}"
            );
        }

        // The integer case must still be encoded, or the check above would
        // pass for an encoder that havoced everything.
        let mut fresh = FreshGen::new();
        let mut overflow = Vec::new();
        let e = lia_rvalue(
            &Rvalue::Bin(BinOp::Add, Operand::int(1), Operand::int(2)),
            &HashMap::new(),
            &mut fresh,
            &is_wide,
            &is_float,
            &mut overflow,
            &theory,
        );
        assert!(
            e.contains('+'),
            "integer addition must still be encoded, got {e}"
        );
    }

    /// `And`/`Or`/`Xor` are the exception, and the distinction matters.
    ///
    /// The lifter lowers `&&`, `||` and `^` on booleans to the bitwise
    /// opcodes, so their operands are 0 or 1 -- a case LIA expresses exactly.
    /// The encoding is `(ite both-operands-in-{0,1} exact-value fresh)`, which
    /// keeps the guarantee this module exists for: on any operand outside
    /// {0,1} the guard is false and the value is an unconstrained binder, so
    /// nothing is invented. #77 was CHC encoding such operators as the literal
    /// `0`, which is not a conservative unknown but a specific wrong value.
    #[test]
    fn boolean_bitwise_operators_are_exact_and_fall_back_to_a_binder() {
        for op in [BinOp::And, BinOp::Or, BinOp::Xor] {
            let e = encode(&Rvalue::Bin(op, Operand::int(7), Operand::int(3)));
            assert!(
                e.starts_with("(ite "),
                "{op:?} should be conditional, got {e}"
            );
            assert!(
                e.contains("_f"),
                "{op:?} must fall back to an unconstrained binder, got {e}"
            );
            assert!(
                !e.ends_with(" 0)"),
                "{op:?} must not fall back to a literal value (#77), got {e}"
            );
        }
    }

    /// Narrowing truncates, which LIA cannot express either.
    #[test]
    fn a_narrowing_cast_is_havoced_not_encoded() {
        let e = encode(&Rvalue::Cast(Ty::Int, Ty::Long, Operand::Var(VarId(0))));
        assert!(
            e.starts_with("_f"),
            "narrowing cast must be havoced, got {e}"
        );
    }

    /// The operators LIA *does* model must still be encoded, or the fix would
    /// have turned the engine into a havoc machine.
    #[test]
    fn operators_lia_does_model_are_still_encoded() {
        let e = encode(&Rvalue::Bin(BinOp::Add, Operand::int(2), Operand::int(3)));
        assert!(e.contains('+'), "addition must still be encoded, got {e}");
    }
}

/// Both CHC encoders, run over the same programs, required to agree where
/// agreement is a soundness property.
///
/// `chc.rs` carries two encoders — `encode_chc_interproc` (LIA, unbounded `Int`
/// with explicit overflow guards) and `encode_chc_single` (bitvector, exact
/// machine integers) — selected by whether the program has a resolvable call.
/// They encode the same language, for the same obligations, for the same
/// engine. Three capabilities were once added to one and not the other in a
/// single week; each divergence cost a wrong answer or a silently lost task,
/// and each was found by reducing a failing benchmark days later.
///
/// # What this asserts, and what it deliberately does not
///
/// The two are **not** semantically identical and must not be tested as if they
/// were. LIA over-approximates a Java `int` as an unbounded integer and routes
/// the overflow cases to `error`; the bitvector encoding wraps natively. On a
/// safe program they may legitimately differ in *precision* — one proves it and
/// the other returns `unknown` — and failing on that would only encourage
/// whoever hits it to weaken the stronger encoder.
///
/// So the harness splits the two questions, exactly as `metamorphic.py` does:
///
/// * **A `Safe` answer on a program that is unsafe by construction fails.**
///   That is the −16 direction, it is a claim about every execution, and it is
///   the same claim from both encoders. A guard present in one and missing in
///   the other shows up here and nowhere else.
/// * **A precision difference on a safe program is reported, not failed.**
///
/// Ground truth comes from the JLS and the program's construction, never from
/// what either encoder currently says — that is the thing under test.
#[cfg(test)]
mod encoder_conformance {
    use super::tests::z3_available;
    use super::*;
    use ajave_ir::{BinOp, Block, Body, Const, Operand, Rvalue, Stmt, Terminator, Ty, VarId};

    fn mk(name: &str) -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: name.into(),
            desc: "()V".into(),
        }
    }

    fn ivar(slot: u16) -> VarInfo {
        VarInfo {
            kind: VarKind::Local(slot),
            ty: Ty::Int,
        }
    }

    /// A single-method program: the shape `encode_chc_single` is chosen for,
    /// and one `encode_chc_interproc` handles too (it simply has no callees to
    /// summarise). Both encoders therefore apply, which is what makes them
    /// comparable at all.
    fn single(nvars: u16, stmts: Vec<Stmt>, cond: Operand) -> (Program, MethodKey) {
        let m = mk("main");
        let mut prog = Program::default();
        prog.bodies.insert(
            m.clone(),
            Body {
                is_static: true,
                key: m.clone(),
                entry: BlockId(0),
                vars: (0..nvars).map(ivar).collect(),
                obligations: vec![Obligation {
                    id: ObligationId(0),
                    kind: ObligationKind::Assertion,
                    cond,
                    bytecode_offset: 0,
                    line: None,
                    guarded: false,
                }],
                blocks: vec![Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts,
                    term: Terminator::Return(None),
                    exceptional: vec![],
                }],
            },
        );
        prog.entry = Some(m.clone());
        (prog, m)
    }

    /// Ask one encoder whether the error predicate is unreachable.
    ///
    /// Mirrors the engine's own call path — `drop_empty_quantifiers` included —
    /// because an encoder tested through a different path is not the encoder
    /// that runs.
    fn asks_safe(smt2: String, m: &MethodKey) -> ChcOutcome {
        let refs = [ObligationRef {
            method: m.clone(),
            id: ObligationId(0),
        }];
        run_chc_solver("z3", &drop_empty_quantifiers(&smt2), &refs, 10)
            .map(|(_, outcome)| outcome)
            .unwrap_or(ChcOutcome::Unknown)
    }

    fn both(prog: &Program, m: &MethodKey) -> (ChcOutcome, ChcOutcome) {
        let obs = [ObligationRef {
            method: m.clone(),
            id: ObligationId(0),
        }];
        let body = prog.body(m).expect("body");
        let lia = asks_safe(encode_chc_interproc(prog, m, &obs, &HashMap::new()), m);
        let bv = asks_safe(encode_chc_single(body, &[ObligationId(0)]), m);
        (lia, bv)
    }

    // ---- the corpus: verdict by construction, argued in each comment ----

    /// `int x = 5; assert x == 5;` — safe, trivially.
    fn safe_constant() -> (Program, MethodKey) {
        let (x, c) = (VarId(0), VarId(1));
        single(
            2,
            vec![
                Stmt::Assign(x, Rvalue::Use(Operand::Const(Const::Int(5)))),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Eq, Operand::Var(x), Operand::int(5))),
                Stmt::Check(ObligationId(0)),
            ],
            Operand::Var(c),
        )
    }

    /// `assert false;` — unsafe, reachable on every execution.
    fn unsafe_constant() -> (Program, MethodKey) {
        single(1, vec![Stmt::Check(ObligationId(0))], Operand::int(0))
    }

    /// `int n = nondet(); assert n == 0;` — unsafe: nothing constrains `n`,
    /// so JLS 4.2.1 permits any of 2^32 values and all but one violate it.
    fn unsafe_nondet() -> (Program, MethodKey) {
        let (n, c) = (VarId(0), VarId(1));
        single(
            2,
            vec![
                Stmt::Assign(n, Rvalue::Nondet(Ty::Int, None)),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Eq, Operand::Var(n), Operand::int(0))),
                Stmt::Check(ObligationId(0)),
            ],
            Operand::Var(c),
        )
    }

    /// `int n = nondet(); assume(n > 0); assert n > 0;` — safe: the assumption
    /// is exactly the assertion.
    fn safe_assumed() -> (Program, MethodKey) {
        let (n, g) = (VarId(0), VarId(1));
        single(
            2,
            vec![
                Stmt::Assign(n, Rvalue::Nondet(Ty::Int, None)),
                Stmt::Assign(g, Rvalue::Bin(BinOp::Gt, Operand::Var(n), Operand::int(0))),
                Stmt::Assume(Operand::Var(g)),
                Stmt::Check(ObligationId(0)),
            ],
            Operand::Var(g),
        )
    }

    /// `int n = nondet(); assert n + 1 > n;` — **unsafe in Java**, and this is
    /// the one that separates the theories. It is valid over the unbounded
    /// integers LIA uses, and false at `Integer.MAX_VALUE` where `+ 1` wraps to
    /// `Integer.MIN_VALUE` (JLS 15.18.2). The bitvector encoding gets this from
    /// its semantics; LIA gets it only from an explicit overflow guard, which is
    /// the asymmetry most likely to rot.
    fn unsafe_overflow() -> (Program, MethodKey) {
        let (n, s, c) = (VarId(0), VarId(1), VarId(2));
        single(
            3,
            vec![
                Stmt::Assign(n, Rvalue::Nondet(Ty::Int, None)),
                Stmt::Assign(s, Rvalue::Bin(BinOp::Add, Operand::Var(n), Operand::int(1))),
                Stmt::Assign(c, Rvalue::Bin(BinOp::Gt, Operand::Var(s), Operand::Var(n))),
                Stmt::Check(ObligationId(0)),
            ],
            Operand::Var(c),
        )
    }

    fn corpus() -> Vec<(&'static str, bool, (Program, MethodKey))> {
        vec![
            ("safe_constant", true, safe_constant()),
            ("safe_assumed", true, safe_assumed()),
            ("unsafe_constant", false, unsafe_constant()),
            ("unsafe_nondet", false, unsafe_nondet()),
            ("unsafe_overflow", false, unsafe_overflow()),
        ]
    }

    /// The soundness half. Neither encoder may call an unsafe program safe.
    ///
    /// This is the property a divergence actually threatens: a guard that lives
    /// in one encoder and not the other lets that one prove something false,
    /// and CHC publishes `Discharged` on a `Safe`, so the cost is a wrong TRUE
    /// at −16 rather than a lost proof.
    #[test]
    fn neither_encoder_calls_an_unsafe_program_safe() {
        if !z3_available() {
            eprintln!("no z3 on PATH; skipping");
            return;
        }
        for (name, is_safe, (prog, m)) in corpus() {
            if is_safe {
                continue;
            }
            let (lia, bv) = both(&prog, &m);
            assert_ne!(
                lia,
                ChcOutcome::Safe,
                "{name}: the LIA encoder proved a program that is unsafe by construction"
            );
            assert_ne!(
                bv,
                ChcOutcome::Safe,
                "{name}: the bitvector encoder proved a program that is unsafe by construction"
            );
        }
    }

    /// The harness's own liveness check.
    ///
    /// Every assertion above is of the form "not Safe", which an encoder that
    /// silently stopped answering would satisfy perfectly. `assert false` with
    /// no guard is reachable on every execution and both theories decide it
    /// immediately, so `Unknown` here means the harness has gone blind rather
    /// than that the program is hard.
    #[test]
    fn both_encoders_actually_answer() {
        if !z3_available() {
            eprintln!("no z3 on PATH; skipping");
            return;
        }
        let (prog, m) = unsafe_constant();
        let (lia, bv) = both(&prog, &m);
        assert_eq!(lia, ChcOutcome::Unsafe, "LIA did not decide `assert false`");
        assert_eq!(bv, ChcOutcome::Unsafe, "BV did not decide `assert false`");
    }

    /// The precision half. A difference here is legitimate — the theories are
    /// not the same — so this reports rather than fails. It exists so that a
    /// capability landing in one encoder and not the other is *visible* on the
    /// next test run instead of surfacing as a lost task three commits later.
    #[test]
    fn precision_differences_between_the_encoders_are_reported() {
        if !z3_available() {
            eprintln!("no z3 on PATH; skipping");
            return;
        }
        let mut diverged = Vec::new();
        for (name, is_safe, (prog, m)) in corpus() {
            if !is_safe {
                continue;
            }
            let (lia, bv) = both(&prog, &m);
            if lia != bv {
                diverged.push(format!("{name}: lia={lia:?} bv={bv:?}"));
            }
            assert!(
                lia == ChcOutcome::Safe || bv == ChcOutcome::Safe,
                "{name} is safe by construction and neither encoder proved it \
                 (lia={lia:?}, bv={bv:?}) — that is not a precision difference, \
                 it is both of them failing"
            );
        }
        if !diverged.is_empty() {
            eprintln!(
                "chc: encoders differ in precision on {} safe program(s):\n  {}",
                diverged.len(),
                diverged.join("\n  ")
            );
        }
    }
}
