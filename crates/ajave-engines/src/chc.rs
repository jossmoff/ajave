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
use std::collections::{HashMap, HashSet};
use std::io::Write as IoWrite;
use std::process::{Command, Stdio};

use log::{debug, info, trace, warn};
use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_ir::*;

pub struct ChcEngine {
    solver_binary: String,
    done: bool,
}

impl ChcEngine {
    pub fn new() -> Self {
        let binary = std::env::var("ROAST_CHC_SOLVER").unwrap_or_else(|_| "z3".to_string());
        ChcEngine {
            solver_binary: binary,
            done: false,
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

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
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
            return Progress::Stalled;
        }

        // CHC's LIA encoding only models integer arithmetic, not heap/arrays.
        // Skip if any reachable method uses arrays, field access, or unresolved
        // calls to library methods — proving those safe requires heap/string
        // modeling that LIA doesn't have.
        let reachable_methods = prog.reachable_from_entry();
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
        let uses_float = reachable_methods
            .iter()
            .any(|mk| prog.body(mk).is_some_and(body_uses_float_types));
        if uses_float {
            info!("chc: skipping — reachable methods use float/double arithmetic");
            return Progress::Stalled;
        }
        // Skip if any reachable method has calls to non-Verifier library methods
        // without bodies. These become havoced (unconstrained) in the LIA encoding,
        // which is unsound for discharge — the real method may throw exceptions or
        // return values that violate assertions. Verifier.nondet* calls are safe
        // because CHC models them as unconstrained inputs (correct semantics).
        let has_unresolved = reachable_methods.iter().any(|mk| {
            prog.body(mk).map_or(false, |b| {
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

        // Only attempt Assertion obligations (NegArraySize etc. require heap).
        let obs: Vec<ObligationId> = open
            .iter()
            .filter(|oref| oref.method == *entry)
            .filter(|oref| {
                body.obligation(oref.id).kind == ObligationKind::Assertion
            })
            .map(|oref| oref.id)
            .collect();

        if obs.is_empty() {
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
        let mut invariants: HashMap<(MethodKey, BlockId), Vec<(usize, i64, i64)>> =
            HashMap::new();
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
            encode_chc_interproc(prog, entry, &obs, &invariants)
        } else {
            info!("chc: using single-method BV encoding");
            encode_chc_single(body, &obs)
        };

        debug!("chc: generated {} bytes of CHC encoding", smt2.len());
        if let Ok(path) = std::env::var("AJAVE_CHC_DUMP") {
            let _ = std::fs::write(&path, &smt2);
        }
        trace!("chc: encoding:\n{}", &smt2[..smt2.len().min(4000)]);

        let mut advanced = false;
        match run_chc_solver(&self.solver_binary, &smt2, &obs) {
            Ok(results) => {
                for (oid, safe) in results {
                    if safe {
                        let oref = ObligationRef {
                            method: entry.clone(),
                            id: oid,
                        };
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

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Returns true if the body uses array or heap operations that CHC's LIA
/// encoding cannot model: array load/store/new, field get/put, instanceof.
/// Seconds Spacer may spend on one query.
///
/// CHC runs late in the portfolio, so this is a slice of the remaining budget
/// rather than the whole of it: a proof needing longer is one the other engines
/// have already failed to find, and spending the task's whole budget on it
/// costs the answers they would have produced.
fn solver_timeout_secs() -> u32 {
    std::env::var("AJAVE_CHC_TIMEOUT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(10)
}

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

/// Check if the program has calls from the entry method (or its callees)
/// to methods that we have bodies for — i.e. inter-procedural reasoning helps.
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
                pos = inner[pos..].find(';').map(|p| pos + p + 1).unwrap_or(bytes.len());
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
                        pos = inner[pos..].find(';').map(|p| pos + p + 1).unwrap_or(bytes.len());
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
    let Expr::Bin(Op::And, lo_e, hi_e) = e else { return None };
    let (Expr::Bin(Op::Le, l, lv), Expr::Bin(Op::Le, hv, h)) =
        (lo_e.as_ref(), hi_e.as_ref()) else { return None };
    let (Expr::Int(lo), Expr::Var(v1), Expr::Var(v2), Expr::Int(hi)) =
        (l.as_ref(), lv.as_ref(), hv.as_ref(), h.as_ref()) else { return None };
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
        FreshGen { counter: 0, extra_forall: Vec::new() }
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

const INT_MIN: i64 = -2147483648;
const INT_MAX: i64 = 2147483647;

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
fn lia_rvalue(
    rv: &Rvalue,
    var_map: &HashMap<usize, String>,
    fresh: &mut FreshGen,
    is_wide: &dyn Fn(&Operand) -> bool,
    overflow: &mut Vec<String>,
    theory: &LiaTheory,
) -> String {
    match rv {
        Rvalue::Use(o) => lia_operand(o, var_map),
        Rvalue::Nondet(..) | Rvalue::Havoc(_, _) => fresh.fresh(),
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
                return fresh.fresh();
            }
            let l = lia_operand(a, var_map);
            let r = lia_operand(b, var_map);
            let e = theory.encode_binop(op, &l, &r);
            if smt_text::overflowing(op) {
                overflow.push(smt_text::lia_overflow_cond(
                    &e,
                    is_wide(a) || is_wide(b),
                ));
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
        _ => fresh.fresh(),
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
    obligations: &[ObligationId],
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
    invariants: &HashMap<(MethodKey, BlockId), Vec<(usize, i64, i64)>>,
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

    // Declare block relations for each method.
    for mk in &all_methods {
        let Some(body) = prog.body(mk) else { continue };
        let mid = &method_ids[mk];
        let n_vars = body.vars.len();
        let sig = (0..n_vars).map(|_| "Int").collect::<Vec<_>>().join(" ");

        out.push_str(&format!("; blocks for {}\n", mk));
        for block in &body.blocks {
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
        let is_entry = mk == entry;

        let src_vars: Vec<String> = (0..n_vars).map(|i| format!("v{}", i)).collect();
        let dst_vars: Vec<String> = (0..n_vars).map(|i| format!("w{}", i)).collect();

        let forall_src: String = src_vars
            .iter()
            .map(|v| format!("({} Int)", v))
            .collect::<Vec<_>>()
            .join(" ");

        // Every clause body that mentions a source block goes through here, so
        // conjoining the block's invariant once reaches all of them.
        let block_app_src = |bid: u32| -> String {
            let app = format!("({}_b{} {})", mid, bid, src_vars.join(" "));
            let Some(bounds) = invariants.get(&(mk.clone(), BlockId(bid))) else {
                return app;
            };
            let mut parts = vec![app];
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
            format!("({}_b{} {})", mid, bid, dst_vars.join(" "))
        };

        out.push_str(&format!(
            "; === {} ===\n(assert (forall ({}) {}))\n",
            mk, forall_src, block_app_src(body.entry.0)
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
            let mut var_map: HashMap<usize, String> = HashMap::new();
            let mut call_constraints: Vec<String> = Vec::new();

            for i in 0..n_vars {
                var_map.insert(i, format!("v{}", i));
            }

            for stmt in &block.stmts {
                match stmt {
                    Stmt::Assign(vid, rv) => match rv {
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
                        _ => {
                            let expr = lia_rvalue(
                                rv, &var_map, &mut fresh, &is_wide, &mut overflow, &theory,
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
                    },
                    Stmt::Assume(op) => {
                        let expr = lia_operand(op, &var_map);
                        constraints.push(format!("(not (= {} 0))", expr));
                    }
                    Stmt::Check(oid) => {
                        if is_entry && obligations.contains(oid) {
                            let ob = body.obligation(*oid);
                            let cond_expr = lia_operand(&ob.cond, &var_map);
                            let mut conds = constraints.clone();
                            conds.extend(call_constraints.iter().cloned());
                            conds.push(format!("(= {} 0)", cond_expr));
                            conds.push(block_app_src(block.id.0));

                            let body_expr = and_expr(&conds);
                            let q = add_extra_forall_lia(&forall_src, &fresh);
                            out.push_str(&format!(
                                "(assert (forall ({}) (=> {} error)))\n",
                                q, body_expr
                            ));
                        }
                    }
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
                conds.extend(call_constraints.iter().cloned());
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
            for i in 0..n_vars {
                let val = var_map.get(&i).cloned().unwrap_or_else(|| format!("v{}", i));
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
                out.push_str(&format!(
                    "(assert (forall ({}) (=> {} {})))\n",
                    q,
                    body_expr,
                    block_app_dst(target_bid)
                ));
            };

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
                        mk_trans(target.0, &[eq.clone()], &mut out);
                        neg.push(format!("(not {})", eq));
                    }
                    mk_trans(default.0, &neg, &mut out);
                }
                Terminator::Return(Some(op)) if ret_ch != 'V' => {
                    let ret_expr = lia_operand(op, &var_map);
                    let mut summary_args: Vec<String> = param_indices
                        .iter()
                        .map(|&pi| {
                            var_map.get(&pi).cloned().unwrap_or_else(|| format!("v{}", pi))
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

    let var_widths: Vec<(usize, u32)> = body
        .vars
        .iter()
        .enumerate()
        .map(|(i, vi)| (i, width_of(&vi.ty)))
        .collect();
    let width_map: HashMap<usize, u32> = var_widths.iter().cloned().collect();
    let mut fresh_decls: Vec<(String, u32)> = Vec::new();
    let var_indices = &var_widths;
    let n_vars = var_indices.len();

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

    let src_vars: Vec<String> = (0..n_vars).map(|i| format!("v{}", i)).collect();
    let dst_vars: Vec<String> = (0..n_vars).map(|i| format!("v{}p", i)).collect();

    let forall_src: String = var_indices
        .iter()
        .enumerate()
        .map(|(i, (_, w))| format!("(v{} (_ BitVec {}))", i, w))
        .collect::<Vec<_>>()
        .join(" ");
    let forall_both: String = {
        let src = var_indices
            .iter()
            .enumerate()
            .map(|(i, (_, w))| format!("(v{} (_ BitVec {}))", i, w));
        let dst = var_indices
            .iter()
            .enumerate()
            .map(|(i, (_, w))| format!("(v{}p (_ BitVec {}))", i, w));
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

        for i in 0..n_vars {
            var_map.insert(i, format!("v{}", i));
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
                Stmt::Check(oid) => {
                    if obligations.contains(oid) {
                        let ob = body.obligation(*oid);
                        let cond_expr =
                            smt_text::encode_operand(&BitvectorTheory, &ob.cond, &var_map);
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
                    }
                }
                _ => {}
            }
        }

        let mut assign_constraints: Vec<String> = Vec::new();
        for i in 0..n_vars {
            let val = var_map.get(&i).unwrap();
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
                forall_both, body_expr, block_app_dst(target_bid)
            )
        };

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
                    out.push_str(&mk_trans(target.0, &[eq.clone()]));
                    neg_cases.push(format!("(not {})", eq));
                }
                out.push_str(&mk_trans(default.0, &neg_cases));
            }
            _ => {}
        }
    }

    if !fresh_decls.is_empty() {
        let insert_pos = out.find("(assert ").unwrap_or(out.len());
        let decl_block: String = fresh_decls
            .iter()
            .map(|(name, width)| format!("(declare-fun {} () (_ BitVec {}))\n", name, width))
            .collect();
        out.insert_str(insert_pos, &decl_block);
    }

    out.push_str("(assert (not error))\n");
    out.push_str("(check-sat)\n");

    out
}

// ---------------------------------------------------------------------------
// Solver interaction
// ---------------------------------------------------------------------------

fn run_chc_solver(
    binary: &str,
    smt2: &str,
    obligations: &[ObligationId],
) -> Result<Vec<(ObligationId, bool)>, String> {
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
            &format!("-T:{}", solver_timeout_secs()),
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
        "sat" => Ok(obligations.iter().map(|oid| (*oid, true)).collect()),
        _ => Ok(vec![]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk(name: &str, desc: &str) -> MethodKey {
        MethodKey { class: "Main".into(), name: name.into(), desc: desc.into() }
    }

    fn int_var(slot: u16) -> VarInfo {
        VarInfo { kind: VarKind::Local(slot), ty: Ty::Int }
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
                        Stmt::Assign(
                            c,
                            Rvalue::Bin(BinOp::Gt, Operand::Var(r), Operand::Var(n)),
                        ),
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

    fn z3_available() -> bool {
        Command::new("which")
            .arg("z3")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
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
        let smt2 = encode_chc_interproc(&prog, &main, &[ObligationId(0)]);
        assert!(
            smt2.contains("; overflow"),
            "the inter-procedural encoding must route 32-bit overflow to \
             `error`; without that, unbounded Int makes `x + 1 > x` valid, \
             which it is not in Java"
        );
        let proved = run_chc_solver("z3", &smt2, &[ObligationId(0)]).unwrap_or_default();
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
        lia_rvalue(rv, &var_map, &mut fresh, &is_wide, &mut overflow, &theory)
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
        for op in [
            BinOp::Div, BinOp::Rem, BinOp::And, BinOp::Or,
            BinOp::Xor, BinOp::Shl, BinOp::Shr, BinOp::UShr,
        ] {
            let e = encode(&Rvalue::Bin(op, Operand::int(7), Operand::int(3)));
            assert!(e.starts_with("_f"), "{op:?} must be havoced, got {e}");
        }
    }

    /// Narrowing truncates, which LIA cannot express either.
    #[test]
    fn a_narrowing_cast_is_havoced_not_encoded() {
        let e = encode(&Rvalue::Cast(Ty::Int, Ty::Long, Operand::Var(VarId(0))));
        assert!(e.starts_with("_f"), "narrowing cast must be havoced, got {e}");
    }

    /// The operators LIA *does* model must still be encoded, or the fix would
    /// have turned the engine into a havoc machine.
    #[test]
    fn operators_lia_does_model_are_still_encoded() {
        let e = encode(&Rvalue::Bin(BinOp::Add, Operand::int(2), Operand::int(3)));
        assert!(e.contains('+'), "addition must still be encoded, got {e}");
    }
}
