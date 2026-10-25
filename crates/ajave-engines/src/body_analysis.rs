//! Shared body-analysis utilities used by multiple engines.

use ajave_ir::{BinOp, BlockId, Body, Operand, Rvalue, Stmt, Terminator, VarId};
use ajave_models;

/// Returns `true` if the body uses operations that are havoced (unmodelled)
/// in the simplified SMT/LIA encoding: field access, instance-of checks,
/// method calls, or explicit havoc. Proving engines skip such bodies to
/// remain sound.
// Nested deliberately: matching `Stmt::Assign` and then the `Rvalue` mirrors
// the IR's own shape, and fusing them into one pattern reads worse.
#[allow(clippy::collapsible_match)]
pub fn body_uses_havoced_ops(body: &Body) -> bool {
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(_, rv) => match rv {
                    Rvalue::GetStatic(_)
                    | Rvalue::GetField { .. }
                    | Rvalue::InstanceOf { .. }
                    | Rvalue::Call { .. }
                    | Rvalue::Havoc(_, _) => return true,
                    _ => {}
                },
                Stmt::PutField { .. } => return true,
                _ => {}
            }
        }
    }
    false
}

/// Returns `true` if the body uses Long or Double typed variables.
/// The interval AI domain uses i32 arithmetic, so its intervals are unsound
/// for bodies that manipulate 64-bit values (comparisons, casts, etc.).
pub fn body_uses_wide_types(body: &Body) -> bool {
    use ajave_ir::Ty;
    body.vars
        .iter()
        .any(|vi| matches!(vi.ty, Ty::Long | Ty::Double))
}

/// Returns `true` if the body uses Float or Double typed variables (but not
/// necessarily Long). Used to route bodies to the widening interval CPA.
pub fn body_uses_float_types(body: &Body) -> bool {
    use ajave_ir::Ty;
    body.vars
        .iter()
        .any(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
}

/// Returns `true` if the body uses Long typed variables. The i32-based
/// interval domain is unsound for Long arithmetic; these bodies must be
/// skipped entirely by the standard interval analysis.
pub fn body_uses_long_types(body: &Body) -> bool {
    use ajave_ir::Ty;
    body.vars.iter().any(|vi| matches!(vi.ty, Ty::Long))
}

/// Returns `true` if the body calls transcendental Math methods (sin, cos, exp,
/// log, pow, sqrt, etc.) that require a nonlinear real arithmetic solver.
pub fn body_uses_transcendental_math(body: &Body) -> bool {
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(_, Rvalue::Call { target, .. }) = stmt {
                if ajave_models::is_transcendental_math(&target.class, &target.name) {
                    return true;
                }
            }
        }
    }
    false
}

/// Returns `true` if the body has any back-edges (loops).
pub fn body_has_loops(body: &Body) -> bool {
    for block in &body.blocks {
        let succs = match &block.term {
            Terminator::Goto(t) => vec![*t],
            Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
            Terminator::Switch { cases, default, .. } => {
                let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
                v.push(*default);
                v
            }
            _ => vec![],
        };
        for s in succs {
            if s.0 <= block.id.0 {
                return true;
            }
        }
    }
    false
}

/// Walk backward through a block's statements to find the most recent
/// assignment of `v` to a binary operation `Rvalue::Bin(op, a, b)`.
pub fn find_defining_bin(
    body: &Body,
    block: BlockId,
    v: VarId,
) -> Option<(BinOp, &Operand, &Operand)> {
    for s in body.block(block).stmts.iter().rev() {
        if let Stmt::Assign(dv, Rvalue::Bin(op, a, b)) = s {
            if *dv == v {
                return Some((*op, a, b));
            }
        }
    }
    None
}

/// Negate a comparison operator (Eq<->Ne, Lt<->Ge, Le<->Gt).
/// Non-comparison operators are returned unchanged.
pub fn negate_binop(op: BinOp) -> BinOp {
    match op {
        BinOp::Eq => BinOp::Ne,
        BinOp::Ne => BinOp::Eq,
        BinOp::Lt => BinOp::Ge,
        BinOp::Le => BinOp::Gt,
        BinOp::Gt => BinOp::Le,
        BinOp::Ge => BinOp::Lt,
        other => other,
    }
}

/// Does this body call a method whose exceptional behaviour we do not model?
///
/// A library method with no body is either havoced or modelled for its *value*.
/// Neither captures the exceptions it may raise: `"abc".charAt(5)` throws
/// `StringIndexOutOfBoundsException`, but the IR emits no `Check` for it, so no
/// engine can find a violation and the program looks safe by vacuity.
///
/// Any engine that wants to discharge a **no-runtime-exception** obligation has
/// to account for that. The BMC does it via
/// `Completeness::has_potentially_throwing_havoc`; the interval AI has no
/// equivalent notion of a call at all, so it needs this check instead.
///
/// Methods with bodies are excluded: those are analysed directly, and whatever
/// they throw shows up as an obligation in the callee.
pub fn body_has_unmodelled_throwing_call(prog: &ajave_ir::Program, body: &Body) -> bool {
    first_unmodelled_throwing_call(prog, body).is_some()
}

/// The first such call, for diagnostics: knowing *which* signature blocks a
/// proof is what tells us whether the allowlist is too tight or the program
/// genuinely does something we cannot reason about.
pub fn first_unmodelled_throwing_call<'a>(
    prog: &ajave_ir::Program,
    body: &'a Body,
) -> Option<&'a ajave_ir::MethodKey> {
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(_, Rvalue::Call { target, .. }) = stmt {
                if prog.body(target).is_some() {
                    continue; // has a body — analysed on its own terms
                }
                // An interface or abstract method has no body of its own, but
                // the call is still resolvable when every implementation we can
                // see does. `ObjectFactory.createObject()` is declared on an
                // interface and implemented by the benchmark, so treating it as
                // an unanalysable library call blocked those tasks outright.
                let impls = prog.devirtualise(target);
                if !impls.is_empty() && impls.iter().all(|k| prog.body(k).is_some()) {
                    continue;
                }
                // A call only blocks the verdict when we cannot state *why*
                // it might throw. If its contract names conditions over the
                // arguments, the lifter has already seeded them as obligations
                // and the engines either discharge them or leave them open —
                // either way the burden is carried explicitly, and vetoing here
                // as well would double-count it and lose every program that
                // merely *mentions* such a method.
                match ajave_models::contract_of(&target.class, &target.name, &target.desc) {
                    Some(c) if c.preconditions_all_seeded() => continue,
                    Some(_) => return Some(target),
                    None => {
                        if crate::smt_bmc::could_throw_runtime_exception(target) {
                            return Some(target);
                        }
                    }
                }
            }
        }
    }
    None
}

// ─── Per-obligation scoping (the three-levers experiment, docs/plans/three-levers.md) ───

/// Whether per-obligation scoping is enabled.
///
/// `cegar` refuses a whole program when `body_uses_havoced_ops` holds anywhere,
/// and `chc` refuses any body where `body_uses_heap_ops` does. Measured, that
/// guard skips 109 of 121 tasks — but obligations are individual, and one havoc
/// in a sixty-obligation method kills all sixty, including the fifty-nine whose
/// paths never reach it.
///
/// Gated so one build can be ablated against itself. See also
/// `AJAVE_ASK_ON_DECLINE` and `AJAVE_SCOPE_ALL_METHODS`.
pub fn obligation_scoping_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_SCOPE_OBLIGATION").as_deref() != Ok("0"))
}

/// Whether an engine that cannot proceed should publish a `Query` rather than
/// simply returning `Blocked`.
pub fn ask_on_decline_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_ASK_ON_DECLINE").as_deref() != Ok("0"))
}

/// Whether engines may analyse methods other than the entry point.
pub fn all_methods_scoping_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_SCOPE_ALL_METHODS").as_deref() != Ok("0"))
}

/// Blocks of `body` in which `pred` holds of some statement.
fn blocks_matching(body: &Body, pred: &dyn Fn(&Stmt) -> bool) -> Vec<BlockId> {
    body.blocks
        .iter()
        .filter(|b| b.stmts.iter().any(pred))
        .map(|b| b.id)
        .collect()
}

/// Obligations in `body` that an unsupported statement can reach.
///
/// Forward CFG reachability from every block containing a statement `pred`
/// accepts, to every `Check`. An obligation NOT in the returned set is one the
/// unsupported feature cannot influence, so an engine that refuses the feature
/// may still attempt that obligation.
///
/// # Why this direction of imprecision is the safe one
///
/// The caller uses this to *widen* what an over-approximating engine attempts,
/// and a discharge is a claim about every execution — so an obligation wrongly
/// judged unreachable from a havoc would be a wrong TRUE at −16.
///
/// Every source of imprecision here therefore over-approximates reachability:
///
/// * Block granularity, not statement — a havoc late in a block taints the
///   obligations checked earlier in that same block.
/// * Exceptional edges are followed, so a handler counts as reachable.
/// * A call is treated as reaching **everything** in the callee and, because a
///   caller resumes after it returns, the call's own successors are already
///   covered by the ordinary CFG walk.
/// * A body we cannot find contributes all of its obligations.
///
/// Deliberately *not* backward slicing, which is the stronger version: slicing
/// rewrites the body, which renumbers `VarId`s and so invalidates every
/// obligation and invariant keyed by them. Reachability answers the same
/// question without touching the IR.
pub fn obligations_reachable_from(
    prog: &ajave_ir::Program,
    method: &ajave_ir::MethodKey,
    body: &Body,
    pred: &dyn Fn(&Stmt) -> bool,
) -> std::collections::HashSet<(ajave_ir::MethodKey, ajave_ir::ObligationId)> {
    use std::collections::{BTreeSet, HashSet};
    let mut out: HashSet<(ajave_ir::MethodKey, ajave_ir::ObligationId)> = HashSet::new();
    let starts = blocks_matching(body, pred);
    if starts.is_empty() {
        return out;
    }

    // Blocks reachable from any offending block, within this method.
    let mut seen: BTreeSet<BlockId> = BTreeSet::new();
    let mut work = starts;
    // Methods a reachable call enters: all of their obligations are tainted,
    // transitively, because we do not analyse what the callee does.
    let mut tainted: BTreeSet<ajave_ir::MethodKey> = BTreeSet::new();
    while let Some(bid) = work.pop() {
        if !seen.insert(bid) {
            continue;
        }
        let Some(block) = body.blocks.get(bid.0 as usize) else {
            continue;
        };
        for stmt in &block.stmts {
            match stmt {
                Stmt::Check(oid) => {
                    out.insert((method.clone(), *oid));
                }
                Stmt::Assign(_, Rvalue::Call { target, .. }) => {
                    tainted.insert(target.clone());
                }
                _ => {}
            }
        }
        match &block.term {
            Terminator::Goto(t) => work.push(*t),
            Terminator::Branch { then_, else_, .. } => {
                work.push(*then_);
                work.push(*else_);
            }
            Terminator::Switch { cases, default, .. } => {
                for (_, t) in cases {
                    work.push(*t);
                }
                work.push(*default);
            }
            Terminator::Return(_) | Terminator::Halt | Terminator::Throw(_) => {}
            Terminator::Diverge(_) => {}
        }
        for e in &block.exceptional {
            work.push(e.target);
        }
    }

    // Everything the tainted methods can reach, transitively.
    let mut mwork: Vec<ajave_ir::MethodKey> = tainted.into_iter().collect();
    let mut mseen: BTreeSet<ajave_ir::MethodKey> = BTreeSet::new();
    while let Some(mk) = mwork.pop() {
        if !mseen.insert(mk.clone()) {
            continue;
        }
        let Some(b) = prog.body(&mk) else { continue };
        for block in &b.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Stmt::Check(oid) => {
                        out.insert((mk.clone(), *oid));
                    }
                    Stmt::Assign(_, Rvalue::Call { target, .. }) => {
                        mwork.push(target.clone());
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// `Stmt` predicate matching the operations `body_uses_havoced_ops` rejects.
#[allow(clippy::collapsible_match)]
pub fn stmt_is_havoced_op(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Assign(_, rv) => matches!(
            rv,
            Rvalue::GetStatic(_)
                | Rvalue::GetField { .. }
                | Rvalue::InstanceOf { .. }
                | Rvalue::Call { .. }
                | Rvalue::Havoc(_, _)
                | Rvalue::ArrayLoad { .. }
                | Rvalue::ArrayLength(_)
                | Rvalue::New(_)
                | Rvalue::NewArray { .. }
        ),
        Stmt::PutField { .. } | Stmt::PutStatic { .. } | Stmt::ArrayStore { .. } => true,
        _ => false,
    }
}

// ─── Cooperation options (docs/plans/cooperation-options.md) ───
//
// Each defaults **off**, so the default build is unchanged and each option is
// benchmarked individually against it. The three-levers flags above default
// *on* because those were expected to interact; these four are independent.

/// A — `interval-ai` answers `Want::Bounds` queries from its own fixpoint.
pub fn answers_queries_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_AI_ANSWERS").as_deref() == Ok("1"))
}

/// B — a witness the producing engine knows cannot replay becomes a published
/// fact rather than a silent withholding.
pub fn refute_artifact_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_REFUTE_ARTIFACT").as_deref() == Ok("1"))
}

/// C — the BMC publishes a `Residual` describing what it did not cover.
pub fn residual_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_RESIDUAL").as_deref() == Ok("1"))
}

/// D — nullness as a question kind.
pub fn null_queries_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_NULL_QUERIES").as_deref() == Ok("1"))
}
