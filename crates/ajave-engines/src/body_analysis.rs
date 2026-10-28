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
/// `AJAVE_SCOPE_ALL_METHODS`. (`AJAVE_ASK_ON_DECLINE` was the third of these
/// and was removed with CEGAR's asker on 2026-10-26 — see #40.)
pub fn obligation_scoping_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_SCOPE_OBLIGATION").as_deref() != Ok("0"))
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
                | Rvalue::New { .. }
                | Rvalue::NewArray { .. }
        ),
        Stmt::PutField { .. } | Stmt::PutStatic { .. } | Stmt::ArrayStore { .. } => true,
        _ => false,
    }
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

/// Which allocation each reference variable holds, **at every program point**.
///
/// Returned as the map in effect *before* statement `idx` of each block, keyed
/// `(BlockId, idx)`, because `interval.rs`'s `transfer` is handed one statement
/// at a time and needs the state that statement runs in.
///
/// # Why this is a dataflow and not a per-variable map
///
/// The first version answered one site per variable for the whole body, matched
/// `Rvalue::New` directly, and was **dead code on every real program**. Two
/// independent reasons, both visible in any lifter dump:
///
/// *The lifter never names the receiver directly.* For `Box a = new Box();
/// a.v = 1;` it emits
///
/// ```text
/// v0 = new Main$Box
/// v2 = v0
/// v1 = v2
/// v5 = v1          <- v5 is the receiver
/// v5.v = 1
/// ```
///
/// so without copy propagation every real receiver resolves to nothing.
///
/// *javac reuses local slots.* In a two-object program `v1` is assigned from
/// **both** allocations, so a flow-insensitive map must drop it as ambiguous —
/// correctly, which is why per-point resolution is required rather than merely
/// nicer.
///
/// Kept separate from `interpolation::array_sites_at_block_entry` rather than
/// generalised over both: the CHC encoders look sites up in a map keyed only by
/// `NewArray` sites, and an object site arriving there hits the silent-drop
/// path that issue #18 was about.
pub fn ref_alloc_sites_at(body: &Body) -> std::collections::BTreeMap<(BlockId, u32), RefSiteMap> {
    use std::collections::BTreeMap;

    let succs = |b: &ajave_ir::Block| -> Vec<BlockId> {
        use ajave_ir::Terminator::*;
        let mut v = match &b.term {
            Goto(t) => vec![*t],
            Branch { then_, else_, .. } => vec![*then_, *else_],
            Switch { cases, default, .. } => {
                let mut c: Vec<_> = cases.iter().map(|(_, t)| *t).collect();
                c.push(*default);
                c
            }
            Return(_) | Throw(_) | Halt | Diverge(_) => vec![],
        };
        v.extend(b.exceptional.iter().map(|e| e.target));
        v
    };

    let mut entry: BTreeMap<BlockId, RefSiteMap> = body
        .blocks
        .iter()
        .map(|b| (b.id, RefSiteMap::new()))
        .collect();
    // `reached` distinguishes "not yet visited" from "visited, knows nothing".
    // Without it the entry block's empty map looks like a predecessor that
    // disagrees with everything and no site ever propagates.
    let mut reached: BTreeMap<BlockId, bool> = body.blocks.iter().map(|b| (b.id, false)).collect();
    reached.insert(body.entry, true);

    for _ in 0..=body.blocks.len() {
        let mut changed = false;
        for b in &body.blocks {
            if !reached[&b.id] {
                continue;
            }
            let mut cur = entry[&b.id].clone();
            for st in &b.stmts {
                update_ref_sites(&mut cur, st);
            }
            for s in succs(b) {
                // Join by agreement: a variable survives only if every
                // predecessor says it holds the *same* site. A disagreement
                // means it names different objects on different paths, so it
                // names none — which is what makes a strong update to the
                // surviving cells sound.
                let merged: RefSiteMap = if reached[&s] {
                    cur.iter()
                        .filter(|(v, site)| entry[&s].get(v) == Some(*site))
                        .map(|(v, site)| (*v, *site))
                        .collect()
                } else {
                    cur.clone()
                };
                if !reached[&s] || merged != entry[&s] {
                    entry.insert(s, merged);
                    reached.insert(s, true);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Expand block entries to per-statement maps.
    let mut out = BTreeMap::new();
    for b in &body.blocks {
        let mut cur = entry[&b.id].clone();
        for (i, st) in b.stmts.iter().enumerate() {
            out.insert((b.id, i as u32), cur.clone());
            update_ref_sites(&mut cur, st);
        }
    }
    out
}

/// `VarId -> AllocSite` for object references at one program point. Absence
/// means "may hold any object", never "holds none".
pub type RefSiteMap = std::collections::BTreeMap<VarId, ajave_ir::AllocSite>;

/// One statement's effect on which object each reference holds.
///
/// Every assignment must be handled, including those that destroy knowledge: a
/// slot reassigned from a field load, a call, or an allocation of a different
/// class no longer holds what it did, and leaving the stale entry is the
/// unsound direction — it would attribute a write to an object the variable no
/// longer points at.
pub fn update_ref_sites(map: &mut RefSiteMap, st: &Stmt) {
    let Stmt::Assign(v, rv) = st else { return };
    match rv {
        Rvalue::New { site, .. } | Rvalue::NewArray { site, .. } => {
            map.insert(*v, *site);
        }
        Rvalue::Use(Operand::Var(w)) => match map.get(w).copied() {
            Some(site) => {
                map.insert(*v, site);
            }
            None => {
                map.remove(v);
            }
        },
        _ => {
            map.remove(v);
        }
    }
}

#[cfg(test)]
mod alloc_site_tests {
    use super::*;
    use ajave_ir::{
        AllocSite, Block, BlockId, Body, Const, Operand, Rvalue, Stmt, Terminator, VarId,
    };

    fn body_blocks(blocks: Vec<Block>) -> Body {
        Body {
            key: ajave_ir::MethodKey {
                class: "Main".into(),
                name: "main".into(),
                desc: "()V".into(),
            },
            entry: BlockId(0),
            blocks,
            vars: Vec::new(),
            obligations: Vec::new(),
            is_static: true,
        }
    }

    fn blk(id: u32, stmts: Vec<Stmt>, term: Terminator) -> Block {
        Block {
            id: BlockId(id),
            stmts,
            term,
            bytecode_offset: 0,
            exceptional: Vec::new(),
        }
    }

    fn body_with(stmts: Vec<Stmt>) -> Body {
        body_blocks(vec![blk(0, stmts, Terminator::Return(None))])
    }

    fn new_at(idx: u32) -> Rvalue {
        Rvalue::New {
            class: "Box".into(),
            site: AllocSite {
                block: BlockId(0),
                index: idx,
            },
        }
    }

    fn copy(from: u32) -> Rvalue {
        Rvalue::Use(Operand::Var(VarId(from)))
    }

    /// Resolve `v` at the point just before statement `idx` of block 0.
    fn at(body: &Body, idx: u32, v: u32) -> Option<u32> {
        ref_alloc_sites_at(body)
            .get(&(BlockId(0), idx))
            .and_then(|m| m.get(&VarId(v)))
            .map(|s| s.index)
    }

    /// **The defect that made B2 and B3 dead code (#104).**
    ///
    /// The lifter never names the receiver directly — it emits
    /// `v0 = new Box; v2 = v0; v1 = v2; v5 = v1; v5.f = ...`. Without copy
    /// propagation every real receiver resolves to nothing, so `site_of`
    /// returned `None` everywhere and the site cells were never populated.
    /// Smoke measured 173 with the feature on and 173 ablated.
    #[test]
    fn a_receiver_reached_through_copies_resolves_to_its_site() {
        let b = body_with(vec![
            Stmt::Assign(VarId(0), new_at(0)),
            Stmt::Assign(VarId(2), copy(0)),
            Stmt::Assign(VarId(1), copy(2)),
            Stmt::Assign(VarId(5), copy(1)),
            Stmt::Assign(VarId(9), Rvalue::Use(Operand::int(0))),
        ]);
        // Before statement 4, the whole copy chain has run.
        assert_eq!(at(&b, 4, 5), Some(0), "the receiver must carry the site");
        assert_eq!(at(&b, 4, 0), Some(0), "and so must the original");
    }

    /// A site is known only *after* its allocation runs. Resolving it earlier
    /// would attribute a write to an object that does not exist yet.
    #[test]
    fn a_site_is_not_known_before_its_allocation() {
        let b = body_with(vec![
            Stmt::Assign(VarId(9), Rvalue::Use(Operand::int(0))),
            Stmt::Assign(VarId(0), new_at(1)),
            Stmt::Assign(VarId(9), Rvalue::Use(Operand::int(1))),
        ]);
        assert_eq!(at(&b, 0, 0), None, "not allocated yet");
        assert_eq!(at(&b, 2, 0), Some(1), "allocated by now");
    }

    /// **Flow sensitivity, the second half of #104.** javac reuses slots, so a
    /// two-object program assigns one variable both allocations. The old
    /// per-variable map had to drop it as ambiguous; per-point resolution keeps
    /// both, which is the whole capability B2 exists for.
    #[test]
    fn a_reused_slot_holds_each_object_at_the_point_it_holds_it() {
        let b = body_with(vec![
            Stmt::Assign(VarId(1), new_at(0)), // v1 = a
            Stmt::Assign(VarId(5), copy(1)),   // v5 = a   (kept)
            Stmt::Assign(VarId(1), new_at(2)), // v1 = b   (slot reused)
            Stmt::Assign(VarId(10), copy(1)),  // v10 = b
            Stmt::Assign(VarId(9), Rvalue::Use(Operand::int(0))),
        ]);
        assert_eq!(at(&b, 4, 5), Some(0), "v5 still holds the first object");
        assert_eq!(at(&b, 4, 10), Some(2), "v10 holds the second");
        assert_eq!(
            at(&b, 4, 1),
            Some(2),
            "and the reused slot holds the latest"
        );
    }

    /// A variable reaching a point from two different allocations names
    /// neither: a strong update through it would be a lie about one of them.
    /// This is the soundness condition the join enforces.
    #[test]
    fn a_variable_reaching_a_point_from_two_sites_resolves_to_nothing() {
        let b = body_blocks(vec![
            blk(
                0,
                vec![],
                Terminator::Branch {
                    cond: Operand::int(1),
                    then_: BlockId(1),
                    else_: BlockId(2),
                },
            ),
            blk(
                1,
                vec![Stmt::Assign(VarId(1), new_at(10))],
                Terminator::Goto(BlockId(3)),
            ),
            blk(
                2,
                vec![Stmt::Assign(VarId(1), new_at(20))],
                Terminator::Goto(BlockId(3)),
            ),
            blk(
                3,
                vec![Stmt::Assign(VarId(9), Rvalue::Use(Operand::int(0)))],
                Terminator::Return(None),
            ),
        ]);
        let m = ref_alloc_sites_at(&b);
        assert!(
            m.get(&(BlockId(3), 0))
                .and_then(|m| m.get(&VarId(1)))
                .is_none(),
            "two allocations reach this point, so the variable names neither"
        );
    }

    /// Both predecessors agreeing is the case that must still resolve — a join
    /// that dropped everything would be sound and useless.
    #[test]
    fn a_variable_both_predecessors_agree_on_still_resolves() {
        let b = body_blocks(vec![
            blk(
                0,
                vec![Stmt::Assign(VarId(1), new_at(7))],
                Terminator::Branch {
                    cond: Operand::int(1),
                    then_: BlockId(1),
                    else_: BlockId(2),
                },
            ),
            blk(1, vec![], Terminator::Goto(BlockId(3))),
            blk(2, vec![], Terminator::Goto(BlockId(3))),
            blk(
                3,
                vec![Stmt::Assign(VarId(9), Rvalue::Use(Operand::int(0)))],
                Terminator::Return(None),
            ),
        ]);
        let m = ref_alloc_sites_at(&b);
        assert_eq!(
            m.get(&(BlockId(3), 0))
                .and_then(|m| m.get(&VarId(1)))
                .map(|s| s.index),
            Some(7),
            "both paths agree, so the site survives the join"
        );
    }

    /// A slot reassigned from something that is not an allocation must lose the
    /// site. Keeping it is the unsound direction: a later write through that
    /// slot would be attributed to an object it no longer points at.
    #[test]
    fn a_slot_reassigned_from_a_non_allocation_loses_its_site() {
        let b = body_with(vec![
            Stmt::Assign(VarId(0), new_at(0)),
            Stmt::Assign(VarId(0), Rvalue::Use(Operand::Const(Const::Null))),
            Stmt::Assign(VarId(9), Rvalue::Use(Operand::int(0))),
        ]);
        assert_eq!(at(&b, 1, 0), Some(0));
        assert_eq!(at(&b, 2, 0), None, "null is not that object");
    }
}
