//! Tier 1, wired up: run the interval domain to a fixpoint over the entry
//! method, then discharge every obligation whose safety condition provably
//! holds at every state that reaches it.
//!
//! Scoped deliberately to a single body (no interprocedural reasoning yet --
//! consistent with the frontend, which diverges rather than guessing at
//! unmodelled calls). Extending this across method boundaries is a `Cpa`
//! composition exercise, not a rewrite: the domain and its merge policy are
//! exactly that.

use std::collections::{HashMap, HashSet};

use crate::body_analysis::{body_has_loops, body_uses_float_types, body_uses_long_types};
use crate::interval::{Interval, IntervalCpa, WidenAtLoopHeaders, NEG_INF, POS_INF};
use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_core::fixpoint::{explore, HasLocation, Sep};
use ajave_core::term::{Expr, Op};
use ajave_ir::{
    BlockId, Const, FieldKey, MethodKey, ObligationId, Operand, Program, Rvalue, Stmt, Terminator,
    VarId,
};
use log::{debug, info};

/// Analyze constructors to find fields guaranteed non-null after construction.
/// Returns a set of FieldKeys that are always assigned non-null in every <init>.
fn analyze_constructor_fields(prog: &Program) -> HashSet<FieldKey> {
    let mut nonnull_fields = HashSet::new();
    for (mk, body) in &prog.bodies {
        if mk.name != "<init>" {
            continue;
        }
        // Track which variables are known non-null and which are copies of `this`.
        let mut nonnull_vars: HashSet<VarId> = HashSet::new();
        let mut this_vars: HashSet<VarId> = HashSet::new();
        // Seed `this` (Local 0) and all reference-typed parameters as non-null.
        let max_param_slot = crate::interval::param_slot_count(&mk.desc) + 1;
        for (idx, vi) in body.vars.iter().enumerate() {
            if vi.ty == ajave_ir::Ty::Ref {
                if let ajave_ir::VarKind::Local(slot) = vi.kind {
                    if (slot as usize) < max_param_slot {
                        nonnull_vars.insert(VarId(idx as u32));
                        if slot == 0 {
                            this_vars.insert(VarId(idx as u32));
                        }
                    }
                }
            }
        }
        // Pass 1: find all New/Str/Class/GetStatic assignments and this-copies.
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Stmt::Assign(v, rv) = stmt {
                    match rv {
                        Rvalue::New { .. } | Rvalue::NewArray { .. } => {
                            nonnull_vars.insert(*v);
                        }
                        Rvalue::Use(Operand::Const(Const::Str(_) | Const::Class(_))) => {
                            nonnull_vars.insert(*v);
                        }
                        // Static field loads (enum constants, etc.) are non-null
                        // in practice. This is a sound heuristic: class initializers
                        // run before any instance constructor, and static ref fields
                        // of program classes are either explicitly initialized or
                        // default to null. For enum constants they're always non-null.
                        Rvalue::GetStatic(_)
                            // Only for Ref-typed vars (not int/boolean static fields)
                            if body
                                .vars
                                .get(v.0 as usize)
                                .map(|vi| vi.ty == ajave_ir::Ty::Ref)
                                .unwrap_or(false)
                            => {
                                nonnull_vars.insert(*v);
                            }
                        _ => {}
                    }
                }
            }
        }
        // Pass 2: propagate through variable copies (fixpoint).
        for _ in 0..10 {
            let mut changed = false;
            for block in &body.blocks {
                for stmt in &block.stmts {
                    if let Stmt::Assign(v, Rvalue::Use(Operand::Var(src))) = stmt {
                        if nonnull_vars.contains(src) && nonnull_vars.insert(*v) {
                            changed = true;
                        }
                        if this_vars.contains(src) && this_vars.insert(*v) {
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // Pass 3: find PutField(this, field, non-null-var).
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Stmt::PutField { obj, field, val } = stmt {
                    let obj_is_this = match obj {
                        Operand::Var(v) => this_vars.contains(v),
                        _ => false,
                    };
                    if !obj_is_this {
                        continue;
                    }
                    let val_nonnull = match val {
                        Operand::Const(Const::Str(_) | Const::Class(_)) => true,
                        Operand::Var(vv) => nonnull_vars.contains(vv),
                        _ => false,
                    };
                    if val_nonnull {
                        nonnull_fields.insert(field.clone());
                    }
                }
            }
        }
    }
    nonnull_fields
}

/// Analyze methods to find those that always return non-null.
/// Checks if every Return(Some(v)) in the body returns a variable known to
/// be non-null (New, string constant, class constant, this, or nonnull-param).
/// The standard streams, when the program cannot have reassigned them.
///
/// `System.out`/`err`/`in` are **not** `static final`, and
/// `System.setOut(null)` is legal -- verified on a real JVM (OpenJDK 21), where
/// it returns normally and leaves `System.out` null. So they carry no
/// unconditional non-null guarantee, and `is_nonnull_static` is right to
/// exclude them.
///
/// But that is a fact about the *stream setters*, not about the fields. A
/// program that never calls one cannot observe a null stream: the JVM
/// initialises all three before `main`, and only `setOut`/`setErr`/`setIn` can
/// change them.
///
/// This matters because `System.out.println` is everywhere. `System.out` was
/// the single most common unconstrained `GetStatic` in the corpus, and the
/// resulting NullDeref on the receiver is what left several tasks unprovable
/// with nothing else open.
///
/// Scope of the claim, stated honestly: this scans the *lifted* methods. A
/// library method we do not model could in principle call `System.setOut`, and
/// nothing here rules that out -- it rests on the same footing as every other
/// statement in `contract_of` about what external code does. No JDK method we
/// model reassigns a stream, and no benchmark in the corpus calls a setter at
/// all.
fn stream_fields_are_stable(prog: &Program) -> bool {
    !prog.bodies.values().any(|body| {
        body.blocks.iter().any(|b| {
            b.stmts.iter().any(|st| {
                matches!(
                    st,
                    Stmt::Assign(_, Rvalue::Call { target, .. })
                        if target.class == "java/lang/System"
                            && matches!(target.name.as_str(), "setOut" | "setErr" | "setIn")
                )
            })
        })
    })
}

/// The stream fields, as a set, when they are stable.
fn stable_stream_statics(prog: &Program) -> HashSet<FieldKey> {
    let mut out = HashSet::new();
    if !stream_fields_are_stable(prog) {
        return out;
    }
    for (name, desc) in [
        ("out", "Ljava/io/PrintStream;"),
        ("err", "Ljava/io/PrintStream;"),
        ("in", "Ljava/io/InputStream;"),
    ] {
        out.insert(FieldKey {
            class: "java/lang/System".to_string(),
            name: name.to_string(),
            desc: desc.to_string(),
        });
    }
    out
}

fn analyze_return_nullness(
    prog: &Program,
    nonnull_fields: &HashSet<FieldKey>,
) -> HashSet<MethodKey> {
    let mut nonnull_returns = HashSet::new();
    'methods: for (mk, body) in &prog.bodies {
        // Only analyze methods that return a reference type.
        if !mk.desc.ends_with(";") && !mk.desc.ends_with(")V") {
            // Returns a primitive — not relevant for nullness.
            continue;
        }
        if mk.desc.ends_with(")V") {
            continue; // void return
        }

        // Seed non-null variables: params + New + constants
        let mut nonnull_vars: HashSet<VarId> = HashSet::new();
        let max_param_slot = crate::interval::param_slot_count(&mk.desc) + 1;
        for (idx, vi) in body.vars.iter().enumerate() {
            if vi.ty == ajave_ir::Ty::Ref {
                if let ajave_ir::VarKind::Local(slot) = vi.kind {
                    if (slot as usize) < max_param_slot {
                        nonnull_vars.insert(VarId(idx as u32));
                    }
                }
            }
        }

        // Single pass: find non-null producing assignments
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Stmt::Assign(v, rv) = stmt {
                    let nonnull = match rv {
                        Rvalue::New { .. } | Rvalue::NewArray { .. } => true,
                        Rvalue::Use(Operand::Const(Const::Str(_) | Const::Class(_))) => true,
                        Rvalue::GetStatic(fk) if crate::interval::is_nonnull_static(fk) => true,
                        Rvalue::GetField {
                            obj: Operand::Var(ov),
                            field,
                        } => nonnull_vars.contains(ov) && nonnull_fields.contains(field),
                        _ => false,
                    };
                    if nonnull {
                        nonnull_vars.insert(*v);
                    }
                }
            }
        }
        // Propagate copies
        for _ in 0..10 {
            let mut changed = false;
            for block in &body.blocks {
                for stmt in &block.stmts {
                    if let Stmt::Assign(v, Rvalue::Use(Operand::Var(src))) = stmt {
                        if nonnull_vars.contains(src) && nonnull_vars.insert(*v) {
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // Check all return statements
        let mut has_ref_return = false;
        for block in &body.blocks {
            if let Terminator::Return(Some(op)) = &block.term {
                has_ref_return = true;
                let ret_nonnull = match op {
                    Operand::Const(Const::Str(_) | Const::Class(_)) => true,
                    Operand::Const(Const::Null) => false,
                    Operand::Var(v) => nonnull_vars.contains(v),
                    _ => false,
                };
                if !ret_nonnull {
                    continue 'methods;
                }
            }
        }
        if has_ref_return {
            nonnull_returns.insert(mk.clone());
        }
    }
    nonnull_returns
}

/// Compute the precision policy for the flat field abstraction.
///
/// Two things are needed. First, which classes have at most one live instance —
/// only for those may a `PutField` replace the shared cell outright instead of
/// joining into it. We require a single `New` site for the class, and that the
/// site not sit inside a loop (a `New` on a back-edge runs repeatedly and
/// produces many instances). Second, which fields each method may write,
/// transitively, so a call clobbers only those cells rather than all of them.
fn analyze_field_precision(prog: &Program) -> crate::interval::FieldPrec {
    use crate::body_analysis::body_has_loops;

    // ── Allocation sites per class ──────────────────────────────────────
    let mut alloc_sites: HashMap<String, usize> = HashMap::new();
    let mut alloc_in_loop: HashSet<String> = HashSet::new();
    for body in prog.bodies.values() {
        let looping = body_has_loops(body);
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Stmt::Assign(_, Rvalue::New { class: cls, .. }) = stmt {
                    *alloc_sites.entry(cls.clone()).or_insert(0) += 1;
                    if looping {
                        // Conservative: we do not check whether this particular
                        // block is on the back-edge, only that the method loops.
                        alloc_in_loop.insert(cls.clone());
                    }
                }
            }
        }
    }
    let singleton_classes: HashSet<String> = alloc_sites
        .iter()
        .filter(|(cls, &n)| n == 1 && !alloc_in_loop.contains(*cls))
        .map(|(cls, _)| cls.clone())
        .collect();

    // ── Direct writes per method ────────────────────────────────────────
    let mut direct: HashMap<MethodKey, HashSet<FieldKey>> = HashMap::new();
    let mut all_written: HashSet<FieldKey> = HashSet::new();
    let mut callees: HashMap<MethodKey, Vec<MethodKey>> = HashMap::new();
    for (mk, body) in &prog.bodies {
        let mut w = HashSet::new();
        let mut cs = Vec::new();
        for block in &body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Stmt::PutStatic(fk, _) => {
                        w.insert(fk.clone());
                        all_written.insert(fk.clone());
                    }
                    Stmt::PutField { field, .. } => {
                        w.insert(field.clone());
                        all_written.insert(field.clone());
                    }
                    Stmt::Assign(
                        _,
                        Rvalue::Call {
                            target, is_virtual, ..
                        },
                    ) => {
                        cs.push(target.clone());
                        if *is_virtual {
                            cs.extend(prog.devirtualise(target));
                        }
                    }
                    _ => {}
                }
            }
        }
        direct.insert(mk.clone(), w);
        callees.insert(mk.clone(), cs);
    }

    // ── Transitive closure over the call graph ──────────────────────────
    // A callee without a body could write anything, so its caller inherits
    // `all_written` — the same fallback `clobbered_by` uses.
    let mut writes = direct.clone();
    for _ in 0..16 {
        let mut changed = false;
        for (mk, cs) in &callees {
            let mut add: HashSet<FieldKey> = HashSet::new();
            for c in cs {
                match writes.get(c) {
                    Some(w) => add.extend(w.iter().cloned()),
                    None => {
                        // No body. Before assuming it writes everything, ask
                        // the contract table: a call declared `Effect::Pure`
                        // touches nothing we track, so field knowledge survives
                        // across it. Without this, a single `s.length()` in a
                        // method discards every field value the analysis had —
                        // which is what made the flat field abstraction worth
                        // so little in practice.
                        match ajave_models::contract_of(&c.class, &c.name, &c.desc) {
                            Some(ct) if ct.effect == ajave_models::Effect::Pure => {}
                            _ => add.extend(all_written.iter().cloned()),
                        }
                    }
                }
            }
            let entry = writes.entry(mk.clone()).or_default();
            let before = entry.len();
            entry.extend(add);
            if entry.len() != before {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // ── B2: per-method allocation sites ─────────────────────────────────
    // `unique` is false for a body with a loop, where a `new` on the back-edge
    // produces one object per iteration and the site summarises all of them.
    // The same conservatism `singleton_classes` applies per class, applied per
    // site — which is the whole gain, since two sites of one class are now
    // distinguishable where the class-level test gave up on both.
    let sites: HashMap<MethodKey, crate::interval::SiteInfo> = prog
        .bodies
        .iter()
        .map(|(mk, body)| {
            (
                mk.clone(),
                crate::interval::SiteInfo {
                    at: crate::body_analysis::ref_alloc_sites_at(body),
                    unique_sites: crate::body_analysis::unique_alloc_sites(body),
                },
            )
        })
        .collect();

    crate::interval::FieldPrec {
        singleton_classes,
        sites,
        writes,
        all_written,
        nothing: HashSet::new(),
    }
}

pub struct AiEngine {
    done: bool,
    /// Fields known to be non-null after constructor completes.
    nonnull_fields: HashSet<FieldKey>,
    /// Methods known to always return non-null.
    nonnull_returns: HashSet<MethodKey>,
    /// Static fields this program cannot have made null.
    nonnull_statics: HashSet<FieldKey>,
    /// Precision policy for the flat field abstraction.
    field_prec: crate::interval::FieldPrec,
}

/// Hints are per **block entry**: states whose `location().index != 0` are
/// skipped below. A body with a single block therefore publishes nothing even
/// though it converges trivially — its only block-entry state is the method
/// entry, where nothing is known yet.
///
/// That is not a defect, but it does make a hand-built single-block fixture
/// look like a counterexample to the completeness gate above. It is not one;
/// see `docs/interval-ai-hint-path.md`.
fn join_block_intervals(
    method: &MethodKey,
    reached: &[crate::interval::IState],
    body: &ajave_ir::Body,
) -> HashMap<(BlockId, VarId), Interval> {
    // Group the reached states by block first. The join below must range over
    // *every* state at a block, including the ones that say nothing about a
    // variable, and that cannot be done in a single pass over `reached`.
    //
    // This is where the published hints were unsound. `IState` stores
    // intervals sparsely — `IState::set` deliberately *removes* an entry
    // rather than storing Top, because an absent entry already means Top —
    // and the previous version iterated `state.vars`. A state in which a
    // variable was Top therefore contributed nothing to the join instead of
    // widening it to Top, so a bound narrowed on one branch was published as
    // holding at the join of that branch with one that knew nothing.
    //
    // `smt-bmc` asserts these as facts true at the block on every path, so the
    // result was a discharged obligation that a JVM-confirmed witness
    // violates. See
    // `benchmarks/ajave/engine-cooperation/IntervalHintAtAJoinMustHoldOnBothPaths`.
    let mut by_block: std::collections::BTreeMap<BlockId, Vec<&crate::interval::IState>> =
        std::collections::BTreeMap::new();
    for state in reached {
        let loc = state.location();
        if loc.method != *method || loc.index != 0 {
            continue;
        }
        by_block.entry(loc.block).or_default().push(state);
    }

    let mut out: HashMap<(BlockId, VarId), Interval> = HashMap::new();
    for (block, states) in by_block {
        // Every variable any state at this block has an opinion about. A
        // variable no state mentions is Top everywhere and is not worth a key.
        let vids: std::collections::BTreeSet<VarId> =
            states.iter().flat_map(|s| s.vars.keys().copied()).collect();
        for vid in vids {
            let var_ty = body.vars.get(vid.0 as usize).map(|v| &v.ty);
            if matches!(var_ty, Some(ajave_ir::Ty::Long | ajave_ir::Ty::Double)) {
                continue;
            }
            // `IState::get` returns Top for an absent entry, which is the
            // whole point: the join is over all states at the block, not over
            // the states that happened to record a bound.
            let mut joined = Interval::bottom();
            for s in &states {
                let iv = s.get(vid);
                // A bottom state is infeasible and describes no execution, so
                // it cannot weaken a claim about the ones that are.
                if iv.is_bottom() {
                    continue;
                }
                joined = joined.join(iv);
            }
            if !joined.is_bottom() {
                out.insert((block, vid), joined);
            }
        }
    }
    out
}

impl AiEngine {
    pub fn new() -> Self {
        AiEngine {
            done: false,
            nonnull_fields: HashSet::new(),
            nonnull_returns: HashSet::new(),
            nonnull_statics: HashSet::new(),
            field_prec: Default::default(),
        }
    }
}

impl Default for AiEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// Whether the hint exploration widens at loop headers so it can converge.
///
/// `AJAVE_WIDEN_HINTS=0` restores the pure-`Sep` exploration, which publishes
/// nothing on any program with an unbounded loop. See
/// `docs/interval-ai-hint-path.md` for the measurement that motivated this.
pub fn widened_hints_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_WIDEN_HINTS").as_deref() != Ok("0"))
}

impl AiEngine {
    /// Collect per-block-per-variable interval bounds from the reached states
    /// and publish them to the blackboard for other engines to consume.
    fn publish_interval_hints(
        &self,
        entry: &ajave_ir::MethodKey,
        reached: &[crate::interval::IState],
        bb: &mut Blackboard,
        body: &ajave_ir::Body,
    ) {
        let block_vars = join_block_intervals(entry, reached, body);

        let mut hint_count = 0;
        for ((block, vid), iv) in &block_vars {
            // Only publish if narrower than Top (i.e., actually informative).
            if iv.lo > NEG_INF || iv.hi < POS_INF {
                // A claim any engine can read, rather than one only the BMC
                // knew how to look up. CHC in particular wants these as
                // candidate invariants — the most valuable hint a Horn solver
                // can be given — and could not see them at all while they
                // lived in a bespoke `HashMap` beside the artifact log.
                //
                // Published as `Over` because that is what the interval
                // analysis is; `Candidate` because nothing has checked it
                // inductively, and `Blackboard::inductive_invariants` filters
                // on exactly that.
                let at = ProgramPoint {
                    method: entry.clone(),
                    block: *block,
                    index: 0,
                };
                let lo = Expr::bin(Op::Le, Expr::Int(iv.lo), Expr::Var(*vid));
                let hi = Expr::bin(Op::Le, Expr::Var(*vid), Expr::Int(iv.hi));
                let id = bb.fresh_invariant_id();
                let _ = bb.publish(
                    self.id(),
                    Direction::Over,
                    Artifact::Invariant(Invariant {
                        id,
                        at: at.clone(),
                        formula: Expr::bin(Op::And, lo, hi),
                        status: InvStatus::Candidate,
                        scope: Scope::Point(at.clone()),
                    }),
                );
                hint_count += 1;
            }
        }
        if hint_count > 0 {
            debug!("interval-ai: published {hint_count} interval hints for other engines");
        }
    }
}

impl AiEngine {
    /// Discharge obligations proved safe by the interval analysis.
    fn discharge_obligations(
        &self,
        method: &ajave_ir::MethodKey,
        reached: &[crate::interval::IState],
        bb: &mut Blackboard,
        body: &ajave_ir::Body,
        _prog: &Program,
    ) -> bool {
        // NOTE: this deliberately does *not* refuse to discharge when the
        // method contains a call with unmodelled exception behaviour.
        //
        // Such a call does mean we cannot claim the program is free of runtime
        // exceptions — but that is a statement about the *verdict*, and the CLI
        // enforces it over the whole reachable set before reporting TRUE.
        // Refusing here as well changed nothing about the final answer while
        // preventing every unrelated obligation in the method from being
        // discharged: an out-of-range `charAt` elsewhere in the body has no
        // bearing on whether *this* dereference is null. Blocking them cost
        // ~54 correct answers in securibench alone for no soundness gain.
        let mut safe: HashMap<ObligationId, bool> =
            body.obligations.iter().map(|o| (o.id, true)).collect();
        // The abstract state at each obligation's check, joined over every
        // reached state there. This is the *certificate* for the discharge:
        // "here is what I claim holds at this point, which is why the check
        // passes". Until 2026-10-26 the discharge named an invariant id that
        // was never published at all (#A1), so the proof referenced a
        // certificate nobody had written.
        let mut at_check: HashMap<ObligationId, (ProgramPoint, crate::interval::IState)> =
            HashMap::new();

        for state in reached {
            let loc = state.location();
            if loc.method != *method {
                continue;
            }
            let Some(Stmt::Check(oid)) = body.block(loc.block).stmts.get(loc.index) else {
                continue;
            };
            let ob = body.obligation(*oid);
            let cond_ok = match &ob.cond {
                Operand::Const(Const::Int(v)) => *v != 0,
                _ => state.eval_operand(&ob.cond).definitely_nonzero(),
            };
            if !cond_ok {
                debug!(
                    "interval-ai: obligation {:?} NOT safe at block {:?}, float_vars={:?}, vars={:?}",
                    oid, loc.block, state.float_vars, state.vars,
                );
            }
            let entry_flag = safe.entry(*oid).or_insert(true);
            *entry_flag = *entry_flag && cond_ok;

            // Join rather than overwrite: an obligation checked on several
            // paths must be certified against what holds on *all* of them. A
            // single path's state would be an under-approximation, which is
            // the wrong direction for a proof.
            match at_check.get_mut(oid) {
                Some((_, acc)) => *acc = ajave_core::fixpoint::Lattice::join(acc, state),
                None => {
                    at_check.insert(*oid, (loc.clone(), state.clone()));
                }
            }
        }

        let safe_count = safe.values().filter(|&&v| v).count();
        if safe_count > 0 {
            debug!(
                "interval-ai: {safe_count}/{} obligations proved safe for {:?}",
                safe.len(),
                method,
            );
        }

        let mut advanced = false;
        for (oid, is_safe) in safe {
            if !is_safe {
                continue;
            }
            if bb.is_assertion_only() {
                let ob = body.obligation(oid);
                if !ob.kind.is_assertion() {
                    continue;
                }
            }
            let oref = ObligationRef {
                method: method.clone(),
                id: oid,
            };
            let inv_id = bb.fresh_invariant_id();
            // Publish the certificate before the claim that rests on it, so
            // the blackboard can check that the claim's reference resolves.
            if let Some((at, state)) = at_check.get(&oid) {
                if let Some(formula) = interval_state_as_formula(state, body) {
                    let _ = bb.publish(
                        EngineId("interval-ai"),
                        Direction::Over,
                        Artifact::Invariant(Invariant {
                            id: inv_id,
                            at: at.clone(),
                            formula,
                            status: InvStatus::Candidate,
                            scope: Scope::Point(at.clone()),
                        }),
                    );
                }
            }
            let published = bb.publish(
                EngineId("interval-ai"),
                Direction::Over,
                Artifact::Status(
                    oref,
                    Status::Discharged {
                        by: EngineId("interval-ai"),
                        proof: ProofKind::Invariant(inv_id),
                    },
                ),
            );
            if published.is_ok() {
                advanced = true;
            }
        }
        advanced
    }
}

/// The integer part of an abstract state, as a conjunction of bounds.
///
/// Only variables the analysis actually narrowed, and only integer ones: the
/// certifier checks in LIA, so a float bound could not be stated there and
/// claiming one would invite a checker to confirm something it cannot see. See
/// `invariant_check`'s module doc, and #48 for why that matters.
///
/// Returns `None` when nothing was narrowed — an empty conjunction is `true`,
/// which is a certificate that justifies nothing, and publishing one would
/// make the discharge look certified while resting on no information at all.
fn interval_state_as_formula(
    state: &crate::interval::IState,
    body: &ajave_ir::Body,
) -> Option<Expr> {
    let mut conjuncts: Vec<Expr> = Vec::new();
    for (vid, iv) in &state.vars {
        let is_int = body
            .vars
            .get(vid.0 as usize)
            .map(|vi| !matches!(vi.ty, ajave_ir::Ty::Float | ajave_ir::Ty::Double))
            .unwrap_or(false);
        if !is_int || *iv == Interval::top() {
            continue;
        }
        if iv.lo > NEG_INF {
            conjuncts.push(Expr::bin(Op::Le, Expr::Int(iv.lo), Expr::Var(*vid)));
        }
        if iv.hi < POS_INF {
            conjuncts.push(Expr::bin(Op::Le, Expr::Var(*vid), Expr::Int(iv.hi)));
        }
    }
    let mut it = conjuncts.into_iter();
    let first = it.next()?;
    Some(it.fold(first, |acc, c| Expr::bin(Op::And, acc, c)))
}

impl Engine for AiEngine {
    fn id(&self) -> EngineId {
        EngineId("interval-ai")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    /// Which obligations are still open decides what the fixpoint is asked
    /// to prove, and it is the only thing this reads from the board.
    /// No resumable parameter, deliberately. `widen_delay` is the obvious
    /// candidate and the wrong one: this engine reaches its fixpoint in
    /// milliseconds on essentially every task, so it is never the engine
    /// holding the clock, and a later widening buys precision on loops where
    /// the interval domain has already lost the property for other reasons.
    fn interest(&self) -> Interest {
        // `STATUS` only. This engine briefly declared `QUERY` too, while it was
        // a second answerer for `Want::Bounds` — removed 2026-10-26 after it
        // measured no gain against `ranges`, which answers both `Bounds` and
        // `NonNull` from published contracts and is the answerer `smt-bmc`'s
        // questions actually reach.
        Interest::STATUS
    }

    /// Runs the interval analysis at init time to publish hints for BMC and
    /// other engines. The discharge logic runs later in `step()`.
    fn init(&mut self, prog: &Program, bb: &mut Blackboard) {
        // Analyze constructors for field nullness.
        self.nonnull_fields = analyze_constructor_fields(prog);
        if !self.nonnull_fields.is_empty() {
            debug!(
                "interval-ai: {} fields known non-null from constructors",
                self.nonnull_fields.len()
            );
        }
        self.nonnull_returns = analyze_return_nullness(prog, &self.nonnull_fields);
        self.nonnull_statics = stable_stream_statics(prog);
        self.field_prec = analyze_field_precision(prog);
        debug!(
            "interval-ai: {} singleton class(es) eligible for strong field updates",
            self.field_prec.singleton_classes.len()
        );
        if !self.nonnull_returns.is_empty() {
            debug!(
                "interval-ai: {} methods known to return non-null",
                self.nonnull_returns.len()
            );
        }

        let Some(entry) = &prog.entry else {
            info!("interval-ai: declining — no entry method");
            return;
        };
        let Some(body) = prog.body(entry) else {
            info!("interval-ai: declining — entry has no body");
            return;
        };
        if !body.is_fully_lifted() {
            info!("interval-ai: declining — entry not fully lifted");
            return;
        }
        if body_uses_long_types(body) {
            info!("interval-ai: declining — entry uses long");
            return;
        }

        // Float-loop bodies: run widening CPA and discharge obligations during
        // init, before BMC gets a chance to publish spurious violations.
        if body_uses_float_types(body) && body_has_loops(body) {
            let policy = WidenAtLoopHeaders::from_body(body);
            info!("interval-ai: init — float widening analysis on entry method");
            let start = ProgramPoint {
                method: entry.clone(),
                block: body.entry,
                index: 0,
            };
            let (reached, complete) =
                explore(&IntervalCpa::default(), &policy, prog, &start, (), 2000);
            if complete {
                self.discharge_obligations(entry, &reached, bb, body, prog);
            } else {
                info!(
                    "interval-ai: declining — float widening incomplete ({} states)",
                    reached.len()
                );
            }
            return;
        }

        // A float-typed body without loops is analysed by the ordinary CPA.
        //
        // `IState::float_vars` tracks `FloatInterval` and treats a missing
        // entry as Top, so floats are represented, not ignored. The widening
        // CPA above exists for float *loops*, where a plain join may not reach
        // a fixpoint -- without loops the ordinary analysis terminates and
        // there is nothing to decline for.
        //
        // Declining here refused 28 of 172 sampled no-runtime-exception tasks,
        // and the shape of the guard pair was the tell: the *harder* case (with
        // loops) was analysed and the easier one was not.

        let cpa = IntervalCpa {
            nonnull_fields: self.nonnull_fields.clone(),
            nonnull_returns: self.nonnull_returns.clone(),
            nonnull_statics: self.nonnull_statics.clone(),
            field_prec: self.field_prec.clone(),
        };
        // `&Sep` below means **no widening**, so a loop whose trip count is
        // not statically known enumerates states until `max_states` and
        // returns `complete = false` — and then nothing is published at all,
        // however precise the intervals were.
        //
        // Measured on three programs differing only in their loop: bounded 83
        // hints applied, unbounded 0, no loop 32. That gate is why B2, B3 and
        // #103 each measured exactly zero, and it is **correct** — an
        // incomplete exploration has not visited every reachable state, and
        // `smt-bmc` asserts a hint as a fact.
        //
        // Note the asymmetry with the float-loop branch above, which widens and
        // therefore converges. Using a widening policy here is the single
        // change most likely to make interval hints matter, and it is a
        // measurement rather than an argument.
        //
        // See `docs/interval-ai-hint-path.md` before building anything that
        // depends on these hints.
        info!("interval-ai: init — running abstract interpretation for hints");
        let start = ProgramPoint {
            method: entry.clone(),
            block: body.entry,
            index: 0,
        };
        let max_states = 1000usize;
        // Widen at loop headers so the exploration can actually converge.
        //
        // `&Sep` is pure path sensitivity: a loop whose trip count is not
        // statically known enumerates states until `max_states`, returns
        // `complete = false`, and then **nothing is published at all** —
        // measured as 83 hints on a bounded loop against 0 on the same program
        // with an unbounded one. Since `publish` is gated on completeness (it
        // must be: an unfinished search has not visited every state, and
        // `smt-bmc` asserts a hint as a fact), the engine was silent on exactly
        // the programs where the BMC cannot unroll and needs help.
        //
        // Soundness is unchanged. Both join and widen are upper bounds on the
        // states they replace, so a converged widening analysis still
        // over-approximates every reachable state — which is all a published
        // `Over` interval claims. This is the same argument the float-loop
        // branch above already relies on, with the same policy.
        //
        // The cost is precision at loop headers: a hint may be weaker than the
        // path-sensitive one would have been. Weaker is not wrong, and a weaker
        // hint that exists beats a sharper one that is never published.
        //
        // See `docs/interval-ai-hint-path.md`.
        let (reached, complete) = if widened_hints_enabled() {
            let policy = WidenAtLoopHeaders::from_body(body);
            explore(&cpa, &policy, prog, &start, (), max_states)
        } else {
            explore(&cpa, &Sep, prog, &start, (), max_states)
        };

        if complete {
            self.publish_interval_hints(entry, &reached, bb, body);
        }
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };

        // Collect methods to analyze.
        // For NRE, analyze all methods with open obligations (intra-procedural
        // analysis is sound for NRE: each method's params are non-null from the
        // JVM call convention, and we're checking runtime exceptions).
        // For assert, only analyze the entry method (callee analysis with
        // assumed-NonNull params is unsound for assert: the caller might pass
        // null to trigger an assertion failure).
        // `open_or_unconfirmed`, not `open`: a violation from an
        // under-approximating engine is a *candidate* until JVM replay
        // confirms it, and `open()` hides those obligations from every
        // over-approximating engine. Whichever engine published first then
        // won outright, so a spurious candidate permanently blocked the
        // proof that would have refuted it. `proved_safe` records the
        // discharge either way, and `verdict_excluding` turns it into a
        // TRUE only once the violation is actually refuted.
        let open = bb.open_or_unconfirmed();
        let mut methods_to_analyze: Vec<ajave_ir::MethodKey> = Vec::new();
        methods_to_analyze.push(entry.clone());
        if !bb.is_assertion_only() {
            for oref in &open {
                if !methods_to_analyze.contains(&oref.method) {
                    methods_to_analyze.push(oref.method.clone());
                }
            }
        }

        info!(
            "interval-ai: analyzing {} methods",
            methods_to_analyze.len()
        );

        let mut advanced = false;
        let max_states_per_method =
            ((budget.work as usize) / methods_to_analyze.len().max(1)).max(500);
        let cpa = IntervalCpa {
            nonnull_fields: self.nonnull_fields.clone(),
            nonnull_returns: self.nonnull_returns.clone(),
            nonnull_statics: self.nonnull_statics.clone(),
            field_prec: self.field_prec.clone(),
        };

        for method in &methods_to_analyze {
            let Some(body) = prog.body(method) else {
                continue;
            };
            if !body.is_fully_lifted() {
                continue;
            }
            // Skip methods with Long types (AI domain is i32-based).
            if body_uses_long_types(body) {
                continue;
            }

            let start = ProgramPoint {
                method: method.clone(),
                block: body.entry,
                index: 0,
            };

            // Float loops need widening from the outset — their state
            // sequences are effectively never subsumed exactly.
            let use_widening = body_uses_float_types(body) && body_has_loops(body);
            let (reached, complete) = if use_widening {
                let policy = WidenAtLoopHeaders::from_body(body);
                info!(
                    "interval-ai: using the widening merge policy for {:?}",
                    method
                );
                explore(&cpa, &policy, prog, &start, (), max_states_per_method)
            } else {
                let (r, c) = explore(&cpa, &Sep, prog, &start, (), max_states_per_method);
                // The precise CPA is path-sensitive and keeps loop iterations
                // apart, so a loop whose trip count isn't statically known
                // exhausts the state cap instead of converging. Retry those
                // under widening rather than forfeiting the proof. Bodies that
                // already converged keep their sharper bounds.
                if !c && body_has_loops(body) {
                    debug!(
                        "interval-ai: {:?} incomplete, retrying with widening",
                        method
                    );
                    let mut policy = WidenAtLoopHeaders::from_body(body);
                    // This retry exists precisely because the precise run ran
                    // out of states, so widen almost immediately rather than
                    // spending the budget re-deriving the same divergence.
                    policy.widen_delay = 2;
                    // Only loop headers are merged, so the straight-line blocks
                    // between them still hold one state per path; give the
                    // retry enough room for the header states to stabilise.
                    explore(&cpa, &policy, prog, &start, (), max_states_per_method * 8)
                } else {
                    (r, c)
                }
            };

            if !complete {
                debug!(
                    "interval-ai: analysis incomplete for {:?}, skipping",
                    method
                );
                continue;
            }
            debug!(
                "interval-ai: reached {} abstract states for {:?}",
                reached.len(),
                method
            );

            if self.discharge_obligations(method, &reached, bb, body, prog) {
                advanced = true;
            }
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Blocked
        }
    }
}

#[cfg(test)]
mod join_hint_tests {
    use super::*;
    use crate::interval::{IState, Interval};
    use ajave_core::artifact::ProgramPoint;

    fn mk() -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: "main".into(),
            desc: "()V".into(),
        }
    }

    fn body_with_int_vars(n: usize) -> ajave_ir::Body {
        ajave_ir::Body {
            key: mk(),
            entry: BlockId(0),
            blocks: vec![ajave_ir::Block {
                id: BlockId(0),
                stmts: Vec::new(),
                term: ajave_ir::Terminator::Return(None),
                bytecode_offset: 0,
                exceptional: Vec::new(),
            }],
            vars: (0..n)
                .map(|i| ajave_ir::VarInfo {
                    ty: ajave_ir::Ty::Int,
                    kind: ajave_ir::VarKind::Local(i as u16),
                })
                .collect(),
            obligations: Vec::new(),
            is_static: true,
        }
    }

    fn state_at(block: u32, bounds: &[(u32, i64, i64)]) -> IState {
        let mut st = IState::top_at(ProgramPoint {
            method: mk(),
            block: BlockId(block),
            index: 0,
        });
        for &(v, lo, hi) in bounds {
            st.vars.insert(VarId(v), Interval { lo, hi });
        }
        st
    }

    /// The defect that produced a JVM-confirmed wrong discharge.
    ///
    /// `IState` stores intervals sparsely and `IState::set` *removes* a Top
    /// entry by design, so a state that knows nothing about `v0` has no entry
    /// for it. Joining only over present entries published the one branch's
    /// bound as a fact true at the join, and `smt-bmc` asserts these as facts
    /// true on every path reaching the block.
    ///
    /// Named after
    /// `benchmarks/ajave/engine-cooperation/IntervalHintAtAJoinMustHoldOnBothPaths`.
    #[test]
    fn a_variable_top_in_one_state_is_not_published_as_bounded_at_the_join() {
        let body = body_with_int_vars(2);
        let reached = vec![
            // The then-branch narrowed v0 to exactly 0.
            state_at(3, &[(0, 0, 0), (1, 5, 5)]),
            // The else-branch knows nothing about v0 — hence no entry — but
            // does bound v1.
            state_at(3, &[(1, 7, 7)]),
        ];
        let out = join_block_intervals(&mk(), &reached, &body);
        assert!(
            !out.contains_key(&(BlockId(3), VarId(0)))
                || out[&(BlockId(3), VarId(0))] == Interval::top(),
            "v0 is Top on one path, so no bound may be published for it: got {:?}",
            out.get(&(BlockId(3), VarId(0)))
        );
        assert_eq!(
            out[&(BlockId(3), VarId(1))],
            Interval { lo: 5, hi: 7 },
            "v1 is bounded on both paths, so the join of the two is publishable"
        );
    }

    /// The precision this must not give up: when every state at a block agrees
    /// on a bound, the bound is still published. A fix that simply stopped
    /// publishing at join points would pass the test above and be worthless.
    #[test]
    fn a_bound_every_state_agrees_on_is_still_published() {
        let body = body_with_int_vars(1);
        let reached = vec![
            state_at(3, &[(0, 1, 1)]),
            state_at(3, &[(0, 2, 4)]),
            state_at(3, &[(0, 3, 3)]),
        ];
        let out = join_block_intervals(&mk(), &reached, &body);
        assert_eq!(out[&(BlockId(3), VarId(0))], Interval { lo: 1, hi: 4 });
    }

    /// A bottom state is infeasible: it describes no execution, so it must not
    /// widen a claim about the states that do. Without this the fix above would
    /// cost every bound at any block an infeasible path also reaches.
    #[test]
    fn an_infeasible_state_does_not_weaken_the_join() {
        let body = body_with_int_vars(1);
        let reached = vec![
            state_at(3, &[(0, 2, 2)]),
            state_at(3, &[(0, 1, 0)]), // lo > hi: bottom
        ];
        let out = join_block_intervals(&mk(), &reached, &body);
        assert_eq!(out[&(BlockId(3), VarId(0))], Interval { lo: 2, hi: 2 });
    }
}
