//! Tier 1, wired up: run the interval domain to a fixpoint over the entry
//! method, then discharge every obligation whose safety condition provably
//! holds at every state that reaches it.
//!
//! Scoped deliberately to a single body (no interprocedural reasoning yet --
//! consistent with the frontend, which diverges rather than guessing at
//! unmodelled calls). Extending this across method boundaries is a `Cpa`
//! composition exercise, not a rewrite: `core::cpa::Product` exists for
//! exactly that.

use std::collections::{HashMap, HashSet};

use crate::body_analysis::{
    answers_queries_enabled, body_has_loops, body_uses_float_types, body_uses_long_types,
};
use crate::interval::{Interval, IntervalCpa, WideningIntervalCpa, NEG_INF, POS_INF};
use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::cpa::{reachability, HasLocation};
use ajave_core::engine::{Budget, Engine, Progress};
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
                        Rvalue::New(_) | Rvalue::NewArray { .. } => {
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
                        Rvalue::New(_) | Rvalue::NewArray { .. } => true,
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
                if let Stmt::Assign(_, Rvalue::New(cls)) = stmt {
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

    crate::interval::FieldPrec {
        singleton_classes,
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
    /// Joined intervals from a **complete** fixpoint, kept so `step` can answer
    /// `Want::Bounds` queries that did not exist when `init` ran.
    ///
    /// Keyed by `(method, var)` and joined over **every** state the variable is
    /// live in, not by program point. Two reasons, and the first is a
    /// measurement: `smt-bmc` posts every query with `index: 0`, and the
    /// variable it asks about is the destination of a call, which has no value
    /// at block entry. Keyed by point, the engine held 32 facts and could
    /// answer none of them.
    ///
    /// Joining over all points is **sound in the direction that matters**: the
    /// result contains the variable's range at every individual point, so it is
    /// wider than the true bound at the asker's point. A wider bound assumed by
    /// the asker removes fewer executions, so a proof over it still holds. The
    /// cost is precision, which is the right way round.
    ///
    /// Empty unless the run converged. A truncated `reached` set
    /// *under*-approximates reachable states, so a join over it can be too
    /// narrow — which would be an unsound bound and the wrong-TRUE direction.
    /// `init` only fills this on `complete`, which is the same gate the hint
    /// path uses and for the same reason.
    answerable: HashMap<(MethodKey, VarId), Interval>,
    /// The same, for float and double variables.
    ///
    /// Kept separate rather than unified because the two domains have different
    /// bounds types and different notions of top, and because the *asker* that
    /// motivated this channel asks about doubles: `smt-bmc` posts a query for
    /// every unmodelled call, and the call that started all of this is
    /// `Math.sin`, whose result is a double. Answering only integers would have
    /// left the one measured asker unserved — which the engine's own
    /// instrumentation showed on the first run: 26 facts held, one query, zero
    /// answerable.
    answerable_fp: HashMap<(MethodKey, VarId), crate::interval::FloatInterval>,
}

/// Join the interval for each `(block, var)` across every reached state.
///
/// Extracted so the hint path and the query answerer cannot disagree about what
/// a published interval means. The result is a sound over-approximation
/// *provided the fixpoint converged*: every concrete value at that block is
/// inside the returned interval. Callers must check `complete` first — a
/// truncated `reached` set under-approximates reachable states, so joining over
/// it can produce an interval that is too narrow.
///
/// Block-entry states only (`index == 0`): a mid-block state reflects values
/// after an assignment, which do not hold on entry to the block.
///
/// 32-bit integers only. The domain's bounds are `i32`, so a `Long` or `Double`
/// interval read out of it would be a claim about a range the analysis never
/// represented.
/// Join a variable's interval over **every** state in the method.
///
/// The per-block joins below answer "what holds on entry to this block", which
/// is what an invariant hint needs. This answers "what range can this variable
/// ever take", which is what a `Want::Bounds` query needs — and is strictly
/// wider, hence sound to hand to an asker whose point we cannot match exactly.
fn join_method_intervals(
    method: &MethodKey,
    reached: &[crate::interval::IState],
    body: &ajave_ir::Body,
) -> HashMap<VarId, Interval> {
    let mut out: HashMap<VarId, Interval> = HashMap::new();
    for state in reached {
        if state.location().method != *method {
            continue;
        }
        for (&vid, &iv) in &state.vars {
            if iv.is_bottom() {
                continue;
            }
            let var_ty = body.vars.get(vid.0 as usize).map(|v| &v.ty);
            if matches!(var_ty, Some(ajave_ir::Ty::Long | ajave_ir::Ty::Double)) {
                continue;
            }
            let j = out.entry(vid).or_insert_with(Interval::bottom);
            *j = j.join(iv);
        }
    }
    out
}

/// The float half of `join_method_intervals`.
fn join_method_float_intervals(
    method: &MethodKey,
    reached: &[crate::interval::IState],
) -> HashMap<VarId, crate::interval::FloatInterval> {
    let mut out: HashMap<VarId, crate::interval::FloatInterval> = HashMap::new();
    for state in reached {
        if state.location().method != *method {
            continue;
        }
        for (&vid, &iv) in &state.float_vars {
            if iv.is_bottom() {
                continue;
            }
            match out.get(&vid).copied() {
                Some(prev) => {
                    out.insert(vid, prev.join(iv));
                }
                None => {
                    out.insert(vid, iv);
                }
            }
        }
    }
    out
}

fn join_block_intervals(
    method: &MethodKey,
    reached: &[crate::interval::IState],
    body: &ajave_ir::Body,
) -> HashMap<(BlockId, VarId), Interval> {
    let mut out: HashMap<(BlockId, VarId), Interval> = HashMap::new();
    for state in reached {
        let loc = state.location();
        if loc.method != *method || loc.index != 0 {
            continue;
        }
        for (&vid, &iv) in &state.vars {
            if iv.is_bottom() {
                continue;
            }
            let var_ty = body.vars.get(vid.0 as usize).map(|v| &v.ty);
            if matches!(var_ty, Some(ajave_ir::Ty::Long | ajave_ir::Ty::Double)) {
                continue;
            }
            let joined = out.entry((loc.block, vid)).or_insert_with(Interval::bottom);
            *joined = joined.join(iv);
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
            answerable: HashMap::new(),
            answerable_fp: HashMap::new(),
        }
    }
}

impl Default for AiEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl AiEngine {
    /// Answer open `Want::Bounds` questions from the stored fixpoint.
    ///
    /// Returns how many were answered. `ranges` answers the same question from
    /// a published JDK contract, so it can only speak about library calls; this
    /// speaks about the program's own variables, which is what an asker that
    /// havoced a value actually needs.
    ///
    /// # Soundness
    ///
    /// `Answer::Bounds` is universal, and this engine is `Over`, so the
    /// direction is already right and the blackboard enforces it at publish.
    /// The load-bearing condition is elsewhere: `answerable` is filled only
    /// from a **complete** fixpoint, because a join over a truncated `reached`
    /// set can be too narrow, and a too-narrow bound assumed by the BMC would
    /// remove real executions — a wrong TRUE.
    ///
    /// An interval at top is answered `Unknown` rather than left open. Saying
    /// "asked and cannot say" stops the scheduler re-asking, which is what the
    /// `Unknown` arm is documented to be for.
    fn answer_bounds_queries(&mut self, bb: &mut Blackboard) -> usize {
        let pending: Vec<(u32, MethodKey, VarId)> = bb
            .unanswered()
            .into_iter()
            .filter(|q| q.want == Want::Bounds)
            .filter_map(|q| match &q.about {
                Expr::Var(v) => Some((q.id, q.at.method.clone(), *v)),
                _ => None,
            })
            .collect();
        if pending.is_empty() {
            return 0;
        }

        let mut answered = 0usize;
        let mut unknown = 0usize;
        for (qid, method, vid) in pending {
            // Keyed by method as well as variable: a `VarId` indexes exactly
            // one `Body`, so answering a question about a method this run did
            // not analyse would be a claim about a different variable that
            // happens to share a number — the id-collision class `CLAUDE.md`
            // records under faults between engines.
            let iv = self
                .answerable
                .get(&(method.clone(), vid))
                .copied()
                .filter(|iv| !iv.is_bottom());

            // A float fact, if the integer domain has nothing. `Expr::double`
            // holds the value as its IEEE-754 bit pattern, which is what makes
            // the claim exact and `Eq`/`Hash`-able.
            let fp = self.answerable_fp.get(&(method.clone(), vid)).copied();

            let answer = match iv {
                Some(iv) if iv.lo > NEG_INF || iv.hi < POS_INF => Answer::Bounds {
                    lo: Expr::Int(iv.lo),
                    hi: Expr::Int(iv.hi),
                },
                _ if fp.is_some_and(|f| f.lo.is_finite() || f.hi.is_finite()) => {
                    let f = fp.expect("checked by the guard");
                    Answer::Bounds {
                        lo: Expr::double(f.lo),
                        hi: Expr::double(f.hi),
                    }
                }
                // Either no fact, or a fact that says nothing. Both are
                // honestly `Unknown`, and publishing it is cheaper than
                // leaving the asker to wait.
                _ => {
                    unknown += 1;
                    Answer::Unknown
                }
            };
            let is_bound = matches!(answer, Answer::Bounds { .. });
            let published = bb.publish(
                self.id(),
                self.direction(),
                Artifact::Lemma(Lemma {
                    query: qid,
                    by: self.id(),
                    answer,
                }),
            );
            if published.is_ok() && is_bound {
                answered += 1;
            }
        }
        // The pre-check the plan asks for, emitted by the implementation rather
        // than run separately: how many questions this engine could actually
        // answer. If `bounded` stays near zero the option is falsified.
        info!(
            "interval-ai: answered {} query(ies) with a bound, {} as unknown \
             ({} int + {} float facts held)",
            answered,
            unknown,
            self.answerable.len(),
            self.answerable_fp.len()
        );
        answered
    }

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
                        at,
                        formula: Expr::bin(Op::And, lo, hi),
                        status: InvStatus::Candidate,
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
        // `QUERY` as well as `STATUS` once this engine answers questions: a
        // query posted by an engine that runs *after* this one would otherwise
        // never wake it, and the answer would never be given. #37 is the same
        // mistake in the other direction — an interest in a kind nobody
        // produces — so both halves of this declaration are worth checking
        // against the producers that actually exist.
        if answers_queries_enabled() {
            Interest::STATUS.union(Interest::QUERY)
        } else {
            Interest::STATUS
        }
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
            let wcpa = WideningIntervalCpa::from_body(body);
            info!("interval-ai: init — float widening analysis on entry method");
            let start = ProgramPoint {
                method: entry.clone(),
                block: body.entry,
                index: 0,
            };
            let (reached, complete) = reachability(&wcpa, prog, &start, (), 2000);
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
        info!("interval-ai: init — running abstract interpretation for hints");
        let start = ProgramPoint {
            method: entry.clone(),
            block: body.entry,
            index: 0,
        };
        let max_states = 1000usize;
        let (reached, complete) = reachability(&cpa, prog, &start, (), max_states);

        if complete {
            self.publish_interval_hints(entry, &reached, bb, body);
            // Kept for the query answerer. Only on `complete`, for the reason
            // stated on the field.
            if answers_queries_enabled() {
                for (vid, iv) in join_method_intervals(entry, &reached, body) {
                    self.answerable.insert((entry.clone(), vid), iv);
                }
                for (vid, iv) in join_method_float_intervals(entry, &reached) {
                    self.answerable_fp.insert((entry.clone(), vid), iv);
                }
            }
        }
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, budget: Budget) -> Progress {
        // Answer first, and on every entry — including entries after `done`.
        //
        // This engine is one-shot for *discharge*, but answering is not the
        // same work: a question posted by an engine further down the portfolio
        // arrives after this one has finished, and the fixpoint that can answer
        // it is already computed and sitting in `answerable`. Returning
        // `Exhausted` before looking would throw away the whole point of the
        // channel.
        let answered = if answers_queries_enabled() {
            self.answer_bounds_queries(bb)
        } else {
            0
        };

        if self.done {
            return if answered > 0 {
                Progress::Advanced
            } else {
                Progress::Exhausted
            };
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
                let wcpa = WideningIntervalCpa::from_body_with(body, cpa.clone());
                info!("interval-ai: using widening CPA for {:?}", method);
                reachability(&wcpa, prog, &start, (), max_states_per_method)
            } else {
                let (r, c) = reachability(&cpa, prog, &start, (), max_states_per_method);
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
                    let mut wcpa = WideningIntervalCpa::from_body_with(body, cpa.clone());
                    // This retry exists precisely because the precise run ran
                    // out of states, so widen almost immediately rather than
                    // spending the budget re-deriving the same divergence.
                    wcpa.widen_delay = 2;
                    // Only loop headers are merged, so the straight-line blocks
                    // between them still hold one state per path; give the
                    // retry enough room for the header states to stabilise.
                    reachability(&wcpa, prog, &start, (), max_states_per_method * 8)
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
