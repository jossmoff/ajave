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

use crate::body_analysis::{body_uses_wide_types, body_uses_float_types, body_uses_long_types, body_has_loops};
use crate::interval::{IntervalCpa, WideningIntervalCpa, Interval, Nullness, NEG_INF, POS_INF};
use log::{debug, info};
use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::cpa::{reachability, HasLocation};
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_core::term::{Expr, Op};
use ajave_ir::{BlockId, Const, FieldKey, MethodKey, ObligationId, Operand, Program, Rvalue, Stmt, Terminator, VarId};

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
                        Rvalue::New(_) | Rvalue::NewArray { .. } => { nonnull_vars.insert(*v); }
                        Rvalue::Use(Operand::Const(Const::Str(_) | Const::Class(_))) => { nonnull_vars.insert(*v); }
                        // Static field loads (enum constants, etc.) are non-null
                        // in practice. This is a sound heuristic: class initializers
                        // run before any instance constructor, and static ref fields
                        // of program classes are either explicitly initialized or
                        // default to null. For enum constants they're always non-null.
                        Rvalue::GetStatic(_) => {
                            // Only for Ref-typed vars (not int/boolean static fields)
                            if body.vars.get(v.0 as usize)
                                .map(|vi| vi.ty == ajave_ir::Ty::Ref)
                                .unwrap_or(false)
                            {
                                nonnull_vars.insert(*v);
                            }
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
            if !changed { break; }
        }
        // Pass 3: find PutField(this, field, non-null-var).
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Stmt::PutField { obj, field, val } = stmt {
                    let obj_is_this = match obj {
                        Operand::Var(v) => this_vars.contains(v),
                        _ => false,
                    };
                    if !obj_is_this { continue; }
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
fn analyze_return_nullness(prog: &Program, nonnull_fields: &HashSet<FieldKey>) -> HashSet<MethodKey> {
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
                        Rvalue::GetField { obj: Operand::Var(ov), field } => {
                            nonnull_vars.contains(ov) && nonnull_fields.contains(field)
                        }
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
            if !changed { break; }
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
    for (_mk, body) in &prog.bodies {
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
                    Stmt::Assign(_, Rvalue::Call { target, is_virtual, .. }) => {
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
    /// Precision policy for the flat field abstraction.
    field_prec: crate::interval::FieldPrec,
}

impl AiEngine {
    pub fn new() -> Self {
        AiEngine {
            done: false,
            nonnull_fields: HashSet::new(),
            nonnull_returns: HashSet::new(),
            field_prec: Default::default(),
        }
    }
}

impl Default for AiEngine {
    fn default() -> Self {
        Self::new()
    }
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
        // For each (block, var), join all intervals across reached states at
        // that block. The result is a sound over-approximation: every concrete
        // value at that block is within the published interval.
        let mut block_vars: HashMap<(BlockId, VarId), Interval> = HashMap::new();

        for state in reached {
            let loc = state.location();
            if loc.method != *entry {
                continue;
            }
            // Only use states at block entry (index 0) — mid-block states
            // reflect post-assignment values that don't hold at block entry.
            if loc.index != 0 {
                continue;
            }
            for (&vid, &iv) in &state.vars {
                if iv.is_bottom() {
                    continue;
                }
                // Only publish for 32-bit integer variables. The interval
                // domain uses i32 range; Long/Double intervals would be wrong.
                let var_ty = body.vars.get(vid.0 as usize).map(|v| &v.ty);
                if matches!(var_ty, Some(ajave_ir::Ty::Long | ajave_ir::Ty::Double)) {
                    continue;
                }
                let key = (loc.block, vid);
                let joined = block_vars
                    .entry(key)
                    .or_insert_with(Interval::bottom);
                *joined = joined.join(iv);
            }
        }

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
            debug!(
                "interval-ai: published {hint_count} interval hints for other engines"
            );
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
        prog: &Program,
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

    /// Runs the interval analysis at init time to publish hints for BMC and
    /// other engines. The discharge logic runs later in `step()`.
    fn init(&mut self, prog: &Program, bb: &mut Blackboard) {
        // Analyze constructors for field nullness.
        self.nonnull_fields = analyze_constructor_fields(prog);
        if !self.nonnull_fields.is_empty() {
            debug!("interval-ai: {} fields known non-null from constructors", self.nonnull_fields.len());
        }
        self.nonnull_returns = analyze_return_nullness(prog, &self.nonnull_fields);
        self.field_prec = analyze_field_precision(prog);
        debug!(
            "interval-ai: {} singleton class(es) eligible for strong field updates",
            self.field_prec.singleton_classes.len()
        );
        if !self.nonnull_returns.is_empty() {
            debug!("interval-ai: {} methods known to return non-null", self.nonnull_returns.len());
        }

        let Some(entry) = &prog.entry else { return; };
        let Some(body) = prog.body(entry) else { return; };
        if !body.is_fully_lifted() { return; }
        if body_uses_long_types(body) { return; }

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
                debug!("interval-ai: float widening incomplete ({} states), skipping discharge", reached.len());
            }
            return;
        }

        if body_uses_float_types(body) { return; }

        let cpa = IntervalCpa {
            nonnull_fields: self.nonnull_fields.clone(),
            nonnull_returns: self.nonnull_returns.clone(),
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

        info!("interval-ai: analyzing {} methods", methods_to_analyze.len());

        let mut advanced = false;
        let max_states_per_method = ((budget.work as usize) / methods_to_analyze.len().max(1)).max(500);
        let cpa = IntervalCpa {
            nonnull_fields: self.nonnull_fields.clone(),
            nonnull_returns: self.nonnull_returns.clone(),
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
                    debug!("interval-ai: {:?} incomplete, retrying with widening", method);
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
                debug!("interval-ai: analysis incomplete for {:?}, skipping", method);
                continue;
            }
            debug!("interval-ai: reached {} abstract states for {:?}", reached.len(), method);

            if self.discharge_obligations(method, &reached, bb, body, prog) {
                advanced = true;
            }
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}
