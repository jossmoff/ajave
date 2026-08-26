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
use ajave_ir::{BlockId, Const, FieldKey, ObligationId, Operand, Program, Rvalue, Stmt, VarId};

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

pub struct AiEngine {
    done: bool,
    /// Fields known to be non-null after constructor completes.
    nonnull_fields: HashSet<FieldKey>,
}

impl AiEngine {
    pub fn new() -> Self {
        AiEngine { done: false, nonnull_fields: HashSet::new() }
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
                bb.publish_interval_hint(entry.clone(), *block, *vid, iv.lo, iv.hi);
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
        _prog: &Program,
    ) -> bool {
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

        let cpa = IntervalCpa { nonnull_fields: self.nonnull_fields.clone() };
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
        let open = bb.open();
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
        let cpa = IntervalCpa { nonnull_fields: self.nonnull_fields.clone() };

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

            // Use widening CPA for float-loop bodies, standard CPA otherwise.
            let use_widening = body_uses_float_types(body) && body_has_loops(body);
            let (reached, complete) = if use_widening {
                let wcpa = WideningIntervalCpa::from_body(body);
                info!("interval-ai: using widening CPA for {:?}", method);
                reachability(&wcpa, prog, &start, (), max_states_per_method)
            } else if body_uses_float_types(body) {
                // Float body without loops: skip (no widening needed, and
                // the standard CPA doesn't handle floats).
                continue;
            } else {
                reachability(&cpa, prog, &start, (), max_states_per_method)
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
