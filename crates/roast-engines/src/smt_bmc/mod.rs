//! SMT-backed bounded model checker.
//!
//! Encodes paths symbolically and asks a solver for satisfying assignments,
//! replacing the concrete engine's "enumerate, don't solve" with "solve, don't
//! enumerate". Finds any bug reachable within bounded depth for arbitrary
//! integer/long inputs, not just a fixed candidate pool.
//!
//! Direction: Under. JvmReplay confirms all witnesses.

mod encode;
mod explore;
mod merge;
mod str_encode;

use std::collections::{HashMap, HashSet};

use log::{debug, info, warn};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_core::smt::{SatResult, Solver, SolverFactory, Term};
use roast_ir::verdict::{NondetEntry, NondetValue, Witness};
use roast_ir::*;
use roast_models;

/// Triple key for field identification: (class, name, desc).
type FK = (String, String, String);

/// Maximum number of solver check-sat calls per run to prevent hangs.
const MAX_SOLVER_CALLS: u32 = 10_000;

/// Maximum number of violations to collect before stopping exploration.
const MAX_VIOLATIONS: usize = 50;

/// Maximum call inlining depth to prevent infinite recursion.
const MAX_CALL_DEPTH: u32 = 10;

/// Maximum number of times a loop back-edge may be taken on a single path.
const MAX_LOOP_UNROLL: u32 = 5;

/// Maximum total block visits across all paths. Prevents exponential blowup
/// from loops with internal branches: e.g. 5 unrolls × 3 branches per
/// iteration = 2^15 paths, each visiting ~10 blocks = 320k visits.
const MAX_BLOCK_VISITS: u64 = 50_000;

/// Maximum number of path forks. Path forking (as opposed to diamond merging)
/// doubles the work at each fork. This limit prevents exponential blowup.
const MAX_FORKS: u32 = 500;

pub struct SmtBmc {
    factory: Box<dyn SolverFactory>,
    max_depth: u32,
    done: bool,
}

impl SmtBmc {
    pub fn new(factory: Box<dyn SolverFactory>, max_depth: u32) -> Self {
        SmtBmc {
            factory,
            max_depth,
            done: false,
        }
    }
}

impl Engine for SmtBmc {
    fn id(&self) -> EngineId {
        EngineId("smt-bmc")
    }

    fn direction(&self) -> Direction {
        // Exact, because this engine is sound in both directions and uses both:
        //
        //  * A violation comes with a satisfying assignment, which becomes a
        //    witness and is replayed on a real JVM. That is under-approximating
        //    reasoning, published as `Under`.
        //  * A discharge is published only when `all_paths_complete` holds and
        //    no budget was exhausted -- every path through the body was
        //    covered, so within the bound nothing was approximated away. That
        //    is over-approximating reasoning, published as `Over`.
        //
        // Declaring `Under` here while publishing discharges as `Over` is what
        // the blackboard's direction registration is designed to catch, so the
        // declaration says what the engine actually does.
        Direction::Exact
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };

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
            postdom: crate::postdom::PostDom::new(body),
            program_classes: prog.bodies.keys().map(|k| k.class.clone()).collect(),
            vars: HashMap::new(),
            str_vars: HashMap::new(),
            nondet_terms: Vec::new(),
            var_widths: HashMap::new(),
            violations: Vec::new(),
            depth: 0,
            max_depth: self.max_depth,
            solver_calls: 0,
            exhausted: false,
            all_paths_complete: true,
            skipped_obligations: HashSet::new(),
            statics: HashMap::new(),
            static_str: HashMap::new(),
            static_tainted: HashSet::new(),
            field_arrays: HashMap::new(),
            field_str: HashMap::new(),
            field_tainted: HashSet::new(),
            array_map: Vec::new(),
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
            all_calls_resolved: true,
            has_unresolved_in_try: false,
            current_block: None,
            path_constraints: Vec::new(),
            inlined_methods: HashSet::new(),
        };

        // Constrain entry method's Ref-typed parameters to be non-null.
        // JVM guarantees main()'s args is non-null; for other entry methods
        // we conservatively assume Ref parameters are non-null since they were
        // provided by a concrete caller.
        ctx.constrain_ref_params_nonnull();

        ctx.explore_block(body.entry, 0);

        let violations = std::mem::take(&mut ctx.violations);
        let violations_empty = violations.is_empty();
        debug!(
            "smt-bmc: exploration complete, found {} violation(s), {} solver calls, {} block visits, {} forks, exhausted={}, all_paths_complete={}, all_calls_resolved={}, unresolved_in_try={}, skipped={}",
            violations.len(),
            ctx.solver_calls,
            ctx.block_visits,
            ctx.fork_count,
            ctx.exhausted,
            ctx.all_paths_complete,
            ctx.all_calls_resolved,
            ctx.has_unresolved_in_try,
            ctx.skipped_obligations.len(),
        );

        let mut advanced = false;
        for (method, oid, witness) in violations {
            let oref = ObligationRef { method, id: oid };
            debug!(
                "smt-bmc: publishing violation at {oref:?}, witness={:?}",
                witness.nondet_sequence()
            );
            let published = bb.publish(
                self.id(),
                self.direction(),
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

        // If exploration completed without hitting budget limits and found
        // no violations, publish Bounded for obligations in the entry method.
        if violations_empty && !ctx.exhausted && ctx.budget_left() {
            if ctx.all_paths_complete {
                let open_list = bb.open();
                log::trace!("smt-bmc: exhaustive discharge check: entry={entry:?}, inlined={:?}, open={:?}, skipped={:?}", ctx.inlined_methods, open_list, ctx.skipped_obligations);
                for oref in open_list {
                    let method_explored =
                        &oref.method == entry || ctx.inlined_methods.contains(&oref.method);
                    // For the entry method: only block discharge when a
                    // havoced call is in a try block (exception edges).
                    // For inlined callees: require all_calls_resolved since
                    // havoced calls could have been the path to reach the
                    // callee with different data.
                    // For unexplored methods: require both all_paths_complete
                    // and all_calls_resolved to prove unreachability.
                    let can_discharge = if &oref.method == entry {
                        !ctx.has_unresolved_in_try
                    } else if method_explored {
                        ctx.all_calls_resolved
                    } else {
                        ctx.all_paths_complete && ctx.all_calls_resolved
                    };
                    if can_discharge && !ctx.skipped_obligations.contains(&oref.id) {
                        debug!("smt-bmc: discharging {oref:?} (exhaustive exploration)");
                        let _ = bb.publish(
                            self.id(),
                            Direction::Over,
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
            } else {
                for oref in bb.open() {
                    if &oref.method == entry {
                        let _ = bb.publish(
                            self.id(),
                            self.direction(),
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
    /// Post-dominator tree for `body`, computed once. Decides where a branch's
    /// arms provably reconverge, i.e. whether they can be diamond-merged.
    postdom: crate::postdom::PostDom,
    /// Every class the program declares a body for, for `is_program_class`.
    program_classes: HashSet<String>,
    vars: HashMap<VarId, Term>,
    str_vars: HashMap<VarId, Term>,
    nondet_terms: Vec<(usize, Term, u32, Ty, Option<Term>)>,
    violations: Vec<(MethodKey, ObligationId, Witness)>,
    depth: u32,
    max_depth: u32,
    solver_calls: u32,
    exhausted: bool,
    all_paths_complete: bool,
    skipped_obligations: HashSet<ObligationId>,

    // ── Heap model ──────────────────────────────────────────────────────
    statics: HashMap<FK, Term>,
    static_str: HashMap<FK, Term>,
    static_tainted: HashSet<FK>,
    field_arrays: HashMap<FK, Term>,
    field_str: HashMap<FK, Term>,
    field_tainted: HashSet<FK>,
    array_map: Vec<(Term, Term, Term)>,
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
    /// True when every Call rvalue was resolved (inlined or math-modelled).
    /// When false, some calls were havoced and transitive callees may be hidden.
    all_calls_resolved: bool,
    /// True when a havoced (unresolved) call is in a block with exception edges.
    /// Only in this case can the havoced call throw to an unexplored handler
    /// containing an assertion.
    has_unresolved_in_try: bool,
    /// Current block being explored (for exception edge checks).
    current_block: Option<BlockId>,
    path_constraints: Vec<Term>,
    inlined_methods: HashSet<MethodKey>,
}

/// Everything the two branch handlers need to know about a conditional edge.
///
/// Passed as one value rather than eight positional arguments: the two
/// handlers took the same list in a different order, which is the kind of
/// signature where transposing two `BlockId`s compiles and silently swaps the
/// arms of every branch in the program.
#[derive(Clone, Copy)]
pub(super) struct Branch {
    pub block_id: BlockId,
    /// The condition depends on something the encoding cannot model exactly.
    pub tainted: bool,
    /// Term asserting the condition is true.
    pub nonzero: Term,
    /// Term asserting it is false.
    pub is_zero: Term,
    pub then_: BlockId,
    pub else_: BlockId,
    pub stop_at: Option<BlockId>,
}

/// One arm of a forked switch, held until every arm has been explored and they
/// can be merged back together.
///
/// A named struct rather than a five-tuple of
/// `(Term, SavedState, Option<Term>, Option<Term>, bool)`: two of those fields
/// have the same type and adjacent positions, and telling them apart at the
/// destructuring site meant counting underscores.
pub(super) struct SwitchCase {
    /// Term asserting this case's value was the one selected.
    pub guard: Term,
    pub state: SavedState,
    pub inline_return: Option<Term>,
    pub inline_return_str: Option<Term>,
    pub inline_return_tainted: bool,
}

/// Snapshot of mutable state for save/restore across forks and diamond merges.
#[derive(Clone)]
pub(super) struct SavedState {
    vars: HashMap<VarId, Term>,
    str_vars: HashMap<VarId, Term>,
    nondet_terms: Vec<(usize, Term, u32, Ty, Option<Term>)>,
    var_widths: HashMap<VarId, u32>,
    tainted: HashSet<VarId>,
    float_tainted: HashSet<VarId>,
    path_tainted: bool,
    statics: HashMap<FK, Term>,
    static_str: HashMap<FK, Term>,
    static_tainted: HashSet<FK>,
    field_arrays: HashMap<FK, Term>,
    field_str: HashMap<FK, Term>,
    field_tainted: HashSet<FK>,
    array_map: Vec<(Term, Term, Term)>,
    type_array: Term,
    loop_visits: HashMap<(String, u32), u32>,
    pc_len: usize,
}

/// Small utility methods on ExploreCtx: budget, width, taint, field helpers.
impl<'a> ExploreCtx<'a> {
    fn budget_left(&self) -> bool {
        !self.exhausted
            && self.solver_calls < MAX_SOLVER_CALLS
            && self.violations.len() < MAX_VIOLATIONS
            && self.block_visits < MAX_BLOCK_VISITS
            && self.fork_count < MAX_FORKS
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
            Rvalue::Nondet(ty, _) | Rvalue::Havoc(ty) | Rvalue::Cast(ty, _) => self.width_of_ty(ty),
            Rvalue::Cmp(_, _) | Rvalue::InstanceOf { .. } | Rvalue::ArrayLength(_) => 32,
            Rvalue::GetStatic(fk) | Rvalue::GetField { field: fk, .. } => {
                Self::field_elem_width(&fk.desc)
            }
            Rvalue::ArrayLoad { .. } => 32, // element arrays are 32-bit
            Rvalue::New(_) | Rvalue::NewArray { .. } => 32,
            Rvalue::Call { target, .. } => {
                let ret = target.desc.rsplit(')').nth(1).unwrap_or("");
                let _ = ret;
                // Parse return type from descriptor
                let after_paren = target.desc.split(')').nth(1).unwrap_or("V");
                match after_paren.as_bytes().first() {
                    Some(b'J') | Some(b'D') => 64,
                    _ => 32,
                }
            }
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

    fn field_key_raw(fk: &FieldKey) -> (String, String, String) {
        (fk.class.clone(), fk.name.clone(), fk.desc.clone())
    }

    fn field_key_resolved(&self, fk: &FieldKey) -> (String, String, String) {
        let resolved_class = self.prog.resolve_field_class(&fk.class, &fk.name, &fk.desc);
        (resolved_class, fk.name.clone(), fk.desc.clone())
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
                if roast_models::STR_OWNERS.contains(&target.class.as_str()) {
                    return !self.str_call_modelled(target, args);
                }
                if self.math_call_modelled(target) {
                    return false;
                }
                if self.can_inline(target, *is_virtual) {
                    return false;
                }
                true
            }
            Rvalue::Use(o) | Rvalue::Neg(o) => self.operand_tainted(o) || self.operand_is_float(o),
            Rvalue::Cast(_, o) => self.operand_tainted(o) || self.operand_is_float(o),
            Rvalue::Bin(_, a, b) | Rvalue::Cmp(a, b) => {
                self.operand_tainted(a)
                    || self.operand_tainted(b)
                    || self.operand_is_float(a)
                    || self.operand_is_float(b)
            }
            Rvalue::Nondet(..) => false,
            Rvalue::Havoc(_) => true,
        }
    }

    fn rvalue_float_tainted(&self, rv: &Rvalue) -> bool {
        match rv {
            Rvalue::Use(o) | Rvalue::Neg(o) => {
                self.operand_float_tainted(o) || self.operand_is_float(o)
            }
            Rvalue::Cast(_, o) => self.operand_float_tainted(o) || self.operand_is_float(o),
            Rvalue::Bin(_, a, b) | Rvalue::Cmp(a, b) => {
                self.operand_float_tainted(a)
                    || self.operand_float_tainted(b)
                    || self.operand_is_float(a)
                    || self.operand_is_float(b)
            }
            _ => false,
        }
    }

    /// Is this a class from the program under analysis, as opposed to a
    /// library class we never loaded?
    ///
    /// Reads a set built once at construction. It used to scan every method key
    /// in the program on each call, from inside `get_field_array` and
    /// `rvalue_tainted` -- both on the per-field-access path.
    fn is_program_class(&self, class: &str) -> bool {
        self.program_classes.contains(class)
    }

    fn field_elem_width(desc: &str) -> u32 {
        match desc.as_bytes().first() {
            Some(b'J') | Some(b'D') => 64,
            _ => 32,
        }
    }

    fn get_field_array(&mut self, k: &FK, elem_width: u32) -> Term {
        if let Some(&arr) = self.field_arrays.get(k) {
            return arr;
        }
        let arr = if self.is_program_class(&k.0) {
            let zero = self.solver.bv_const(0, elem_width);
            self.solver.const_array(zero, elem_width)
        } else {
            self.solver
                .fresh_array(&format!("f_{}_{}", k.0.replace('/', "_"), k.1), elem_width)
        };
        self.field_arrays.insert(k.clone(), arr);
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
            if c != class && self.prog.is_subtype(c, class) {
                let id = self.get_type_id(c);
                if !result.contains(&id) {
                    result.push(id);
                }
            }
        }
        result
    }

    fn constrain_ref_params_nonnull(&mut self) {
        let desc = self.body.key.desc.clone();
        let params = Self::parse_param_slots(&desc);
        for (vid_idx, info) in self.body.vars.iter().enumerate() {
            if let roast_ir::VarKind::Local(slot) = info.kind {
                if info.ty == roast_ir::Ty::Ref {
                    if let Some(class) = params
                        .iter()
                        .find(|(s, _)| *s == slot as usize)
                        .map(|(_, c)| c.clone())
                    {
                        let vid = roast_ir::VarId(vid_idx as u32);
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
        if self.solver_calls > MAX_SOLVER_CALLS {
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

    fn check_sat_with_path_and(&mut self, extra: Term) -> SatResult {
        self.solver_calls += 1;
        if self.solver_calls > MAX_SOLVER_CALLS {
            self.exhausted = true;
            return SatResult::Unknown;
        }
        self.solver.push();
        for &pc in &self.path_constraints {
            self.solver.assert(pc);
        }
        self.solver.assert(extra);

        // Don't pop yet — caller may need to extract witness
        self.solver.check_sat()
    }

    fn extract_witness(&mut self) -> Witness {
        let info: Vec<(Term, u32, Ty, Option<Term>)> = self
            .nondet_terms
            .iter()
            .map(|(_, t, w, ty, st)| (*t, *w, *ty, *st))
            .collect();
        let mut entries = Vec::new();
        for (t, w, ty, str_term) in &info {
            let val = self.solver.get_value_i64(*t).unwrap_or(0);
            let raw = if *w <= 32 { val as i32 as i64 } else { val };
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
        Witness { entries }
    }
}
