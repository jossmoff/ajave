//! SMT-backed bounded model checker.
//!
//! Encodes paths symbolically and asks a solver for satisfying assignments,
//! replacing the concrete engine's "enumerate, don't solve" with "solve, don't
//! enumerate". Finds any bug reachable within bounded depth for arbitrary
//! integer/long inputs, not just a fixed candidate pool.
//!
//! Direction: Under. JvmReplay confirms all witnesses.

use std::collections::{HashMap, HashSet};

use log::{debug, info, warn};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_core::smt::{SatResult, Solver, SolverFactory, Term};
use roast_ir::verdict::{NondetEntry, NondetValue, Witness};
use roast_ir::*;
use roast_models;

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
        Direction::Under
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

        let mut ctx = ExploreCtx {
            solver: solver.as_mut(),
            prog,
            body,
            vars: HashMap::new(),
            str_vars: HashMap::new(),
            nondet_terms: Vec::new(),
            violations: Vec::new(),
            depth: 0,
            max_depth: self.max_depth,
            solver_calls: 0,
            exhausted: false,
            heap: HashMap::new(),
            heap_str: HashMap::new(),
            heap_tainted: HashSet::new(),
            ordinal_map: Vec::new(),
            tainted: HashSet::new(),
            path_tainted: false,
            call_depth: 0,
            loop_visits: HashMap::new(),
            block_visits: 0,
            fork_count: 0,
            clinit_done: HashSet::new(),
            next_alloc_id: 1,
            inline_return: None,
            path_constraints: Vec::new(),
        };

        ctx.explore_block(body.entry, 0);

        let violations = std::mem::take(&mut ctx.violations);
        let violations_empty = violations.is_empty();
        debug!(
            "smt-bmc: exploration complete, found {} violation(s), {} solver calls, {} block visits, {} forks, exhausted={}",
            violations.len(),
            ctx.solver_calls,
            ctx.block_visits,
            ctx.fork_count,
            ctx.exhausted,
        );

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
        // no violations, publish Bounded for all open obligations. This tells
        // k-induction that the base case is satisfied at this depth.
        if violations_empty && !ctx.exhausted && ctx.budget_left() {
            for oref in bb.open() {
                let _ = bb.publish(
                    self.id(),
                    self.direction(),
                    Artifact::Status(oref, Status::Bounded { k: self.max_depth }),
                );
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

struct ExploreCtx<'a> {
    solver: &'a mut dyn Solver,
    prog: &'a Program,
    /// The body currently being explored (changes during call inlining).
    body: &'a Body,
    /// Current symbolic state: VarId -> Term (bitvector for ints, BV reference for objects).
    vars: HashMap<VarId, Term>,
    /// String content terms, keyed by VarId. Present only for variables that
    /// hold a tracked string value (nondet strings, string constants, results
    /// of string method calls).
    str_vars: HashMap<VarId, Term>,
    /// (nondet_index, bv_term, width, Ty, Option<str_term>) in encounter order.
    nondet_terms: Vec<(usize, Term, u32, Ty, Option<Term>)>,
    /// Found violations: (method_key, obligation_id, witness).
    violations: Vec<(MethodKey, ObligationId, Witness)>,
    depth: u32,
    max_depth: u32,
    /// Number of check-sat calls made.
    solver_calls: u32,
    /// Set when budget is exhausted; stops further exploration.
    exhausted: bool,
    /// Symbolic heap: tracks the last written value for each field.
    /// Keyed by (class, name, desc). For instance fields from different
    /// receivers this is a flat merge — sound for under-approximation
    /// since JvmReplay confirms all witnesses.
    heap: HashMap<(String, String, String), Term>,
    /// String content in the symbolic heap, parallels `heap`.
    heap_str: HashMap<(String, String, String), Term>,
    /// Taint status for heap fields — true if the stored value is tainted.
    heap_tainted: HashSet<(String, String, String)>,
    /// Per-object ordinal tracking for enum instances. Each entry maps an
    /// object reference term to its ordinal term. Lookups build an ITE chain
    /// over all entries, so this works correctly for ITE-merged references
    /// (e.g. `ite(cond, low_ref, normal_ref)` resolves to the right ordinal).
    ordinal_map: Vec<(Term, Term)>,
    /// Variables whose values depend on unmodelled operations (heap reads,
    /// method calls, etc.). Violations that depend on tainted values are
    /// unreliable — the solver can freely choose values for the unmodelled
    /// parts and produce spurious counterexamples.
    tainted: HashSet<VarId>,
    /// True when the current path goes through a branch or assume whose
    /// condition is tainted. All checks on such paths are skipped.
    path_tainted: bool,
    /// Current call inlining depth.
    call_depth: u32,
    /// Blocks visited on the current path, for loop back-edge detection.
    /// Key: (method class+name+desc, block_id). Counts how many times
    /// we've entered this block on the current path (for bounded unrolling).
    loop_visits: HashMap<(String, u32), u32>,
    /// Total block visits across all paths (monotonically increasing).
    block_visits: u64,
    /// Total path forks (monotonically increasing).
    fork_count: u32,
    /// Classes whose <clinit> has been run (prevents re-initialization).
    clinit_done: HashSet<String>,
    /// Next unique allocation ID for deterministic object references.
    next_alloc_id: i64,
    /// Captured return term from the most recently completed inlined callee
    /// path. Set by Terminator::Return; read by try_inline_call.
    inline_return: Option<Term>,
    /// Accumulated path constraints (Bool terms). Instead of using push/pop
    /// to scope branch conditions, we collect them here and assert them all
    /// at check time. This avoids deep incremental nesting which causes Z3
    /// to return Unknown for BV formulas.
    path_constraints: Vec<Term>,
}

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

    fn get_var(&mut self, vid: VarId) -> Term {
        if let Some(&t) = self.vars.get(&vid) {
            return t;
        }
        let w = self.width_of_var(vid);
        let t = self.solver.fresh_bv(&format!("uninit_v{}", vid.0), w);
        self.vars.insert(vid, t);
        t
    }

    /// Returns true if an operand's value depends on an unmodelled operation.
    fn operand_tainted(&self, op: &Operand) -> bool {
        matches!(op, Operand::Var(v) if self.tainted.contains(v))
    }

    /// Returns true if evaluating this rvalue produces a tainted result —
    /// either because it is itself unmodelled, or because it consumes a
    /// tainted operand.
    fn field_key(fk: &FieldKey) -> (String, String, String) {
        (fk.class.clone(), fk.name.clone(), fk.desc.clone())
    }

    fn rvalue_tainted(&mut self, rv: &Rvalue) -> bool {
        match rv {
            Rvalue::GetStatic(fk) => {
                // Run clinit eagerly so the taint check sees initialized fields.
                self.ensure_clinit(&fk.class);
                let k = Self::field_key(fk);
                if self.heap.contains_key(&k) {
                    self.heap_tainted.contains(&k)
                } else {
                    true
                }
            }
            Rvalue::GetField { field, .. } => {
                // Per-object ordinal lookup is never tainted when we have
                // any ordinal entries (the ITE chain handles resolution).
                if field.name == "$$ordinal" && !self.ordinal_map.is_empty() {
                    return false;
                }
                let k = Self::field_key(field);
                if self.heap.contains_key(&k) {
                    self.heap_tainted.contains(&k)
                } else {
                    true
                }
            }
            Rvalue::ArrayLoad { .. }
            | Rvalue::ArrayLength(_)
            | Rvalue::NewArray { .. }
            | Rvalue::InstanceOf { .. } => true,
            // New allocations are not tainted — field tracking handles state.
            Rvalue::New(_) => false,
            Rvalue::Call { target, args, is_virtual } => {
                // String method calls are modelled via Z3's string theory.
                if roast_models::STR_OWNERS.contains(&target.class.as_str()) {
                    return !self.str_call_modelled(target, args);
                }
                // User method calls that can be inlined are NOT tainted.
                if self.can_inline(target, *is_virtual) {
                    return false;
                }
                true
            }
            Rvalue::Use(o) | Rvalue::Neg(o) | Rvalue::Cast(_, o) => self.operand_tainted(o),
            Rvalue::Bin(_, a, b) | Rvalue::Cmp(a, b) => {
                self.operand_tainted(a) || self.operand_tainted(b)
            }
            Rvalue::Nondet(_) => false,
        }
    }

    /// Check whether a call target can be inlined.
    fn can_inline(&self, target: &MethodKey, is_virtual: bool) -> bool {
        if self.call_depth >= MAX_CALL_DEPTH {
            return false;
        }
        if is_virtual {
            let targets = self.prog.devirtualise(target);
            !targets.is_empty() && targets.iter().all(|t| self.prog.body(t).is_some())
        } else {
            self.prog.body(target).is_some()
        }
    }

    /// Check if a string method call can be encoded via the string theory.
    fn str_call_modelled(&self, target: &MethodKey, args: &[Operand]) -> bool {
        let has_recv_str = args.first().map_or(false, |a| match a {
            Operand::Var(v) => self.str_vars.contains_key(v),
            Operand::Const(Const::Str(_)) => true,
            _ => false,
        });
        let has_arg1_str = args.get(1).map_or(false, |a| match a {
            Operand::Var(v) => self.str_vars.contains_key(v),
            Operand::Const(Const::Str(_)) => true,
            _ => false,
        });
        match target.name.as_str() {
            "length" | "isEmpty" | "toString" => has_recv_str,
            "contains" | "equals" | "startsWith" | "endsWith" | "concat" => {
                has_recv_str && has_arg1_str
            }
            "charAt" | "substring" => has_recv_str,
            "indexOf" => has_recv_str && has_arg1_str,
            "valueOf" => true, // takes an int arg, not a string receiver
            _ => false,
        }
    }

    #[allow(clippy::type_complexity)]
    fn save_state(
        &self,
    ) -> (
        HashMap<VarId, Term>,
        HashMap<VarId, Term>,
        Vec<(usize, Term, u32, Ty, Option<Term>)>,
        HashSet<VarId>,
        bool,
        HashMap<(String, String, String), Term>,
        HashMap<(String, String, String), Term>,
        HashSet<(String, String, String)>,
        HashMap<(String, u32), u32>,
        usize, // path_constraints length
        Vec<(Term, Term)>,
    ) {
        (
            self.vars.clone(),
            self.str_vars.clone(),
            self.nondet_terms.clone(),
            self.tainted.clone(),
            self.path_tainted,
            self.heap.clone(),
            self.heap_str.clone(),
            self.heap_tainted.clone(),
            self.loop_visits.clone(),
            self.path_constraints.len(),
            self.ordinal_map.clone(),
        )
    }

    #[allow(clippy::type_complexity)]
    fn restore_state(
        &mut self,
        saved: (
            HashMap<VarId, Term>,
            HashMap<VarId, Term>,
            Vec<(usize, Term, u32, Ty, Option<Term>)>,
            HashSet<VarId>,
            bool,
            HashMap<(String, String, String), Term>,
            HashMap<(String, String, String), Term>,
            HashSet<(String, String, String)>,
            HashMap<(String, u32), u32>,
            usize,
            Vec<(Term, Term)>,
        ),
    ) {
        self.vars = saved.0;
        self.str_vars = saved.1;
        self.nondet_terms = saved.2;
        self.tainted = saved.3;
        self.path_tainted = saved.4;
        self.heap = saved.5;
        self.heap_str = saved.6;
        self.heap_tainted = saved.7;
        self.loop_visits = saved.8;
        self.path_constraints.truncate(saved.9);
        self.ordinal_map = saved.10;
    }

    /// Run <clinit> for a class if it hasn't been run yet and has a body.
    fn ensure_clinit(&mut self, class: &str) {
        if self.clinit_done.contains(class) {
            return;
        }
        self.clinit_done.insert(class.to_string());
        let clinit_key = MethodKey {
            class: class.to_string(),
            name: "<clinit>".to_string(),
            desc: "()V".to_string(),
        };
        if let Some(clinit) = self.prog.body(&clinit_key) {
            if self.call_depth >= MAX_CALL_DEPTH || !self.budget_left() {
                return;
            }
            debug!("smt-bmc: running <clinit> for {class}");
            let saved_body = self.body;
            let saved_vars = self.vars.clone();
            let saved_str_vars = self.str_vars.clone();
            let saved_tainted = self.tainted.clone();
            let saved_path_tainted = self.path_tainted;
            let saved_pc_len = self.path_constraints.len();

            self.body = clinit;
            self.call_depth += 1;
            self.vars.clear();
            self.str_vars.clear();
            self.tainted.clear();

            self.explore_block(clinit.entry, 0);

            self.call_depth -= 1;
            self.body = saved_body;
            self.vars = saved_vars;
            self.str_vars = saved_str_vars;
            self.tainted = saved_tainted;
            self.path_tainted = saved_path_tainted;
            self.path_constraints.truncate(saved_pc_len);
        }
    }

    fn encode_operand(&mut self, op: &Operand) -> Term {
        match op {
            Operand::Var(v) => self.get_var(*v),
            Operand::Const(Const::Int(n)) => self.solver.bv_const(*n as i64, 32),
            Operand::Const(Const::Long(n)) => self.solver.bv_const(*n, 64),
            Operand::Const(Const::Null) => self.solver.bv_const(0, 32),
            // String constants get a non-null BV reference; the string content
            // is accessed via encode_str_operand.
            Operand::Const(Const::Str(_)) => self.solver.bv_const(1, 32),
            Operand::Const(_) => self.solver.fresh_bv("const", 32),
        }
    }

    /// Get the string content term for an operand. Returns None if the
    /// operand doesn't have tracked string content.
    fn encode_str_operand(&mut self, op: &Operand) -> Option<Term> {
        match op {
            Operand::Var(v) => self.str_vars.get(v).copied(),
            Operand::Const(Const::Str(s)) => Some(self.solver.str_const(s)),
            _ => None,
        }
    }

    /// Encode a string method call. Returns `Some((bv_result, Option<str_result>))`
    /// if the method is modelled, `None` otherwise.
    fn encode_str_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
    ) -> Option<(Term, Option<Term>)> {
        let recv_str = args.first().and_then(|a| self.encode_str_operand(a));
        let one = self.solver.bv_const(1, 32);
        let zero = self.solver.bv_const(0, 32);

        match target.name.as_str() {
            "length" => {
                let s = recv_str?;
                let len_int = self.solver.str_len(s);
                let len_bv = self.solver.int_to_bv32(len_int);
                Some((len_bv, None))
            }
            "isEmpty" => {
                let s = recv_str?;
                let len_int = self.solver.str_len(s);
                let zero_int = self.solver.int_const(0);
                let eq = self.solver.bveq(len_int, zero_int);
                let r = self.solver.ite(eq, one, zero);
                Some((r, None))
            }
            "contains" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_contains(s, t);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "equals" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_eq(s, t);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "startsWith" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_prefixof(t, s);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "endsWith" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_suffixof(t, s);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "charAt" => {
                let s = recv_str?;
                let idx_bv = self.encode_operand(args.get(1)?);
                let idx_int = self.solver.bv32_to_int(idx_bv);
                let ch_str = self.solver.str_at(s, idx_int);
                let ch_int = self.solver.str_to_int(ch_str);
                let ch_bv = self.solver.int_to_bv32(ch_int);
                Some((ch_bv, None))
            }
            "indexOf" => {
                let s = recv_str?;
                let arg1 = args.get(1)?;
                let needle = self.encode_str_operand(arg1)?;
                let start = self.solver.int_const(0);
                let idx_int = self.solver.str_indexof(s, needle, start);
                let idx_bv = self.solver.int_to_bv32(idx_int);
                Some((idx_bv, None))
            }
            "substring" => {
                let s = recv_str?;
                let start_bv = self.encode_operand(args.get(1)?);
                let start_int = self.solver.bv32_to_int(start_bv);
                let len_int = if let Some(end_op) = args.get(2) {
                    let end_bv = self.encode_operand(end_op);
                    let diff_bv = self.solver.bvsub(end_bv, start_bv);
                    self.solver.bv32_to_int(diff_bv)
                } else {
                    let total = self.solver.str_len(s);
                    let total_bv = self.solver.int_to_bv32(total);
                    let diff = self.solver.bvsub(total_bv, start_bv);
                    self.solver.bv32_to_int(diff)
                };
                let result = self.solver.str_substr(s, start_int, len_int);
                Some((one, Some(result)))
            }
            "concat" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let result = self.solver.str_concat(s, t);
                Some((one, Some(result)))
            }
            "toString" => {
                let s = recv_str?;
                Some((one, Some(s)))
            }
            "valueOf" => {
                let arg_bv = self.encode_operand(args.first()?);
                let arg_int = self.solver.bv32_to_int(arg_bv);
                let result = self.solver.str_from_int(arg_int);
                Some((one, Some(result)))
            }
            _ => None,
        }
    }

    fn encode_rvalue(&mut self, rv: &Rvalue) -> Term {
        match rv {
            Rvalue::Use(o) => self.encode_operand(o),
            Rvalue::Nondet(ty) => {
                let w = self.width_of_ty(ty);
                let idx = self.nondet_terms.len();
                let t = self.solver.fresh_bv(&format!("nd_{idx}"), w);
                // Nondet strings are always non-null (they model
                // Verifier.nondetString() which returns a valid String).
                if *ty == Ty::Str {
                    self.assert_nonzero(t);
                }
                let str_term = if *ty == Ty::Str {
                    Some(self.solver.fresh_str(&format!("nds_{idx}")))
                } else {
                    None
                };
                // Only record Int/Long/Str nondets for witness extraction.
                if *ty != Ty::Ref {
                    self.nondet_terms.push((idx, t, w, *ty, str_term));
                }
                t
            }
            Rvalue::Bin(op, a, b) => self.encode_binop(*op, a, b),
            Rvalue::Neg(o) => {
                let t = self.encode_operand(o);
                self.solver.bvneg(t)
            }
            Rvalue::Cast(ty, o) => {
                let t = self.encode_operand(o);
                match ty {
                    Ty::Long => self.solver.sign_extend(t, 32),
                    Ty::Int => self.solver.extract(t, 31, 0),
                    _ => t,
                }
            }
            Rvalue::Cmp(a, b) => {
                let at = self.encode_operand(a);
                let bt = self.encode_operand(b);
                let lt = self.solver.bvslt(at, bt);
                let eq = self.solver.bveq(at, bt);
                let minus1 = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let one = self.solver.bv_const(1, 32);
                let inner = self.solver.ite(eq, zero, one);
                self.solver.ite(lt, minus1, inner)
            }
            Rvalue::GetStatic(fk) => {
                // Lazy clinit: run <clinit> for the class on first access.
                self.ensure_clinit(&fk.class);
                let k = Self::field_key(fk);
                if let Some(&t) = self.heap.get(&k) {
                    t
                } else {
                    self.solver.fresh_bv("heap", 32)
                }
            }
            Rvalue::GetField { field, obj, .. } => {
                // Per-object ordinal lookup via ITE chain over all known
                // (object_ref, ordinal) pairs. Works for ITE-merged references.
                if field.name == "$$ordinal" && !self.ordinal_map.is_empty() {
                    let obj_term = self.encode_operand(obj);
                    let pairs: Vec<(Term, Term)> = self.ordinal_map.clone();
                    let mut result = self.solver.fresh_bv("ord_default", 32);
                    for (ref_term, ord_term) in pairs.iter().rev() {
                        let eq = self.solver.bveq(obj_term, *ref_term);
                        result = self.solver.ite(eq, *ord_term, result);
                    }
                    return result;
                }
                let k = Self::field_key(field);
                if let Some(&t) = self.heap.get(&k) {
                    t
                } else {
                    self.solver.fresh_bv("heap", 32)
                }
            }
            // New: unique non-null reference. Using deterministic increasing
            // IDs instead of unconstrained fresh BVs ensures different
            // allocations are never equal (important for reference equality
            // comparisons, e.g., enum instance identity).
            Rvalue::New(_) => {
                let id = self.next_alloc_id;
                self.next_alloc_id += 1;
                self.solver.bv_const(id, 32)
            }
            // Remaining heap ops: fresh unconstrained (sound for Under).
            Rvalue::ArrayLoad { .. }
            | Rvalue::ArrayLength(_)
            | Rvalue::NewArray { .. }
            | Rvalue::InstanceOf { .. }
            | Rvalue::Call { .. } => self.solver.fresh_bv("heap", 32),
        }
    }

    fn encode_binop(&mut self, op: BinOp, a: &Operand, b: &Operand) -> Term {
        let at = self.encode_operand(a);
        let bt = self.encode_operand(b);
        match op {
            BinOp::Add => self.solver.bvadd(at, bt),
            BinOp::Sub => self.solver.bvsub(at, bt),
            BinOp::Mul => self.solver.bvmul(at, bt),
            BinOp::Div => self.solver.bvsdiv(at, bt),
            BinOp::Rem => self.solver.bvsrem(at, bt),
            BinOp::And => self.solver.bvand(at, bt),
            BinOp::Or => self.solver.bvor(at, bt),
            BinOp::Xor => self.solver.bvxor(at, bt),
            BinOp::Shl => self.solver.bvshl(at, bt),
            BinOp::Shr => self.solver.bvashr(at, bt),
            BinOp::UShr => self.solver.bvlshr(at, bt),
            BinOp::Eq => {
                let cmp = self.solver.bveq(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Ne => {
                let cmp = self.solver.bveq(at, bt);
                let ncmp = self.solver.not(cmp);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(ncmp, one, zero)
            }
            BinOp::Lt => {
                let cmp = self.solver.bvslt(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Le => {
                let cmp = self.solver.bvsle(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Gt => {
                let cmp = self.solver.bvsgt(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Ge => {
                let cmp = self.solver.bvsge(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
        }
    }

    /// Assert that a BV term is nonzero.
    fn assert_nonzero(&mut self, t: Term) {
        let zero = self.solver.bv_const(0, 32);
        let eq = self.solver.bveq(t, zero);
        let neq = self.solver.not(eq);
        self.solver.assert(neq);
    }

    /// Create a Bool term: (t != 0). Does NOT assert — for path_constraints.
    fn nonzero_constraint(&mut self, t: Term) -> Term {
        let zero = self.solver.bv_const(0, 32);
        let eq = self.solver.bveq(t, zero);
        self.solver.not(eq)
    }

    /// Create a Bool term: (t == 0). Does NOT assert — for path_constraints.
    fn zero_constraint(&mut self, t: Term) -> Term {
        let zero = self.solver.bv_const(0, 32);
        self.solver.bveq(t, zero)
    }

    /// Check sat with all path constraints + any extra assertions in a single
    /// flat push scope. This avoids deep incremental nesting.
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

    /// Check sat with all path constraints + one additional constraint,
    /// in a single flat push scope.
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
        let res = self.solver.check_sat();
        // Don't pop yet — caller may need to extract witness
        res
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
        }
    }

    /// Try to inline a method call. Returns true if inlining succeeded,
    /// in which case `dest_var` is set to an unconstrained return value
    /// and violations inside the callee have been explored.
    fn try_inline_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
        dest_var: VarId,
        is_virtual: bool,
    ) -> bool {
        if self.call_depth >= MAX_CALL_DEPTH || !self.budget_left() {
            return false;
        }

        // Resolve concrete target(s)
        let targets = if is_virtual {
            let t = self.prog.devirtualise(target);
            if t.is_empty() {
                return false;
            }
            t
        } else {
            vec![target.clone()]
        };

        // All targets must have bodies for us to inline
        if targets.iter().any(|t| self.prog.body(t).is_none()) {
            return false;
        }

        // Encode args using the caller's current variable state
        let arg_terms: Vec<Term> = args.iter().map(|a| self.encode_operand(a)).collect();
        let arg_str_terms: Vec<Option<Term>> =
            args.iter().map(|a| self.encode_str_operand(a)).collect();
        let arg_tainted: Vec<bool> = args.iter().map(|a| self.operand_tainted(a)).collect();

        // Explore each possible target (for virtual calls, this tries all
        // concrete receivers — each is a possible execution path).
        for resolved in &targets {
            if !self.budget_left() {
                break;
            }
            let callee = self.prog.body(resolved).unwrap();

            // Save caller state
            let saved_body = self.body;
            let saved_vars = self.vars.clone();
            let saved_str_vars = self.str_vars.clone();
            let saved_tainted = self.tainted.clone();
            let saved_path_tainted = self.path_tainted;
            let saved_pc_len = self.path_constraints.len();

            // Switch to callee
            self.body = callee;
            self.call_depth += 1;
            self.vars.clear();
            self.str_vars.clear();
            self.tainted.clear();

            // Map arguments to callee's local variable slots.
            let mut slot = 0u16;
            for (i, arg_t) in arg_terms.iter().enumerate() {
                if let Some((vid_idx, vinfo)) = callee
                    .vars
                    .iter()
                    .enumerate()
                    .find(|(_, vi)| matches!(vi.kind, VarKind::Local(s) if s == slot))
                {
                    let vid = VarId(vid_idx as u32);
                    self.vars.insert(vid, *arg_t);
                    if let Some(st) = arg_str_terms[i] {
                        self.str_vars.insert(vid, st);
                    }
                    if arg_tainted[i] {
                        self.tainted.insert(vid);
                    }
                    slot += if vinfo.ty.is_wide() { 2 } else { 1 };
                } else {
                    slot += 1;
                }
            }

            // Explore callee — violations inside it are found here.
            // No push/pop needed: path_constraints are restored via
            // saved state, and define-const terms are permanent.
            self.inline_return = None;
            self.explore_block(callee.entry, 0);

            // Restore caller state
            self.call_depth -= 1;
            self.body = saved_body;
            self.vars = saved_vars;
            self.str_vars = saved_str_vars;
            self.tainted = saved_tainted;
            self.path_tainted = saved_path_tainted;
            self.path_constraints.truncate(saved_pc_len);
        }

        // Return value: use the callee's actual return term if captured,
        // otherwise fall back to unconstrained. This links nondet values
        // in the callee to the caller's use of the return value, enabling
        // correct witness extraction.
        let w = self.width_of_var(dest_var);
        let ret_t = self.inline_return.unwrap_or_else(|| {
            self.solver.fresh_bv(&format!("ret_{}", target.name), w)
        });
        self.vars.insert(dest_var, ret_t);

        true
    }

    /// Collect all forward-reachable block IDs from `start` (inclusive).
    /// Only follows edges where target > source (no back-edges).
    /// Limited to `limit` blocks to avoid runaway walks.
    fn forward_reachable(&self, start: BlockId, limit: usize) -> HashSet<u32> {
        let mut reached = HashSet::new();
        let mut worklist = vec![start];
        while let Some(bid) = worklist.pop() {
            if !reached.insert(bid.0) || reached.len() >= limit {
                continue;
            }
            let succs = self.block_successors(bid);
            for s in succs {
                if s.0 > bid.0 {
                    worklist.push(s);
                }
            }
        }
        reached
    }

    /// Return all successor block IDs of a terminator.
    fn block_successors(&self, bid: BlockId) -> Vec<BlockId> {
        match &self.body.block(bid).term {
            Terminator::Goto(t) => vec![*t],
            Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
            Terminator::Switch { cases, default, .. } => {
                let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
                v.push(*default);
                v
            }
            _ => vec![],
        }
    }

    /// Find the join (post-dominator) of a diamond branch pattern.
    /// Returns Some(join_block) if both branches converge to the same
    /// block; None if structure is too complex.
    fn find_join(&self, then_: BlockId, else_: BlockId) -> Option<BlockId> {
        self.find_join_multi(&[then_, else_])
    }

    /// Find the join point for multiple branch targets (switch cases + default).
    /// Returns Some(join_block) if ALL targets converge to a common block.
    fn find_join_multi(&self, targets: &[BlockId]) -> Option<BlockId> {
        if targets.is_empty() {
            return None;
        }
        let mut common = self.forward_reachable(targets[0], 50);
        for t in &targets[1..] {
            let reach = self.forward_reachable(*t, 50);
            common = common.intersection(&reach).copied().collect();
        }
        let mut candidates: Vec<u32> = common.into_iter().collect();
        candidates.sort();
        candidates.first().map(|&b| BlockId(b))
    }

    /// Explore a block's statements and terminator, stopping if `stop_at` is reached.
    fn explore_block(&mut self, block_id: BlockId, stmt_idx: usize) {
        self.explore_block_until(block_id, stmt_idx, None);
    }

    fn explore_block_until(&mut self, block_id: BlockId, stmt_idx: usize, stop_at: Option<BlockId>) {
        if stop_at == Some(block_id) {
            return;
        }
        self.block_visits += 1;
        if self.depth > self.max_depth || !self.budget_left() {
            return;
        }

        let b = self.body.block(block_id);

        // Process statements from stmt_idx onwards.
        for idx in stmt_idx..b.stmts.len() {
            if !self.budget_left() {
                return;
            }
            match &b.stmts[idx] {
                Stmt::Assign(v, rv) => {
                    let is_tainted = self.rvalue_tainted(rv);
                    // Try to encode string calls via the string theory,
                    // or inline user method calls.
                    let (t, str_term) = match rv {
                        Rvalue::Call { target, args, .. }
                            if roast_models::STR_OWNERS.contains(&target.class.as_str()) =>
                        {
                            match self.encode_str_call(target, args) {
                                Some((bv, st)) => (bv, st),
                                None => (self.encode_rvalue(rv), None),
                            }
                        }
                        Rvalue::Call {
                            target,
                            args,
                            is_virtual,
                        } => {
                            if self.try_inline_call(target, args, *v, *is_virtual) {
                                // Inlined: vars[v] already set, not tainted.
                                continue;
                            }
                            (self.encode_rvalue(rv), None)
                        }
                        Rvalue::Use(Operand::Var(src)) => {
                            // Propagate string content through copies.
                            let st = self.str_vars.get(src).copied();
                            (self.encode_rvalue(rv), st)
                        }
                        Rvalue::Nondet(Ty::Str) => {
                            let bv = self.encode_rvalue(rv);
                            // The last pushed nondet_term has the str_term.
                            let st = self.nondet_terms.last().and_then(|(_, _, _, _, s)| *s);
                            (bv, st)
                        }
                        Rvalue::GetStatic(fk) => {
                            let k = Self::field_key(fk);
                            let st = self.heap_str.get(&k).copied();
                            (self.encode_rvalue(rv), st)
                        }
                        Rvalue::GetField { field, .. } => {
                            let k = Self::field_key(field);
                            let st = self.heap_str.get(&k).copied();
                            (self.encode_rvalue(rv), st)
                        }
                        _ => (self.encode_rvalue(rv), None),
                    };
                    self.vars.insert(*v, t);
                    if let Some(st) = str_term {
                        self.str_vars.insert(*v, st);
                    } else {
                        self.str_vars.remove(v);
                    }
                    if is_tainted {
                        self.tainted.insert(*v);
                    } else {
                        self.tainted.remove(v);
                    }
                }
                Stmt::Assume(op) => {
                    if self.operand_tainted(op) {
                        self.path_tainted = true;
                    }
                    let t = self.encode_operand(op);
                    let c = self.nonzero_constraint(t);
                    self.path_constraints.push(c);
                    // Check if path is still feasible after assume.
                    let res = self.check_sat_with_path();
                    if res == SatResult::Unsat {
                        return;
                    }
                }
                Stmt::Check(oid) => {
                    // Skip checks whose condition depends on unmodelled
                    // operations — the solver could produce spurious
                    // counterexamples for those.
                    if self.operand_tainted(&self.body.obligation(*oid).cond)
                    {
                        continue;
                    }
                    let ob = self.body.obligation(*oid);
                    let cond = self.encode_operand(&ob.cond);
                    // Check if violation is reachable: path_constraints ∧ cond == 0.
                    let violation_cond = self.zero_constraint(cond);
                    let res = self.check_sat_with_path_and(violation_cond);
                    if res == SatResult::Sat {
                        let witness = self.extract_witness();
                        self.violations
                            .push((self.body.key.clone(), *oid, witness));
                    }
                    // Pop the scope opened by check_sat_with_path_and.
                    self.solver.pop();
                }
                Stmt::PutStatic(fk, val) => {
                    let k = Self::field_key(fk);
                    let t = self.encode_operand(val);
                    self.heap.insert(k.clone(), t);
                    if self.operand_tainted(val) {
                        self.heap_tainted.insert(k.clone());
                    } else {
                        self.heap_tainted.remove(&k);
                    }
                    // Propagate string content to heap.
                    if let Some(st) = match val {
                        Operand::Var(v) => self.str_vars.get(v).copied(),
                        Operand::Const(Const::Str(s)) => Some(self.solver.str_const(s)),
                        _ => None,
                    } {
                        self.heap_str.insert(k, st);
                    } else {
                        self.heap_str.remove(&k);
                    }
                }
                Stmt::PutField { field, val, obj } => {
                    // Per-object ordinal tracking for $$ordinal fields.
                    if field.name == "$$ordinal" {
                        let obj_term = self.encode_operand(obj);
                        let val_term = self.encode_operand(val);
                        self.ordinal_map.push((obj_term, val_term));
                    }
                    let k = Self::field_key(field);
                    let t = self.encode_operand(val);
                    self.heap.insert(k.clone(), t);
                    if self.operand_tainted(val) {
                        self.heap_tainted.insert(k.clone());
                    } else {
                        self.heap_tainted.remove(&k);
                    }
                    if let Some(st) = match val {
                        Operand::Var(v) => self.str_vars.get(v).copied(),
                        Operand::Const(Const::Str(s)) => Some(self.solver.str_const(s)),
                        _ => None,
                    } {
                        self.heap_str.insert(k, st);
                    } else {
                        self.heap_str.remove(&k);
                    }
                }
                Stmt::ArrayStore { .. }
                | Stmt::Nop => {}
            }
        }

        if !self.budget_left() {
            return;
        }

        // Process terminator.
        self.depth += 1;
        match &b.term {
            Terminator::Goto(t) => {
                // Back-edge detection: if the goto target is at or before
                // the current block, it's a loop back-edge. Bound unrolling.
                if t.0 <= block_id.0 {
                    let loop_key = (self.body.key.to_string(), t.0);
                    let count = self.loop_visits.entry(loop_key).or_insert(0);
                    *count += 1;
                    if *count > MAX_LOOP_UNROLL {
                        // Don't explore further; we've unrolled enough.
                    } else {
                        self.explore_block_until(*t, 0, stop_at);
                    }
                } else {
                    self.explore_block_until(*t, 0, stop_at);
                }
            }
            Terminator::Branch { cond, then_, else_ } => {
                let cond_tainted = self.operand_tainted(cond);
                let ct = self.encode_operand(cond);
                let zero = self.solver.bv_const(0, 32);
                let cond_bool = self.solver.bveq(ct, zero);
                let cond_nz = self.solver.not(cond_bool); // true when cond != 0

                // Diamond optimisation: if both branches converge to the
                // same block, explore each side up to the join point and
                // merge with ITE instead of forking into independent paths.
                // This turns exponential path explosion into linear work.
                if let Some(join) = self.find_join(*then_, *else_) {
                    // --- then side ---
                    let saved = self.save_state();
                    if cond_tainted {
                        self.path_tainted = true;
                    }
                    self.path_constraints.push(cond_nz);
                    self.explore_block_until(*then_, 0, Some(join));
                    let then_vars = self.vars.clone();
                    let then_heap = self.heap.clone();
                    let then_tainted = self.tainted.clone();
                    let then_heap_tainted = self.heap_tainted.clone();
                    let then_str = self.str_vars.clone();
                    let then_heap_str = self.heap_str.clone();
                    let then_path_tainted = self.path_tainted;
                    let then_nondets = self.nondet_terms.clone();
                    self.restore_state(saved);

                    // --- else side ---
                    let saved = self.save_state();
                    if cond_tainted {
                        self.path_tainted = true;
                    }
                    self.path_constraints.push(cond_bool);
                    self.explore_block_until(*else_, 0, Some(join));
                    let else_vars = self.vars.clone();
                    let else_heap = self.heap.clone();
                    let else_tainted = self.tainted.clone();
                    let else_heap_tainted = self.heap_tainted.clone();
                    let else_str = self.str_vars.clone();
                    let else_heap_str = self.heap_str.clone();
                    let else_path_tainted = self.path_tainted;
                    let else_nondets = self.nondet_terms.clone();
                    self.restore_state(saved);

                    // Preserve nondets from both sides — the merged ITE state
                    // references terms from both branches, so witness extraction
                    // needs values for all of them.
                    let base_len = self.nondet_terms.len();
                    for nd in &then_nondets[base_len..] {
                        self.nondet_terms.push(nd.clone());
                    }
                    for nd in &else_nondets[base_len..] {
                        self.nondet_terms.push(nd.clone());
                    }

                    // --- merge with ITE ---
                    // Variables
                    let all_vids: HashSet<VarId> = then_vars
                        .keys()
                        .chain(else_vars.keys())
                        .copied()
                        .collect();
                    for vid in all_vids {
                        let tv = then_vars.get(&vid).copied();
                        let ev = else_vars.get(&vid).copied();
                        match (tv, ev) {
                            (Some(t), Some(e)) if t == e => {
                                self.vars.insert(vid, t);
                            }
                            (Some(t), Some(e)) => {
                                let m = self.solver.ite(cond_nz, t, e);
                                self.vars.insert(vid, m);
                            }
                            (Some(t), None) => {
                                let fresh = self.solver.fresh_bv("merge", self.width_of_var(vid));
                                let m = self.solver.ite(cond_nz, t, fresh);
                                self.vars.insert(vid, m);
                            }
                            (None, Some(e)) => {
                                let fresh = self.solver.fresh_bv("merge", self.width_of_var(vid));
                                let m = self.solver.ite(cond_nz, fresh, e);
                                self.vars.insert(vid, m);
                            }
                            (None, None) => {}
                        }
                    }

                    // Heap fields
                    let all_heap_keys: HashSet<_> = then_heap
                        .keys()
                        .chain(else_heap.keys())
                        .cloned()
                        .collect();
                    for k in all_heap_keys {
                        let tv = then_heap.get(&k).copied();
                        let ev = else_heap.get(&k).copied();
                        match (tv, ev) {
                            (Some(t), Some(e)) if t == e => {
                                self.heap.insert(k, t);
                            }
                            (Some(t), Some(e)) => {
                                let m = self.solver.ite(cond_nz, t, e);
                                self.heap.insert(k, m);
                            }
                            (Some(t), None) => {
                                self.heap.insert(k, t);
                            }
                            (None, Some(e)) => {
                                self.heap.insert(k, e);
                            }
                            (None, None) => {}
                        }
                    }

                    // Taint: conservative union
                    self.tainted = &then_tainted | &else_tainted;
                    self.heap_tainted = &then_heap_tainted | &else_heap_tainted;
                    self.path_tainted = then_path_tainted || else_path_tainted;

                    // String vars: keep those present in both with ITE
                    let all_str_vids: HashSet<VarId> = then_str
                        .keys()
                        .chain(else_str.keys())
                        .copied()
                        .collect();
                    self.str_vars.clear();
                    for vid in all_str_vids {
                        match (then_str.get(&vid).copied(), else_str.get(&vid).copied()) {
                            (Some(t), Some(e)) if t == e => {
                                self.str_vars.insert(vid, t);
                            }
                            (Some(t), Some(e)) => {
                                let m = self.solver.ite(cond_nz, t, e);
                                self.str_vars.insert(vid, m);
                            }
                            _ => {} // drop if only on one side
                        }
                    }

                    // Heap strings: same treatment
                    let all_hstr_keys: HashSet<_> = then_heap_str
                        .keys()
                        .chain(else_heap_str.keys())
                        .cloned()
                        .collect();
                    self.heap_str.clear();
                    for k in all_hstr_keys {
                        match (then_heap_str.get(&k).copied(), else_heap_str.get(&k).copied()) {
                            (Some(t), Some(e)) if t == e => {
                                self.heap_str.insert(k, t);
                            }
                            (Some(t), Some(e)) => {
                                let m = self.solver.ite(cond_nz, t, e);
                                self.heap_str.insert(k, m);
                            }
                            (Some(t), None) => {
                                self.heap_str.insert(k, t);
                            }
                            (None, Some(e)) => {
                                self.heap_str.insert(k, e);
                            }
                            (None, None) => {}
                        }
                    }

                    // Continue from join point
                    self.explore_block_until(join, 0, stop_at);
                } else {
                    // No join point found — fall back to path forking.
                    // Path constraints replace push/pop: each branch adds
                    // its condition to path_constraints, which is restored
                    // via save/restore_state (truncation).
                    self.fork_count += 1;
                    // Then branch: cond != 0
                    if self.budget_left() {
                        let saved = self.save_state();
                        if cond_tainted {
                            self.path_tainted = true;
                        }
                        self.path_constraints.push(cond_nz);
                        // Prune infeasible branches early.
                        let feas = self.check_sat_with_path();
                        if feas != SatResult::Unsat {
                            self.explore_block_until(*then_, 0, stop_at);
                        }
                        self.restore_state(saved);
                    }

                    // Else branch: cond == 0
                    if self.budget_left() {
                        let saved = self.save_state();
                        if cond_tainted {
                            self.path_tainted = true;
                        }
                        self.path_constraints.push(cond_bool);
                        let feas = self.check_sat_with_path();
                        if feas != SatResult::Unsat {
                            self.explore_block_until(*else_, 0, stop_at);
                        }
                        self.restore_state(saved);
                    }
                }
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let value_tainted = self.operand_tainted(value);
                let vt = self.encode_operand(value);

                // Collect all switch targets for join-point detection.
                let mut all_targets: Vec<BlockId> =
                    cases.iter().map(|(_, t)| *t).collect();
                all_targets.push(*default);

                if let Some(join) = self.find_join_multi(&all_targets) {
                    // Diamond merge for switch: explore each case up to the
                    // join, capture state, then ITE-merge all cases.

                    // Build condition terms for each case.
                    let case_conds: Vec<(i32, BlockId, Term)> = cases
                        .iter()
                        .map(|(cv, t)| {
                            let c = self.solver.bv_const(*cv as i64, 32);
                            let eq = self.solver.bveq(vt, c);
                            (*cv, *t, eq)
                        })
                        .collect();

                    // Explore each case and capture state.
                    type CaseState = (
                        HashMap<VarId, Term>,
                        HashMap<(String, String, String), Term>,
                        HashSet<VarId>,
                        HashSet<(String, String, String)>,
                        HashMap<VarId, Term>,
                        HashMap<(String, String, String), Term>,
                        bool,
                        Vec<(Term, Term)>,
                    );
                    let mut case_states: Vec<(Term, CaseState)> = Vec::new();

                    let mut all_case_nondets: Vec<Vec<(usize, Term, u32, Ty, Option<Term>)>> = Vec::new();
                    for &(_, target, cond_eq) in &case_conds {
                        if !self.budget_left() {
                            break;
                        }
                        let saved = self.save_state();
                        if value_tainted {
                            self.path_tainted = true;
                        }
                        self.path_constraints.push(cond_eq);
                        self.explore_block_until(target, 0, Some(join));
                        case_states.push((cond_eq, (
                            self.vars.clone(),
                            self.heap.clone(),
                            self.tainted.clone(),
                            self.heap_tainted.clone(),
                            self.str_vars.clone(),
                            self.heap_str.clone(),
                            self.path_tainted,
                            self.ordinal_map.clone(),
                        )));
                        all_case_nondets.push(self.nondet_terms.clone());
                        self.restore_state(saved);
                    }

                    // Default case
                    if self.budget_left() {
                        let saved = self.save_state();
                        if value_tainted {
                            self.path_tainted = true;
                        }
                        for &(_, _, cond_eq) in &case_conds {
                            let neq = self.solver.not(cond_eq);
                            self.path_constraints.push(neq);
                        }
                        self.explore_block_until(*default, 0, Some(join));
                        // Default is the base state for the ITE cascade.
                        let mut merged_vars = self.vars.clone();
                        let mut merged_heap = self.heap.clone();
                        let mut merged_tainted = self.tainted.clone();
                        let mut merged_heap_tainted = self.heap_tainted.clone();
                        let mut merged_str = self.str_vars.clone();
                        let mut merged_heap_str = self.heap_str.clone();
                        let mut merged_pt = self.path_tainted;
                        let mut merged_ordinals = self.ordinal_map.clone();
                        all_case_nondets.push(self.nondet_terms.clone());
                        self.restore_state(saved);

                        // Preserve nondets from all switch cases.
                        let base_len = self.nondet_terms.len();
                        for case_nds in &all_case_nondets {
                            for nd in &case_nds[base_len..] {
                                if !self.nondet_terms.iter().any(|(idx, _, _, _, _)| *idx == nd.0) {
                                    self.nondet_terms.push(nd.clone());
                                }
                            }
                        }

                        // ITE-merge each case on top of the accumulated state,
                        // building the cascade from the last case back to first.
                        for (cond_eq, cs) in case_states.iter().rev() {
                            let (cv, ch, ct, cht, csv, chs, cpt, cord) = cs;

                            // Merge vars
                            let all_vids: HashSet<VarId> = cv.keys()
                                .chain(merged_vars.keys())
                                .copied()
                                .collect();
                            for vid in all_vids {
                                match (cv.get(&vid).copied(), merged_vars.get(&vid).copied()) {
                                    (Some(a), Some(b)) if a == b => {}
                                    (Some(a), Some(b)) => {
                                        let m = self.solver.ite(*cond_eq, a, b);
                                        merged_vars.insert(vid, m);
                                    }
                                    (Some(a), None) => {
                                        let fresh = self.solver.fresh_bv("sw_merge", self.width_of_var(vid));
                                        let m = self.solver.ite(*cond_eq, a, fresh);
                                        merged_vars.insert(vid, m);
                                    }
                                    (None, Some(_)) => {} // keep merged
                                    (None, None) => {}
                                }
                            }

                            // Merge heap
                            let all_hk: HashSet<_> = ch.keys()
                                .chain(merged_heap.keys())
                                .cloned()
                                .collect();
                            for k in all_hk {
                                match (ch.get(&k).copied(), merged_heap.get(&k).copied()) {
                                    (Some(a), Some(b)) if a == b => {}
                                    (Some(a), Some(b)) => {
                                        let m = self.solver.ite(*cond_eq, a, b);
                                        merged_heap.insert(k, m);
                                    }
                                    (Some(a), None) => {
                                        merged_heap.insert(k, a);
                                    }
                                    (None, Some(_)) => {}
                                    (None, None) => {}
                                }
                            }

                            // Taint: conservative union
                            merged_tainted = &merged_tainted | ct;
                            merged_heap_tainted = &merged_heap_tainted | cht;
                            merged_pt = merged_pt || *cpt;

                            // Ordinals: union entries (ITE chain handles resolution)
                            for entry in cord {
                                if !merged_ordinals.contains(entry) {
                                    merged_ordinals.push(entry.clone());
                                }
                            }

                            // String vars and heap strings
                            let all_sv: HashSet<VarId> = csv.keys()
                                .chain(merged_str.keys())
                                .copied()
                                .collect();
                            for vid in all_sv {
                                match (csv.get(&vid).copied(), merged_str.get(&vid).copied()) {
                                    (Some(a), Some(b)) if a == b => {}
                                    (Some(a), Some(b)) => {
                                        let m = self.solver.ite(*cond_eq, a, b);
                                        merged_str.insert(vid, m);
                                    }
                                    _ => {}
                                }
                            }
                            let all_hsk: HashSet<_> = chs.keys()
                                .chain(merged_heap_str.keys())
                                .cloned()
                                .collect();
                            for k in all_hsk {
                                match (chs.get(&k).copied(), merged_heap_str.get(&k).copied()) {
                                    (Some(a), Some(b)) if a == b => {}
                                    (Some(a), Some(b)) => {
                                        let m = self.solver.ite(*cond_eq, a, b);
                                        merged_heap_str.insert(k, m);
                                    }
                                    (Some(a), None) => {
                                        merged_heap_str.insert(k, a);
                                    }
                                    (None, Some(_)) => {}
                                    (None, None) => {}
                                }
                            }
                        }

                        // Apply merged state
                        self.vars = merged_vars;
                        self.heap = merged_heap;
                        self.tainted = merged_tainted;
                        self.heap_tainted = merged_heap_tainted;
                        self.str_vars = merged_str;
                        self.heap_str = merged_heap_str;
                        self.path_tainted = merged_pt;
                        self.ordinal_map = merged_ordinals;

                        // Continue from join
                        self.explore_block_until(join, 0, stop_at);
                    }
                } else {
                    // No join point — fall back to fork-based exploration.
                    for (case_val, target) in cases {
                        if !self.budget_left() {
                            break;
                        }
                        self.fork_count += 1;
                        let saved = self.save_state();
                        if value_tainted {
                            self.path_tainted = true;
                        }
                        let cv = self.solver.bv_const(*case_val as i64, 32);
                        let eq = self.solver.bveq(vt, cv);
                        self.path_constraints.push(eq);
                        self.explore_block_until(*target, 0, stop_at);
                        self.restore_state(saved);
                    }

                    if self.budget_left() {
                        let saved = self.save_state();
                        if value_tainted {
                            self.path_tainted = true;
                        }
                        for (case_val, _) in cases {
                            let cv = self.solver.bv_const(*case_val as i64, 32);
                            let eq = self.solver.bveq(vt, cv);
                            let neq = self.solver.not(eq);
                            self.path_constraints.push(neq);
                        }
                        self.explore_block_until(*default, 0, stop_at);
                        self.restore_state(saved);
                    }
                }
            }
            // Path ends.
            Terminator::Return(Some(val)) => {
                // Capture return value for try_inline_call propagation.
                if self.call_depth > 0 {
                    self.inline_return = Some(self.encode_operand(val));
                }
            }
            Terminator::Return(None)
            | Terminator::Halt
            | Terminator::Throw(_)
            | Terminator::Diverge(_) => {}
        }
        self.depth -= 1;
    }
}
