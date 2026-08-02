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
const MAX_SOLVER_CALLS: u32 = 500;

/// Maximum number of violations to collect before stopping exploration.
const MAX_VIOLATIONS: usize = 50;

/// Maximum call inlining depth to prevent infinite recursion.
const MAX_CALL_DEPTH: u32 = 10;

/// Maximum number of times a loop back-edge may be taken on a single path.
const MAX_LOOP_UNROLL: u32 = 5;

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
            tainted: HashSet::new(),
            path_tainted: false,
            call_depth: 0,
            loop_visits: HashMap::new(),
        };

        ctx.explore_block(body.entry, 0);

        let violations = std::mem::take(&mut ctx.violations);
        debug!(
            "smt-bmc: exploration complete, found {} violation(s), {} solver calls",
            violations.len(),
            ctx.solver_calls
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
}

impl<'a> ExploreCtx<'a> {
    fn budget_left(&self) -> bool {
        !self.exhausted
            && self.solver_calls < MAX_SOLVER_CALLS
            && self.violations.len() < MAX_VIOLATIONS
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

    fn rvalue_tainted(&self, rv: &Rvalue) -> bool {
        match rv {
            Rvalue::GetStatic(fk) => {
                let k = Self::field_key(fk);
                if self.heap.contains_key(&k) {
                    self.heap_tainted.contains(&k)
                } else {
                    true
                }
            }
            Rvalue::GetField { field, .. } => {
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
                let k = Self::field_key(fk);
                if let Some(&t) = self.heap.get(&k) {
                    t
                } else {
                    self.solver.fresh_bv("heap", 32)
                }
            }
            Rvalue::GetField { field, .. } => {
                let k = Self::field_key(field);
                if let Some(&t) = self.heap.get(&k) {
                    t
                } else {
                    self.solver.fresh_bv("heap", 32)
                }
            }
            // New: non-null reference.
            Rvalue::New(_) => {
                let t = self.solver.fresh_bv("alloc", 32);
                self.assert_nonzero(t);
                t
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

    /// Assert that a BV term is zero.
    fn assert_zero(&mut self, t: Term) {
        let zero = self.solver.bv_const(0, 32);
        let eq = self.solver.bveq(t, zero);
        self.solver.assert(eq);
    }

    fn check_sat(&mut self) -> SatResult {
        self.solver_calls += 1;
        if self.solver_calls > MAX_SOLVER_CALLS {
            self.exhausted = true;
            return SatResult::Unknown;
        }
        self.solver.check_sat()
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

            // Explore callee — violations inside it are found here
            self.solver.push();
            self.explore_block(callee.entry, 0);
            self.solver.pop();

            // Restore caller state
            self.call_depth -= 1;
            self.body = saved_body;
            self.vars = saved_vars;
            self.str_vars = saved_str_vars;
            self.tainted = saved_tainted;
            self.path_tainted = saved_path_tainted;
        }

        // Return value: unconstrained but NOT tainted (callee was explored).
        let w = self.width_of_var(dest_var);
        let ret_t = self.solver.fresh_bv(&format!("ret_{}", target.name), w);
        self.vars.insert(dest_var, ret_t);

        true
    }

    fn explore_block(&mut self, block_id: BlockId, stmt_idx: usize) {
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
                    self.assert_nonzero(t);
                    // Check if path is still feasible after assume.
                    self.solver.push();
                    let res = self.check_sat();
                    self.solver.pop();
                    if res == SatResult::Unsat {
                        return;
                    }
                }
                Stmt::Check(oid) => {
                    // Skip checks on paths tainted by unmodelled operations —
                    // the solver could produce spurious counterexamples.
                    if self.path_tainted
                        || self.operand_tainted(&self.body.obligation(*oid).cond)
                    {
                        continue;
                    }
                    let ob = self.body.obligation(*oid);
                    let cond = self.encode_operand(&ob.cond);
                    // Check if violation is reachable: assert cond == 0.
                    self.solver.push();
                    self.assert_zero(cond);
                    let res = self.check_sat();
                    if res == SatResult::Sat {
                        let witness = self.extract_witness();
                        self.violations
                            .push((self.body.key.clone(), *oid, witness));
                    }
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
                Stmt::PutField { field, val, .. } => {
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
                        self.explore_block(*t, 0);
                    }
                } else {
                    self.explore_block(*t, 0);
                }
            }
            Terminator::Branch { cond, then_, else_ } => {
                let cond_tainted = self.operand_tainted(cond);
                let ct = self.encode_operand(cond);

                // Then branch: cond != 0
                if self.budget_left() {
                    let saved = self.save_state();
                    if cond_tainted {
                        self.path_tainted = true;
                    }
                    self.solver.push();
                    self.assert_nonzero(ct);
                    self.explore_block(*then_, 0);
                    self.solver.pop();
                    self.restore_state(saved);
                }

                // Else branch: cond == 0
                if self.budget_left() {
                    let saved = self.save_state();
                    if cond_tainted {
                        self.path_tainted = true;
                    }
                    self.solver.push();
                    self.assert_zero(ct);
                    self.explore_block(*else_, 0);
                    self.solver.pop();
                    self.restore_state(saved);
                }
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let value_tainted = self.operand_tainted(value);
                let vt = self.encode_operand(value);

                for (case_val, target) in cases {
                    if !self.budget_left() {
                        break;
                    }
                    let saved = self.save_state();
                    if value_tainted {
                        self.path_tainted = true;
                    }
                    self.solver.push();
                    let cv = self.solver.bv_const(*case_val as i64, 32);
                    let eq = self.solver.bveq(vt, cv);
                    self.solver.assert(eq);
                    self.explore_block(*target, 0);
                    self.solver.pop();
                    self.restore_state(saved);
                }

                // Default case: value != any case.
                if self.budget_left() {
                    let saved = self.save_state();
                    if value_tainted {
                        self.path_tainted = true;
                    }
                    self.solver.push();
                    for (case_val, _) in cases {
                        let cv = self.solver.bv_const(*case_val as i64, 32);
                        let eq = self.solver.bveq(vt, cv);
                        let neq = self.solver.not(eq);
                        self.solver.assert(neq);
                    }
                    self.explore_block(*default, 0);
                    self.solver.pop();
                    self.restore_state(saved);
                }
            }
            // Path ends.
            Terminator::Return(_)
            | Terminator::Halt
            | Terminator::Throw(_)
            | Terminator::Diverge(_) => {}
        }
        self.depth -= 1;
    }
}
