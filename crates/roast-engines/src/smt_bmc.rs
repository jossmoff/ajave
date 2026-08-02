//! SMT-backed bounded model checker.
//!
//! Encodes paths symbolically and asks a solver for satisfying assignments,
//! replacing the concrete engine's "enumerate, don't solve" with "solve, don't
//! enumerate". Finds any bug reachable within bounded depth for arbitrary
//! integer/long inputs, not just a fixed candidate pool.
//!
//! Direction: Under. JvmReplay confirms all witnesses.

use std::collections::HashMap;

use log::{debug, info, warn};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_core::smt::{SatResult, Solver, SolverFactory, Term};
use roast_ir::verdict::{NondetEntry, NondetValue, Witness};
use roast_ir::*;

/// Maximum number of solver check-sat calls per run to prevent hangs.
const MAX_SOLVER_CALLS: u32 = 500;

/// Maximum number of violations to collect before stopping exploration.
const MAX_VIOLATIONS: usize = 50;

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
            body,
            vars: HashMap::new(),
            nondet_terms: Vec::new(),
            violations: Vec::new(),
            depth: 0,
            max_depth: self.max_depth,
            solver_calls: 0,
            exhausted: false,
        };

        ctx.explore_block(body.entry, 0);

        let violations = std::mem::take(&mut ctx.violations);
        debug!(
            "smt-bmc: exploration complete, found {} violation(s), {} solver calls",
            violations.len(),
            ctx.solver_calls
        );

        let mut advanced = false;
        for (oid, witness) in violations {
            let oref = ObligationRef {
                method: entry.clone(),
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
    body: &'a Body,
    /// Current symbolic state: VarId -> Term.
    vars: HashMap<VarId, Term>,
    /// (nondet_index, Term, width, Ty) in encounter order for witness extraction.
    nondet_terms: Vec<(usize, Term, u32, Ty)>,
    /// Found violations.
    violations: Vec<(ObligationId, Witness)>,
    depth: u32,
    max_depth: u32,
    /// Number of check-sat calls made.
    solver_calls: u32,
    /// Set when budget is exhausted; stops further exploration.
    exhausted: bool,
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

    fn encode_operand(&mut self, op: &Operand) -> Term {
        match op {
            Operand::Var(v) => self.get_var(*v),
            Operand::Const(Const::Int(n)) => self.solver.bv_const(*n as i64, 32),
            Operand::Const(Const::Long(n)) => self.solver.bv_const(*n, 64),
            Operand::Const(Const::Null) => self.solver.bv_const(0, 32),
            Operand::Const(_) => self.solver.fresh_bv("const", 32),
        }
    }

    fn encode_rvalue(&mut self, rv: &Rvalue) -> Term {
        match rv {
            Rvalue::Use(o) => self.encode_operand(o),
            Rvalue::Nondet(ty) => {
                let w = self.width_of_ty(ty);
                let idx = self.nondet_terms.len();
                let t = self.solver.fresh_bv(&format!("nd_{idx}"), w);
                // Only record Int/Long/Str nondets for witness extraction.
                // Ref nondets are not consumed by JvmReplay (the concrete
                // engine doesn't record them either).
                if *ty != Ty::Ref {
                    self.nondet_terms.push((idx, t, w, *ty));
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
            // Heap ops: fresh unconstrained (sound for Under).
            Rvalue::GetStatic(_)
            | Rvalue::GetField { .. }
            | Rvalue::ArrayLoad { .. }
            | Rvalue::ArrayLength(_)
            | Rvalue::New(_)
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
            // Comparisons return int 0/1 in the IR.
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
        let info: Vec<(Term, u32, Ty)> = self
            .nondet_terms
            .iter()
            .map(|(_, t, w, ty)| (*t, *w, *ty))
            .collect();
        let mut seq = Vec::new();
        let mut entries = Vec::new();
        for (t, w, ty) in &info {
            let val = self.solver.get_value_i64(*t).unwrap_or(0);
            let raw = if *w <= 32 { val as i32 as i64 } else { val };
            seq.push(raw);
            let (value, method) = match ty {
                Ty::Long => (NondetValue::Long(raw), "nondetLong"),
                Ty::Str => {
                    // SMT doesn't model strings; the raw value is the pool index.
                    let pool = ["", "a", "ab", "abcde", "aaaaa", "hello", "abc", "test"];
                    let len = pool.len() as i64;
                    let idx = ((raw % len + len) % len) as usize;
                    (NondetValue::Str(pool[idx].to_owned()), "nondetString")
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
                    let t = self.encode_rvalue(rv);
                    self.vars.insert(*v, t);
                }
                Stmt::Assume(op) => {
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
                    let ob = self.body.obligation(*oid);
                    let cond = self.encode_operand(&ob.cond);
                    // Check if violation is reachable: assert cond == 0.
                    self.solver.push();
                    self.assert_zero(cond);
                    let res = self.check_sat();
                    if res == SatResult::Sat {
                        let witness = self.extract_witness();
                        self.violations.push((*oid, witness));
                    }
                    self.solver.pop();
                }
                Stmt::PutStatic(..)
                | Stmt::PutField { .. }
                | Stmt::ArrayStore { .. }
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
                self.explore_block(*t, 0);
            }
            Terminator::Branch { cond, then_, else_ } => {
                let ct = self.encode_operand(cond);

                // Then branch: cond != 0
                if self.budget_left() {
                    let saved_vars = self.vars.clone();
                    let saved_nondets = self.nondet_terms.clone();
                    self.solver.push();
                    self.assert_nonzero(ct);
                    self.explore_block(*then_, 0);
                    self.solver.pop();
                    self.vars = saved_vars;
                    self.nondet_terms = saved_nondets;
                }

                // Else branch: cond == 0
                if self.budget_left() {
                    let saved_vars = self.vars.clone();
                    let saved_nondets = self.nondet_terms.clone();
                    self.solver.push();
                    self.assert_zero(ct);
                    self.explore_block(*else_, 0);
                    self.solver.pop();
                    self.vars = saved_vars;
                    self.nondet_terms = saved_nondets;
                }
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let vt = self.encode_operand(value);

                for (case_val, target) in cases {
                    if !self.budget_left() {
                        break;
                    }
                    let saved_vars = self.vars.clone();
                    let saved_nondets = self.nondet_terms.clone();
                    self.solver.push();
                    let cv = self.solver.bv_const(*case_val as i64, 32);
                    let eq = self.solver.bveq(vt, cv);
                    self.solver.assert(eq);
                    self.explore_block(*target, 0);
                    self.solver.pop();
                    self.vars = saved_vars;
                    self.nondet_terms = saved_nondets;
                }

                // Default case: value != any case.
                if self.budget_left() {
                    let saved_vars = self.vars.clone();
                    let saved_nondets = self.nondet_terms.clone();
                    self.solver.push();
                    for (case_val, _) in cases {
                        let cv = self.solver.bv_const(*case_val as i64, 32);
                        let eq = self.solver.bveq(vt, cv);
                        let neq = self.solver.not(eq);
                        self.solver.assert(neq);
                    }
                    self.explore_block(*default, 0);
                    self.solver.pop();
                    self.vars = saved_vars;
                    self.nondet_terms = saved_nondets;
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
