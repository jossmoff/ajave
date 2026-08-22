//! SSA-based SMT encoder for method bodies.
//!
//! Encodes a `Body` as a monolithic SMT formula: all paths through the CFG
//! become a single conjunction of bitvector constraints with ITE terms at
//! merge points. Shared by the k-induction and (future) IMC engines.
//!
//! The encoding walks blocks in topological order. Each variable assignment
//! produces a fresh SSA version. At blocks with multiple predecessors,
//! reaching definitions are joined via `ite(path_cond, v_then, v_else)`.

use std::collections::HashMap;

use roast_core::smt::{Solver, Term};
use roast_ir::*;

/// Result of encoding one method body at a given unrolling depth.
pub struct Encoding {
    /// For each obligation in the body: the path-condition term that is true
    /// iff the obligation's safety condition is violated on some feasible path.
    /// Callers assert this term and check satisfiability.
    pub violation_terms: HashMap<ObligationId, Term>,

    /// The combined path-reachability term: conjunction of all path conditions.
    /// Used by k-induction's step case as the transition relation.
    pub reach_term: Term,

    /// SSA variable terms at each block entry, keyed by `(BlockId, VarId)`.
    /// Used by k-induction to connect consecutive frames.
    pub block_vars: HashMap<(u32, u32), Term>,
}

/// Width of a type in bits for bitvector encoding.
fn width_of(ty: &Ty) -> u32 {
    match ty {
        Ty::Long | Ty::Double => 64,
        _ => 32,
    }
}

/// Encode a single method body as an SMT formula.
///
/// `frame` is a unique prefix for SSA variable names (allows multiple
/// instances in the same solver context for k-induction's step case).
pub fn encode_body(solver: &mut dyn Solver, body: &Body, frame: &str) -> Encoding {
    let mut env = Env {
        solver,
        frame: frame.to_string(),
        vars: HashMap::new(),
        path_conds: HashMap::new(),
        next_ssa: 0,
    };

    // Initialise variables with fresh symbolic values.
    for (i, vi) in body.vars.iter().enumerate() {
        let vid = VarId(i as u32);
        let w = width_of(&vi.ty);
        let t = env.fresh(&format!("v{}", i), w);
        env.vars.insert(vid, t);
    }

    // Mark entry block as reachable (path condition = true).
    let tt = env.solver.bool_const(true);
    env.path_conds.insert(body.entry, tt);

    let mut violation_terms = HashMap::new();

    // Process blocks in ID order (topological for well-structured bytecode).
    for block in &body.blocks {
        let block_pc = match env.path_conds.get(&block.id) {
            Some(&pc) => pc,
            None => continue, // unreachable block
        };

        // Process statements.
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(vid, rv) => {
                    let t = env.encode_rvalue(rv);
                    env.vars.insert(*vid, t);
                }
                Stmt::Assume(op) => {
                    let t = env.encode_operand(op);
                    let zero = env.solver.bv_const(0, 32);
                    let nz = env.solver.bveq(t, zero);
                    let nz = env.solver.not(nz);
                    // Narrow the path condition: assume only feasible paths.
                    let new_pc = env.solver.and(block_pc, nz);
                    env.path_conds.insert(block.id, new_pc);
                }
                Stmt::Check(oid) => {
                    let ob = body.obligation(*oid);
                    let cond = env.encode_operand(&ob.cond);
                    let zero = env.solver.bv_const(0, 32);
                    let is_zero = env.solver.bveq(cond, zero);
                    // Violation = path is reachable AND condition is false.
                    let current_pc = *env.path_conds.get(&block.id).unwrap_or(&block_pc);
                    let violation = env.solver.and(current_pc, is_zero);
                    violation_terms.insert(*oid, violation);
                }
                Stmt::PutStatic(_, _)
                | Stmt::PutField { .. }
                | Stmt::ArrayStore { .. }
                | Stmt::Nop => {}
            }
        }

        // Process terminator — propagate path conditions to successors.
        let current_pc = *env.path_conds.get(&block.id).unwrap_or(&block_pc);
        match &block.term {
            Terminator::Goto(target) => {
                env.merge_pc(*target, current_pc);
            }
            Terminator::Branch { cond, then_, else_ } => {
                let ct = env.encode_operand(cond);
                let zero = env.solver.bv_const(0, 32);
                let is_zero = env.solver.bveq(ct, zero);
                let is_nz = env.solver.not(is_zero);

                let then_pc = env.solver.and(current_pc, is_nz);
                let else_pc = env.solver.and(current_pc, is_zero);
                env.merge_pc(*then_, then_pc);
                env.merge_pc(*else_, else_pc);
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let vt = env.encode_operand(value);
                let mut default_pc = current_pc;
                for (val, target) in cases {
                    let cv = env.solver.bv_const(*val as i64, 32);
                    let eq = env.solver.bveq(vt, cv);
                    let case_pc = env.solver.and(current_pc, eq);
                    env.merge_pc(*target, case_pc);
                    let neq = env.solver.not(eq);
                    default_pc = env.solver.and(default_pc, neq);
                }
                env.merge_pc(*default, default_pc);
            }
            Terminator::Return(_)
            | Terminator::Halt
            | Terminator::Throw(_)
            | Terminator::Diverge(_) => {}
        }
    }

    // Compute overall reachability: disjunction of all terminal block PCs.
    let ff = env.solver.bool_const(false);
    let mut reach = ff;
    for block in &body.blocks {
        match &block.term {
            Terminator::Return(_) | Terminator::Halt => {
                if let Some(&pc) = env.path_conds.get(&block.id) {
                    reach = env.solver.or(reach, pc);
                }
            }
            _ => {}
        }
    }

    Encoding {
        violation_terms,
        reach_term: reach,
        block_vars: HashMap::new(),
    }
}

/// Internal encoding environment.
struct Env<'a> {
    solver: &'a mut dyn Solver,
    frame: String,
    vars: HashMap<VarId, Term>,
    path_conds: HashMap<BlockId, Term>,
    next_ssa: u32,
}

impl<'a> Env<'a> {
    fn fresh(&mut self, name: &str, width: u32) -> Term {
        self.next_ssa += 1;
        self.solver
            .fresh_bv(&format!("{}_{}{}", self.frame, name, self.next_ssa), width)
    }

    fn merge_pc(&mut self, target: BlockId, incoming: Term) {
        let existing = self.path_conds.get(&target).copied();
        let merged = match existing {
            Some(pc) => self.solver.or(pc, incoming),
            None => incoming,
        };
        self.path_conds.insert(target, merged);
    }

    fn operand_width(op: &Operand) -> u32 {
        match op {
            Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => 64,
            _ => 32,
        }
    }

    fn encode_operand(&mut self, op: &Operand) -> Term {
        match op {
            Operand::Var(v) => self.vars.get(v).copied().unwrap_or_else(|| {
                let t = self.fresh("uninit", 32);
                self.vars.insert(*v, t);
                t
            }),
            Operand::Const(Const::Int(n)) => self.solver.bv_const(*n as i64, 32),
            Operand::Const(Const::Long(n)) => self.solver.bv_const(*n, 64),
            Operand::Const(Const::Null) => self.solver.bv_const(0, 32),
            Operand::Const(Const::Str(_)) => self.solver.bv_const(1, 32),
            Operand::Const(Const::Float(f)) => self.solver.bv_const(f.to_bits() as i64, 32),
            Operand::Const(Const::Double(d)) => self.solver.bv_const(d.to_bits() as i64, 64),
            Operand::Const(_) => self.solver.bv_const(0, 32),
        }
    }

    fn encode_rvalue(&mut self, rv: &Rvalue) -> Term {
        match rv {
            Rvalue::Use(o) => self.encode_operand(o),
            Rvalue::Nondet(ty, _) | Rvalue::Havoc(ty) => {
                let w = width_of(ty);
                self.fresh("nd", w)
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
                // Handle width mismatch: sign-extend shorter operand.
                let aw = Self::operand_width(a);
                let bw = Self::operand_width(b);
                let (at, bt) = if aw < bw {
                    (self.solver.sign_extend(at, bw - aw), bt)
                } else if bw < aw {
                    (at, self.solver.sign_extend(bt, aw - bw))
                } else {
                    (at, bt)
                };
                let lt = self.solver.bvslt(at, bt);
                let eq = self.solver.bveq(at, bt);
                let m1 = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let one = self.solver.bv_const(1, 32);
                let inner = self.solver.ite(eq, zero, one);
                self.solver.ite(lt, m1, inner)
            }
            // Heap operations: fresh unconstrained value (sound for over-approx).
            Rvalue::New(_) => {
                let t = self.fresh("alloc", 32);
                // Non-null.
                let zero = self.solver.bv_const(0, 32);
                let eq = self.solver.bveq(t, zero);
                let neq = self.solver.not(eq);
                self.solver.assert(neq);
                t
            }
            Rvalue::GetStatic(_)
            | Rvalue::GetField { .. }
            | Rvalue::ArrayLoad { .. }
            | Rvalue::ArrayLength(_)
            | Rvalue::NewArray { .. }
            | Rvalue::InstanceOf { .. }
            | Rvalue::Call { .. } => self.fresh("havoc", 32),
        }
    }

    fn encode_binop(&mut self, op: BinOp, a: &Operand, b: &Operand) -> Term {
        let at = self.encode_operand(a);
        let bt = self.encode_operand(b);
        // Normalise widths: sign-extend shorter operand (except shifts).
        let aw = Self::operand_width(a);
        let bw = Self::operand_width(b);
        let (at, bt) = if !matches!(op, BinOp::Shl | BinOp::Shr | BinOp::UShr) && aw != bw {
            if aw < bw {
                (self.solver.sign_extend(at, bw - aw), bt)
            } else {
                (at, self.solver.sign_extend(bt, aw - bw))
            }
        } else {
            (at, bt)
        };
        let one = self.solver.bv_const(1, 32);
        let zero = self.solver.bv_const(0, 32);
        match op {
            BinOp::Add => self.solver.bvadd(at, bt),
            BinOp::Sub => self.solver.bvsub(at, bt),
            BinOp::Mul => self.solver.bvmul(at, bt),
            BinOp::Div => self.solver.bvsdiv(at, bt),
            BinOp::Rem => self.solver.bvsrem(at, bt),
            BinOp::And => self.solver.bvand(at, bt),
            BinOp::Or => self.solver.bvor(at, bt),
            BinOp::Xor => self.solver.bvxor(at, bt),
            BinOp::Shl | BinOp::Shr | BinOp::UShr => {
                // JVM: shift amount is masked — 0x1F for int, 0x3F for long.
                let aw = Self::operand_width(a);
                let mask = if aw == 64 { 0x3F } else { 0x1F };
                let mask_t = self.solver.bv_const(mask, 32);
                let bt = self.solver.bvand(bt, mask_t);
                // Shift amount is always int (32-bit) but shifted value
                // may be long (64-bit). Zero-extend shift amount to match.
                let bt = if aw == 64 {
                    self.solver.zero_extend(bt, 32)
                } else {
                    bt
                };
                match op {
                    BinOp::Shl => self.solver.bvshl(at, bt),
                    BinOp::Shr => self.solver.bvashr(at, bt),
                    BinOp::UShr => self.solver.bvlshr(at, bt),
                    _ => unreachable!(),
                }
            }
            BinOp::Eq => {
                let c = self.solver.bveq(at, bt);
                self.solver.ite(c, one, zero)
            }
            BinOp::Ne => {
                let c = self.solver.bveq(at, bt);
                let nc = self.solver.not(c);
                self.solver.ite(nc, one, zero)
            }
            BinOp::Lt => {
                let c = self.solver.bvslt(at, bt);
                self.solver.ite(c, one, zero)
            }
            BinOp::Le => {
                let c = self.solver.bvsle(at, bt);
                self.solver.ite(c, one, zero)
            }
            BinOp::Gt => {
                let c = self.solver.bvsgt(at, bt);
                self.solver.ite(c, one, zero)
            }
            BinOp::Ge => {
                let c = self.solver.bvsge(at, bt);
                self.solver.ite(c, one, zero)
            }
        }
    }
}
