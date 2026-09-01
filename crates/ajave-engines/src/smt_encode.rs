//! SSA-based SMT encoder for method bodies.
//!
//! Encodes a `Body` as a single formula over bitvectors: every path through
//! the CFG is one disjunct, and reaching definitions are joined at merge
//! points with `ite`.
//!
//! # Completeness is part of the result
//!
//! An `Encoding` is only a faithful description of the body when
//! [`Encoding::complete`] is true. The encoder walks each block once, so it
//! describes **one pass** through any loop, and it does not model exceptional
//! edges or unlifted instructions. A caller that wants to conclude "no
//! violation is possible" — as opposed to "no violation on the paths I
//! encoded" — must check the flag.
//!
//! This is not a hypothetical. Both defects below produced a claimed proof for
//! a program that violates its assertion, and both are pinned by tests in
//! `kinduction.rs` (#76):
//!
//! * **Back-edges.** A back-edge targets a block that has already been
//!   processed, so it is dropped. The formula covers one iteration, on which
//!   a property that first fails on the second iteration still holds.
//! * **Merge points.** Reaching definitions used to be threaded through a
//!   single map that each block overwrote in turn, so a join read whatever
//!   the last-processed predecessor assigned rather than an `ite` over both.
//!   The violating branch was absent from the formula entirely. That one is
//!   *fixed* here rather than reported; the traversal below merges properly.
//!
//! Reads of the heap are fresh unconstrained values. That is sound in the
//! direction that matters — an arbitrary value covers whatever the real heap
//! holds — but it means no property that depends on a stored value is
//! provable. Writes are correspondingly dropped.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ajave_core::smt::{Solver, Term};
use ajave_ir::*;

/// Reaching definitions at a program point, keyed by variable.
type VarMap = BTreeMap<VarId, Term>;

/// Result of encoding one method body.
pub struct Encoding {
    /// For each obligation the encoder reached: the term that is true iff the
    /// obligation's safety condition is violated on some encoded path.
    ///
    /// An obligation that is in the body but missing here was **not encoded**
    /// — it sits behind an edge this encoder does not follow. Absence is not
    /// evidence of safety.
    pub violation_terms: HashMap<ObligationId, Term>,

    /// Disjunction of the path conditions of all returning blocks.
    pub reach_term: Term,

    /// Whether the encoding covers every execution of the body.
    ///
    /// False when the CFG has a back-edge (only one iteration is encoded),
    /// when a reachable block ends in `Diverge` (an instruction the lifter
    /// could not model), or when a reachable block has exceptional successors
    /// (handler code is not encoded). A `false` here forbids concluding
    /// safety from an UNSAT violation term.
    pub complete: bool,
}

/// Width of a type in bits for bitvector encoding.
fn width_of(ty: &Ty) -> u32 {
    match ty {
        Ty::Long | Ty::Double => 64,
        _ => 32,
    }
}

/// Width of a field from its JVM descriptor (e.g. "J" → 64, "I" → 32).
fn field_width(desc: &str) -> u32 {
    match desc.as_bytes().first() {
        Some(b'J') | Some(b'D') => 64,
        _ => 32,
    }
}

/// Width of a method's return type from its JVM descriptor (e.g. "(I)J" → 64).
fn return_width(desc: &str) -> u32 {
    let after_paren = desc.split(')').nth(1).unwrap_or("V");
    match after_paren.as_bytes().first() {
        Some(b'J') | Some(b'D') => 64,
        _ => 32,
    }
}

/// Successors of a block along normal (non-exceptional) control flow.
fn successors(block: &Block) -> Vec<BlockId> {
    match &block.term {
        Terminator::Goto(t) => vec![*t],
        Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
        Terminator::Switch { cases, default, .. } => {
            let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
            v.push(*default);
            v
        }
        Terminator::Return(_) | Terminator::Halt
        | Terminator::Throw(_) | Terminator::Diverge(_) => vec![],
    }
}

/// Reverse post-order over forward edges, plus the set of back-edges found.
///
/// An edge to a block that is grey — on the current DFS stack — closes a
/// cycle. Processing the returned order guarantees every *forward* predecessor
/// of a block is encoded before the block itself, which is what makes the
/// merge at a join point well defined.
fn rpo_and_back_edges(body: &Body) -> (Vec<BlockId>, BTreeSet<(BlockId, BlockId)>) {
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        White,
        Grey,
        Black,
    }
    let n = body.blocks.len();
    let mut colour = vec![Colour::White; n];
    let mut post = Vec::with_capacity(n);
    let mut back = BTreeSet::new();

    // Explicit stack: bytecode from a deeply nested method can otherwise
    // overflow a recursive DFS.
    let mut stack: Vec<(BlockId, usize)> = vec![(body.entry, 0)];
    if let Some(c) = colour.get_mut(body.entry.0 as usize) {
        *c = Colour::Grey;
    }
    while let Some((bid, next)) = stack.pop() {
        let idx = bid.0 as usize;
        let Some(block) = body.blocks.get(idx) else { continue };
        let succs = successors(block);
        if next < succs.len() {
            stack.push((bid, next + 1));
            let s = succs[next];
            match colour.get(s.0 as usize) {
                Some(Colour::White) => {
                    colour[s.0 as usize] = Colour::Grey;
                    stack.push((s, 0));
                }
                Some(Colour::Grey) => {
                    back.insert((bid, s));
                }
                _ => {}
            }
        } else {
            colour[idx] = Colour::Black;
            post.push(bid);
        }
    }
    post.reverse();
    (post, back)
}

/// Encode a method body as an SMT formula.
///
/// `frame` prefixes every SSA name, so several encodings can share one solver
/// context without their variables colliding.
pub fn encode_body(
    solver: &mut dyn Solver,
    body: &Body,
    frame: &str,
) -> Encoding {
    let mut env = Env {
        solver,
        frame: frame.to_string(),
        vars: VarMap::new(),
        next_ssa: 0,
    };

    // Every local starts as an unconstrained symbolic value. Constraining
    // them is the caller's job; leaving them free over-approximates the
    // reachable states, which is the safe direction for a safety claim.
    let mut init = VarMap::new();
    for (i, vi) in body.vars.iter().enumerate() {
        let vid = VarId(i as u32);
        let w = width_of(&vi.ty);
        let t = env.fresh(&format!("v{i}"), w);
        init.insert(vid, t);
    }

    let (order, back_edges) = rpo_and_back_edges(body);
    let mut complete = back_edges.is_empty();

    // Pending incoming edges per block: (edge path condition, state on entry
    // along that edge). Merged into a single state when the block is reached.
    let mut incoming: BTreeMap<BlockId, Vec<(Term, VarMap)>> = BTreeMap::new();
    let tt = env.solver.bool_const(true);
    incoming.insert(body.entry, vec![(tt, init)]);

    let mut violation_terms = HashMap::new();
    let mut returning: Vec<Term> = Vec::new();

    for bid in order {
        let Some(edges) = incoming.remove(&bid) else {
            // No encoded edge reaches this block. Either it is genuinely
            // unreachable, or every path to it is a back-edge — in which case
            // `complete` is already false.
            continue;
        };
        let Some(block) = body.blocks.get(bid.0 as usize) else { continue };
        let (mut pc, state) = env.merge(edges);
        env.vars = state;

        // Handler code is not encoded, so a block that can transfer control
        // into a handler has successors this formula does not describe.
        if !block.exceptional.is_empty() {
            complete = false;
        }

        for stmt in &block.stmts {
            match stmt {
                // A monitor imposes no constraint on a sequential encoding.
                Stmt::MonitorEnter(_) | Stmt::MonitorExit(_) => {}
                Stmt::Assign(vid, rv) => {
                    let t = env.encode_rvalue(rv);
                    env.vars.insert(*vid, t);
                }
                Stmt::Assume(op) => {
                    let t = env.encode_operand(op);
                    let zero = env.solver.bv_const(0, 32);
                    let is_zero = env.solver.bveq(t, zero);
                    let nz = env.solver.not(is_zero);
                    pc = env.solver.and(pc, nz);
                }
                Stmt::Check(oid) => {
                    let ob = body.obligation(*oid);
                    let cond = env.encode_operand(&ob.cond);
                    let zero = env.solver.bv_const(0, 32);
                    let is_zero = env.solver.bveq(cond, zero);
                    let violation = env.solver.and(pc, is_zero);
                    // A block can be reached along several edges but is
                    // encoded once, so each obligation is written once.
                    violation_terms.insert(*oid, violation);
                }
                // Heap writes are dropped, matching heap reads being fresh
                // unconstrained values.
                Stmt::PutStatic(_, _)
                | Stmt::PutField { .. }
                | Stmt::ArrayStore { .. }
                | Stmt::Nop => {}
            }
        }

        let mut send = |env: &mut Env, target: BlockId, edge_pc: Term| {
            if back_edges.contains(&(bid, target)) {
                return;
            }
            incoming
                .entry(target)
                .or_default()
                .push((edge_pc, env.vars.clone()));
        };

        match &block.term {
            Terminator::Goto(target) => send(&mut env, *target, pc),
            Terminator::Branch { cond, then_, else_ } => {
                let ct = env.encode_operand(cond);
                let zero = env.solver.bv_const(0, 32);
                let is_zero = env.solver.bveq(ct, zero);
                let is_nz = env.solver.not(is_zero);
                let then_pc = env.solver.and(pc, is_nz);
                let else_pc = env.solver.and(pc, is_zero);
                send(&mut env, *then_, then_pc);
                send(&mut env, *else_, else_pc);
            }
            Terminator::Switch { value, cases, default } => {
                let vt = env.encode_operand(value);
                let mut default_pc = pc;
                for (val, target) in cases {
                    let cv = env.solver.bv_const(*val as i64, 32);
                    let eq = env.solver.bveq(vt, cv);
                    let case_pc = env.solver.and(pc, eq);
                    send(&mut env, *target, case_pc);
                    let neq = env.solver.not(eq);
                    default_pc = env.solver.and(default_pc, neq);
                }
                send(&mut env, *default, default_pc);
            }
            Terminator::Return(_) | Terminator::Halt => returning.push(pc),
            // An instruction the lifter could not model. Whatever happens
            // after it is not in this formula.
            Terminator::Diverge(_) => complete = false,
            Terminator::Throw(_) => {}
        }
    }

    let ff = env.solver.bool_const(false);
    let mut reach = ff;
    for pc in returning {
        reach = env.solver.or(reach, pc);
    }

    Encoding {
        violation_terms,
        reach_term: reach,
        complete,
    }
}

/// Internal encoding environment.
struct Env<'a> {
    solver: &'a mut dyn Solver,
    frame: String,
    vars: VarMap,
    next_ssa: u32,
}

impl<'a> Env<'a> {
    fn fresh(&mut self, name: &str, width: u32) -> Term {
        self.next_ssa += 1;
        self.solver
            .fresh_bv(&format!("{}_{}{}", self.frame, name, self.next_ssa), width)
    }

    /// Join the states arriving on several edges into one.
    ///
    /// The path condition is the disjunction of the edge conditions; each
    /// variable becomes `ite(edge_pc, value_on_that_edge, rest)`. Folding from
    /// the last edge backwards makes the first edge the outermost test, so
    /// the term is determined by edge order rather than by map iteration
    /// order — the encoder must not depend on a hash seed.
    fn merge(&mut self, mut edges: Vec<(Term, VarMap)>) -> (Term, VarMap) {
        if edges.len() == 1 {
            return edges.pop().expect("length checked");
        }
        let mut pc = self.solver.bool_const(false);
        for (epc, _) in &edges {
            pc = self.solver.or(pc, *epc);
        }

        let keys: BTreeSet<VarId> = edges.iter().flat_map(|(_, m)| m.keys().copied()).collect();
        let mut merged = VarMap::new();
        for k in keys {
            // Seed with the last edge's value so the fold has a base case;
            // its guard is implied by the disjunction of the others.
            let mut acc = None;
            for (epc, m) in edges.iter().rev() {
                let Some(&v) = m.get(&k) else { continue };
                acc = Some(match acc {
                    None => v,
                    Some(rest) => self.solver.ite(*epc, v, rest),
                });
            }
            if let Some(t) = acc {
                merged.insert(k, t);
            }
        }
        (pc, merged)
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
            Rvalue::Nondet(ty, _) | Rvalue::Havoc(ty, _) => {
                let w = width_of(ty);
                self.fresh("nd", w)
            }
            Rvalue::Bin(op, a, b) => self.encode_binop(*op, a, b),
            Rvalue::Neg(o) => {
                let t = self.encode_operand(o);
                self.solver.bvneg(t)
            }
            Rvalue::Cast(ty, _src, o) => {
                let t = self.encode_operand(o);
                match ty {
                    Ty::Long => self.solver.sign_extend(t, 32),
                    Ty::Int => self.solver.extract(t, 31, 0),
                    _ => t,
                }
            }
            Rvalue::Cmp(_, a, b) => {
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
            Rvalue::GetStatic(fk) | Rvalue::GetField { field: fk, .. } => {
                let w = field_width(&fk.desc);
                self.fresh("havoc", w)
            }
            Rvalue::ArrayLoad { .. } | Rvalue::ArrayLength(_)
            | Rvalue::NewArray { .. } | Rvalue::InstanceOf { .. } => self.fresh("havoc", 32),
            Rvalue::Call { target, .. } => {
                let w = return_width(&target.desc);
                self.fresh("havoc", w)
            }
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
