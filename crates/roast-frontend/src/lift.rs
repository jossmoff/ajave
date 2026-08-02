//! Bytecode -> IR.
//!
//! Three passes: decode, find basic-block leaders, then lift each block while
//! simulating the operand stack abstractly. Stack entries are materialised into
//! registers `s0..sn` at block boundaries, which is what turns the stack machine
//! into something an invariant generator can reason about.
//!
//! Conventions worth stating once:
//!
//! * The abstract stack holds **one entry per value**, not per slot, so `long`
//!   and `double` occupy a single entry. Internally consistent, and it makes
//!   every stack index a value index.
//! * Exceptional control flow is computed at **block granularity**: a block
//!   inherits every handler covering any instruction in it. That
//!   over-approximates where exceptions go, which is the safe direction.
//! * Anything not modelled becomes `Terminator::Diverge` rather than being
//!   silently skipped. An unsound lifter costs -32 a task; a partial one costs
//!   0, and 0 is recoverable.

use std::collections::HashMap;

use crate::classfile::{ClassFile, Code, Cp};
use log::{debug, warn};
use roast_ir::*;
use roast_models::{self as models, CallModel};

// ---------------------------------------------------------------------------
// Pass 1: decode
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Insn {
    off: usize,
    len: usize,
    op: u8,
    imm: i32,
    /// Branch targets; for switches, the default followed by each case.
    targets: Vec<usize>,
    /// Switch case keys, parallel to `targets[1..]`.
    keys: Vec<i32>,
    /// A `wide` prefix was consumed into this instruction.
    wide: bool,
}

fn i16at(c: &[u8], i: usize) -> i32 {
    i16::from_be_bytes([c[i], c[i + 1]]) as i32
}
fn i32at(c: &[u8], i: usize) -> i32 {
    i32::from_be_bytes([c[i], c[i + 1], c[i + 2], c[i + 3]])
}
fn u16at(c: &[u8], i: usize) -> i32 {
    u16::from_be_bytes([c[i], c[i + 1]]) as i32
}

fn decode(code: &[u8]) -> Result<Vec<Insn>, String> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < code.len() {
        macro_rules! need {
            ($n:expr) => {
                if i + $n > code.len() {
                    return Err(format!("truncated instruction at {i}"));
                }
            };
        }

        let mut op = code[i];
        let mut targets = Vec::new();
        let mut keys = Vec::new();
        let mut imm = 0i32;
        let mut wide = false;

        if op == 0xc4 {
            need!(2);
            wide = true;
            op = code[i + 1];
            let len = if op == 0x84 {
                need!(6);
                imm = (u16at(code, i + 2) << 16) | (i16at(code, i + 4) & 0xffff);
                6
            } else {
                need!(4);
                imm = u16at(code, i + 2);
                4
            };
            out.push(Insn {
                off: i,
                len,
                op,
                imm,
                targets,
                keys,
                wide,
            });
            i += len;
            continue;
        }

        let len = match op {
            0x10 => {
                need!(2);
                imm = code[i + 1] as i8 as i32;
                2
            }
            0x11 => {
                need!(3);
                imm = i16at(code, i + 1);
                3
            }
            0x12 => {
                need!(2);
                imm = code[i + 1] as i32;
                2
            }
            0x13 | 0x14 => {
                need!(3);
                imm = u16at(code, i + 1);
                3
            }
            0x15..=0x19 | 0x36..=0x3a | 0xa9 | 0xbc => {
                need!(2);
                imm = code[i + 1] as i32;
                2
            }
            0x84 => {
                need!(3);
                imm = ((code[i + 1] as i32) << 16) | (code[i + 2] as i8 as i32 & 0xffff);
                3
            }
            0x99..=0xa8 | 0xc6 | 0xc7 => {
                need!(3);
                targets.push((i as i32 + i16at(code, i + 1)) as usize);
                3
            }
            0xc8 | 0xc9 => {
                need!(5);
                targets.push((i as i32 + i32at(code, i + 1)) as usize);
                5
            }
            0xaa => {
                let pad = (4 - ((i + 1) % 4)) % 4;
                let base = i + 1 + pad;
                if base + 12 > code.len() {
                    return Err("truncated tableswitch".into());
                }
                let def = i32at(code, base);
                let low = i32at(code, base + 4);
                let high = i32at(code, base + 8);
                let n = (high as i64 - low as i64 + 1).max(0) as usize;
                if base + 12 + n * 4 > code.len() {
                    return Err("truncated tableswitch table".into());
                }
                targets.push((i as i32 + def) as usize);
                for k in 0..n {
                    targets.push((i as i32 + i32at(code, base + 12 + k * 4)) as usize);
                    keys.push(low.wrapping_add(k as i32));
                }
                (base + 12 + n * 4) - i
            }
            0xab => {
                let pad = (4 - ((i + 1) % 4)) % 4;
                let base = i + 1 + pad;
                if base + 8 > code.len() {
                    return Err("truncated lookupswitch".into());
                }
                let def = i32at(code, base);
                let n = i32at(code, base + 4).max(0) as usize;
                if base + 8 + n * 8 > code.len() {
                    return Err("truncated lookupswitch table".into());
                }
                targets.push((i as i32 + def) as usize);
                for k in 0..n {
                    keys.push(i32at(code, base + 8 + k * 8));
                    targets.push((i as i32 + i32at(code, base + 8 + k * 8 + 4)) as usize);
                }
                (base + 8 + n * 8) - i
            }
            0xb2..=0xb8 | 0xbb | 0xbd | 0xc0 | 0xc1 => {
                need!(3);
                imm = u16at(code, i + 1);
                3
            }
            0xb9 | 0xba => {
                need!(5);
                imm = u16at(code, i + 1);
                5
            }
            0xc5 => {
                need!(4);
                imm = u16at(code, i + 1);
                // Third operand byte is the dimension count, not part of imm.
                keys.push(code[i + 3] as i32);
                4
            }
            _ => 1,
        };

        out.push(Insn {
            off: i,
            len,
            op,
            imm,
            targets,
            keys,
            wide,
        });
        i += len;
    }
    Ok(out)
}

fn ends_block(op: u8) -> bool {
    matches!(op, 0x99..=0xab | 0xac..=0xb1 | 0xbf | 0xc6..=0xc9)
}

/// Instructions that can raise an exception, and so need an exceptional edge
/// when they sit inside a handler range.
fn can_throw(op: u8) -> bool {
    matches!(op,
        0x2e..=0x35 | 0x4f..=0x56
        | 0x6c | 0x6d | 0x70 | 0x71
        | 0xb2..=0xb9
        | 0xbb..=0xc3
        | 0xc5)
}

// ---------------------------------------------------------------------------
// Lifting context
// ---------------------------------------------------------------------------

struct Lifter<'a> {
    cf: &'a ClassFile,
    vars: Vec<VarInfo>,
    local_map: HashMap<u16, VarId>,
    stack_map: HashMap<u16, VarId>,
    obligations: Vec<Obligation>,
    new_classes: HashMap<VarId, String>,
    lines: Vec<(u16, u16)>,
    handlers: Vec<crate::classfile::Handler>,
}

impl<'a> Lifter<'a> {
    fn fresh(&mut self, kind: VarKind, ty: Ty) -> VarId {
        let id = VarId(self.vars.len() as u32);
        self.vars.push(VarInfo { kind, ty });
        id
    }
    fn local(&mut self, slot: u16, ty: Ty) -> VarId {
        if let Some(v) = self.local_map.get(&slot) {
            return *v;
        }
        let v = self.fresh(VarKind::Local(slot), ty);
        self.local_map.insert(slot, v);
        v
    }
    fn stack_slot(&mut self, depth: u16) -> VarId {
        if let Some(v) = self.stack_map.get(&depth) {
            return *v;
        }
        let v = self.fresh(VarKind::Stack(depth), Ty::Int);
        self.stack_map.insert(depth, v);
        v
    }
    fn temp(&mut self, ty: Ty) -> VarId {
        self.fresh(VarKind::Temp, ty)
    }

    /// Copies must carry the allocated class with them. Without this the spill
    /// at a block boundary detaches an `AssertionError` from its `athrow`, and
    /// the assertion obligation is silently never emitted -- a lost FALSE
    /// rather than a wrong answer, but lost every single time.
    fn copy_class(&mut self, dst: VarId, src: &Operand) {
        if let Operand::Var(v) = src {
            if let Some(c) = self.new_classes.get(v).cloned() {
                self.new_classes.insert(dst, c);
            }
        }
    }

    fn line_at(&self, off: u16) -> Option<u16> {
        self.lines
            .iter()
            .rev()
            .find(|(pc, _)| *pc <= off)
            .map(|(_, l)| *l)
    }

    /// Could an exception raised here be caught inside this method?
    fn guarded_at(&self, off: u16) -> bool {
        self.handlers.iter().any(|h| off >= h.start && off < h.end)
    }

    fn obligation(&mut self, kind: ObligationKind, cond: Operand, off: u16) -> ObligationId {
        let id = ObligationId(self.obligations.len() as u32);
        let line = self.line_at(off);
        let guarded = self.guarded_at(off);
        self.obligations.push(Obligation {
            id,
            kind,
            cond,
            bytecode_offset: off,
            line,
            guarded,
        });
        id
    }
}

/// Number of *values* a descriptor takes, and its return type.
fn parse_desc(desc: &str) -> (usize, Option<Ty>) {
    let b = desc.as_bytes();
    let mut i = 1usize;
    let mut n = 0usize;
    while i < b.len() && b[i] != b')' {
        while i < b.len() && b[i] == b'[' {
            i += 1;
        }
        if i < b.len() && b[i] == b'L' {
            while i < b.len() && b[i] != b';' {
                i += 1;
            }
        }
        i += 1;
        n += 1;
    }
    i += 1;
    let ret = match b.get(i) {
        Some(b'V') | None => None,
        Some(b'J') => Some(Ty::Long),
        Some(b'F') => Some(Ty::Float),
        Some(b'D') => Some(Ty::Double),
        Some(b'L') | Some(b'[') => Some(Ty::Ref),
        _ => Some(Ty::Int),
    };
    (n, ret)
}

fn ty_of_field_desc(desc: &str) -> Ty {
    match desc.as_bytes().first() {
        Some(b'J') => Ty::Long,
        Some(b'F') => Ty::Float,
        Some(b'D') => Ty::Double,
        Some(b'L') | Some(b'[') => Ty::Ref,
        _ => Ty::Int,
    }
}

/// Is this operand a category-2 (long/double) value? Needed by `dup2`, whose
/// behaviour depends on the width of what's already on the stack.
fn is_wide_operand(op: &Operand, lf: &Lifter) -> bool {
    match op {
        Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => true,
        Operand::Var(v) => lf.vars[v.0 as usize].ty.is_wide(),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Pass 2/3: leaders and lifting
// ---------------------------------------------------------------------------

pub fn lift_method(cf: &ClassFile, name: &str, desc: &str) -> Result<Body, String> {
    let m = cf
        .method(name, desc)
        .ok_or_else(|| format!("no method {name}{desc}"))?;
    let code: &Code = m
        .code
        .as_ref()
        .ok_or_else(|| format!("{name}{desc} has no Code attribute"))?;

    let key = MethodKey {
        class: cf.this_class.clone(),
        name: name.to_string(),
        desc: desc.to_string(),
    };

    let mut lf = Lifter {
        cf,
        vars: Vec::new(),
        local_map: HashMap::new(),
        stack_map: HashMap::new(),
        obligations: Vec::new(),
        new_classes: HashMap::new(),
        lines: code.lines.clone(),
        handlers: code.handlers.clone(),
    };

    let insns = decode(&code.bytes)?;
    let index: HashMap<usize, usize> = insns.iter().enumerate().map(|(i, n)| (n.off, i)).collect();

    // Leaders: entry, branch targets, fallthroughs after block-ending
    // instructions, handler boundaries, and the point after any throwing
    // instruction, so exceptional edges attach to a block that ends at it.
    let mut leaders: Vec<usize> = vec![0];
    for h in &code.handlers {
        leaders.push(h.target as usize);
        leaders.push(h.start as usize);
        leaders.push(h.end as usize);
    }
    for n in &insns {
        for t in &n.targets {
            leaders.push(*t);
        }
        if (ends_block(n.op) || can_throw(n.op)) && n.off + n.len < code.bytes.len() {
            leaders.push(n.off + n.len);
        }
    }
    leaders.sort_unstable();
    leaders.dedup();
    leaders.retain(|l| index.contains_key(l));

    let block_of: HashMap<usize, BlockId> = leaders
        .iter()
        .enumerate()
        .map(|(i, off)| (*off, BlockId(i as u32)))
        .collect();

    let mut blocks: Vec<Option<Block>> = vec![None; leaders.len()];

    // Handler blocks are entered with the exception object on the stack.
    let mut work: Vec<(usize, u16)> = vec![(0usize, 0u16)];
    for h in &code.handlers {
        if let Some(b) = block_of.get(&(h.target as usize)) {
            work.push((b.0 as usize, 1));
        }
    }
    let mut seen: HashMap<usize, u16> = HashMap::new();

    while let Some((bi, entry_h)) = work.pop() {
        if bi >= leaders.len() {
            continue;
        }
        if let Some(prev) = seen.get(&bi) {
            if *prev != entry_h {
                blocks[bi] = Some(diverging_block(
                    BlockId(bi as u32),
                    leaders[bi] as u16,
                    format!("inconsistent stack height at bb{bi}: {prev} vs {entry_h}"),
                ));
            }
            continue;
        }
        seen.insert(bi, entry_h);

        let start = leaders[bi];
        let end = leaders.get(bi + 1).copied().unwrap_or(code.bytes.len());

        let mut stmts: Vec<Stmt> = Vec::new();
        let mut stack: Vec<Operand> = (0..entry_h)
            .map(|d| Operand::Var(lf.stack_slot(d)))
            .collect();
        let mut term: Option<Terminator> = None;
        let mut succs: Vec<(usize, u16)> = Vec::new();

        let mut ii = index[&start];
        while ii < insns.len() && insns[ii].off < end {
            let n = insns[ii].clone();
            match lift_insn(
                &mut lf,
                &n,
                &mut stack,
                &mut stmts,
                &block_of,
                code.bytes.len(),
            ) {
                Ok(Some((t, s))) => {
                    term = Some(t);
                    succs = s;
                    break;
                }
                Ok(None) => {}
                Err(reason) => {
                    term = Some(Terminator::Diverge(reason));
                    break;
                }
            }
            ii += 1;
        }

        let term = match term {
            Some(t) => t,
            None => match block_of.get(&end) {
                Some(b) => {
                    succs.push((b.0 as usize, stack.len() as u16));
                    Terminator::Goto(*b)
                }
                None => Terminator::Diverge("fell off end of code".into()),
            },
        };

        if !matches!(
            term,
            Terminator::Return(_)
                | Terminator::Throw(_)
                | Terminator::Halt
                | Terminator::Diverge(_)
        ) {
            spill(&mut lf, &mut stmts, &stack);
        }

        // Exceptional successors: every handler covering any instruction in
        // this block.
        let mut exceptional = Vec::new();
        for h in &lf.handlers.clone() {
            let covers = (h.start as usize) < end && start < (h.end as usize);
            if !covers {
                continue;
            }
            let Some(target) = block_of.get(&(h.target as usize)) else {
                continue;
            };
            let class = if h.catch_type == 0 {
                None
            } else {
                cf.class_name(h.catch_type).ok()
            };
            exceptional.push(ExcEdge {
                class,
                target: *target,
            });
            succs.push((target.0 as usize, 1));
        }

        blocks[bi] = Some(Block {
            id: BlockId(bi as u32),
            bytecode_offset: start as u16,
            stmts,
            term,
            exceptional,
        });

        work.extend(succs);
    }

    let blocks: Vec<Block> = blocks
        .into_iter()
        .enumerate()
        .map(|(i, b)| {
            b.unwrap_or(Block {
                id: BlockId(i as u32),
                bytecode_offset: leaders[i] as u16,
                stmts: vec![],
                // Never reached during lifting: genuinely dead code, not a gap
                // in our modelling, so `Halt` rather than `Diverge`.
                term: Terminator::Halt,
                exceptional: vec![],
            })
        })
        .collect();

    Ok(Body {
        key,
        entry: BlockId(0),
        blocks,
        vars: lf.vars,
        obligations: lf.obligations,
    })
}

fn diverging_block(id: BlockId, off: u16, reason: String) -> Block {
    Block {
        id,
        bytecode_offset: off,
        stmts: vec![],
        term: Terminator::Diverge(reason),
        exceptional: vec![],
    }
}

fn spill(lf: &mut Lifter, stmts: &mut Vec<Stmt>, stack: &[Operand]) {
    let mut temps: Vec<(u16, Operand)> = Vec::new();
    for (d, op) in stack.iter().enumerate() {
        let canonical = lf.stack_slot(d as u16);
        if let Operand::Var(v) = op {
            if *v == canonical {
                continue;
            }
        }
        let t = lf.temp(Ty::Int);
        lf.copy_class(t, op);
        stmts.push(Stmt::Assign(t, Rvalue::Use(op.clone())));
        temps.push((d as u16, Operand::Var(t)));
    }
    for (d, t) in temps {
        let canonical = lf.stack_slot(d);
        lf.copy_class(canonical, &t);
        stmts.push(Stmt::Assign(canonical, Rvalue::Use(t)));
    }
}

type LiftOut = Option<(Terminator, Vec<(usize, u16)>)>;

fn lift_insn(
    lf: &mut Lifter,
    n: &Insn,
    stack: &mut Vec<Operand>,
    stmts: &mut Vec<Stmt>,
    block_of: &HashMap<usize, BlockId>,
    code_len: usize,
) -> Result<LiftOut, String> {
    let op = n.op;
    let off = n.off as u16;

    macro_rules! pop {
        () => {
            stack.pop().ok_or_else(|| "stack underflow".to_string())?
        };
    }
    macro_rules! assign {
        ($ty:expr, $rv:expr) => {{
            let t = lf.temp($ty);
            stmts.push(Stmt::Assign(t, $rv));
            Operand::Var(t)
        }};
    }
    macro_rules! nullcheck {
        ($obj:expr) => {{
            let g = assign!(
                Ty::Int,
                Rvalue::Bin(BinOp::Ne, $obj.clone(), Operand::Const(Const::Null))
            );
            let id = lf.obligation(ObligationKind::NullDeref, g, off);
            stmts.push(Stmt::Check(id));
        }};
    }
    macro_rules! boundscheck {
        ($arr:expr, $idx:expr) => {{
            let len = assign!(Ty::Int, Rvalue::ArrayLength($arr.clone()));
            let lo = assign!(
                Ty::Int,
                Rvalue::Bin(BinOp::Ge, $idx.clone(), Operand::int(0))
            );
            let hi = assign!(Ty::Int, Rvalue::Bin(BinOp::Lt, $idx.clone(), len));
            let inb = assign!(Ty::Int, Rvalue::Bin(BinOp::And, lo, hi));
            let id = lf.obligation(ObligationKind::ArrayBounds, inb, off);
            stmts.push(Stmt::Check(id));
        }};
    }
    macro_rules! branch {
        ($cond:expr) => {{
            let then_ = *block_of.get(&n.targets[0]).ok_or("bad branch target")?;
            let next = n.off + n.len;
            if next >= code_len {
                return Err("conditional branch at end of code".into());
            }
            let else_ = *block_of
                .get(&next)
                .ok_or_else(|| format!("no block at fallthrough {next}"))?;
            let h = stack.len() as u16;
            return Ok(Some((
                Terminator::Branch {
                    cond: $cond,
                    then_,
                    else_,
                },
                vec![(then_.0 as usize, h), (else_.0 as usize, h)],
            )));
        }};
    }

    match op {
        0x00 => {}
        0x01 => stack.push(Operand::Const(Const::Null)),
        0x02..=0x08 => stack.push(Operand::int(op as i32 - 3)),
        0x09 | 0x0a => stack.push(Operand::Const(Const::Long(op as i64 - 9))),
        0x0b..=0x0d => stack.push(Operand::Const(Const::Float(op as f32 - 11.0))),
        0x0e | 0x0f => stack.push(Operand::Const(Const::Double(op as f64 - 14.0))),
        0x10 | 0x11 => stack.push(Operand::int(n.imm)),
        0x12..=0x14 => match lf.cf.constant(n.imm as u16) {
            Some(Cp::Int(v)) => stack.push(Operand::Const(Const::Int(*v))),
            Some(Cp::Long(v)) => stack.push(Operand::Const(Const::Long(*v))),
            Some(Cp::Float(v)) => stack.push(Operand::Const(Const::Float(*v))),
            Some(Cp::Double(v)) => stack.push(Operand::Const(Const::Double(*v))),
            // Strings are references we model no state for; havoc is sound.
            Some(Cp::Str(_)) => stack.push(assign!(Ty::Ref, Rvalue::Nondet(Ty::Ref))),
            Some(Cp::Class(_)) => stack.push(Operand::Const(Const::Class("<class>".into()))),
            _ => return Err(format!("unsupported ldc at {off}")),
        },

        // Loads.
        0x15..=0x19 => {
            let ty = [Ty::Int, Ty::Long, Ty::Float, Ty::Double, Ty::Ref][(op - 0x15) as usize];
            let v = lf.local(n.imm as u16, ty);
            stack.push(Operand::Var(v));
        }
        0x1a..=0x2d => {
            let (base, ty) = match op {
                0x1a..=0x1d => (0x1a, Ty::Int),
                0x1e..=0x21 => (0x1e, Ty::Long),
                0x22..=0x25 => (0x22, Ty::Float),
                0x26..=0x29 => (0x26, Ty::Double),
                _ => (0x2a, Ty::Ref),
            };
            let v = lf.local((op - base) as u16, ty);
            stack.push(Operand::Var(v));
        }

        // Array loads.
        0x2e..=0x35 => {
            let idx = pop!();
            let arr = pop!();
            nullcheck!(arr);
            boundscheck!(arr, idx);
            let ty = match op {
                0x2f => Ty::Long,
                0x30 => Ty::Float,
                0x31 => Ty::Double,
                0x32 => Ty::Ref,
                _ => Ty::Int,
            };
            stack.push(assign!(ty, Rvalue::ArrayLoad { arr, idx }));
        }

        // Stores.
        0x36..=0x3a => {
            let ty = [Ty::Int, Ty::Long, Ty::Float, Ty::Double, Ty::Ref][(op - 0x36) as usize];
            let val = pop!();
            let v = lf.local(n.imm as u16, ty);
            lf.copy_class(v, &val);
            stmts.push(Stmt::Assign(v, Rvalue::Use(val)));
        }
        0x3b..=0x4e => {
            let (base, ty) = match op {
                0x3b..=0x3e => (0x3b, Ty::Int),
                0x3f..=0x42 => (0x3f, Ty::Long),
                0x43..=0x46 => (0x43, Ty::Float),
                0x47..=0x4a => (0x47, Ty::Double),
                _ => (0x4b, Ty::Ref),
            };
            let val = pop!();
            let v = lf.local((op - base) as u16, ty);
            lf.copy_class(v, &val);
            stmts.push(Stmt::Assign(v, Rvalue::Use(val)));
        }

        // Array stores.
        0x4f..=0x56 => {
            let val = pop!();
            let idx = pop!();
            let arr = pop!();
            nullcheck!(arr);
            boundscheck!(arr, idx);
            stmts.push(Stmt::ArrayStore { arr, idx, val });
        }

        // Stack shuffling.
        0x57 | 0x58 => {
            pop!();
        }
        0x59 => {
            let t = stack.last().cloned().ok_or("dup on empty stack")?;
            stack.push(t);
        }
        0x5a => {
            let a = pop!();
            let b = pop!();
            stack.push(a.clone());
            stack.push(b);
            stack.push(a);
        }
        0x5b => {
            let a = pop!();
            let b = pop!();
            let c = pop!();
            stack.push(a.clone());
            stack.push(c);
            stack.push(b);
            stack.push(a);
        }
        // dup2 depends on the width of the top value. With one entry per
        // value in our abstract stack, a category-2 top (long/double)
        // degrades to a plain dup; a category-1 top duplicates the *pair*
        // beneath it. Getting this wrong silently mislifts every `dup2` over
        // two ints (e.g. `arr[i]++`-shaped bytecode) without diverging --
        // exactly the class of bug the "loud failure over silent wrong"
        // design is meant to catch, and this one slipped through initially.
        0x5c => {
            let top = stack.last().ok_or("dup2 on empty stack")?.clone();
            if is_wide_operand(&top, lf) {
                stack.push(top);
            } else {
                let b = pop!(); // value1 (top)
                let a = pop!(); // value2
                stack.push(a.clone());
                stack.push(b.clone());
                stack.push(a);
                stack.push(b);
            }
        }
        0x5f => {
            let a = pop!();
            let b = pop!();
            stack.push(a);
            stack.push(b);
        }

        // Add / sub / mul / neg across the four numeric types.
        0x60..=0x6b | 0x74..=0x77 => {
            let ty = arith_ty(op);
            if (0x74..=0x77).contains(&op) {
                let a = pop!();
                stack.push(assign!(ty, Rvalue::Neg(a)));
            } else {
                let b = pop!();
                let a = pop!();
                let bop = match op {
                    0x60..=0x63 => BinOp::Add,
                    0x64..=0x67 => BinOp::Sub,
                    _ => BinOp::Mul,
                };
                stack.push(assign!(ty, Rvalue::Bin(bop, a, b)));
            }
        }
        // Integral division and remainder carry the implicit obligation.
        0x6c | 0x6d | 0x70 | 0x71 => {
            let b = pop!();
            let a = pop!();
            let ty = if matches!(op, 0x6d | 0x71) {
                Ty::Long
            } else {
                Ty::Int
            };
            let zero = if ty == Ty::Long {
                Operand::Const(Const::Long(0))
            } else {
                Operand::int(0)
            };
            let guard = assign!(Ty::Int, Rvalue::Bin(BinOp::Ne, b.clone(), zero));
            let id = lf.obligation(ObligationKind::DivByZero, guard, off);
            stmts.push(Stmt::Check(id));
            let bop = if matches!(op, 0x6c | 0x6d) {
                BinOp::Div
            } else {
                BinOp::Rem
            };
            stack.push(assign!(ty, Rvalue::Bin(bop, a, b)));
        }
        // Floating division and remainder cannot throw.
        0x6e | 0x6f | 0x72 | 0x73 => {
            let b = pop!();
            let a = pop!();
            let ty = arith_ty(op);
            let bop = if matches!(op, 0x6e | 0x6f) {
                BinOp::Div
            } else {
                BinOp::Rem
            };
            stack.push(assign!(ty, Rvalue::Bin(bop, a, b)));
        }
        // Shifts and bitwise ops.
        0x78..=0x83 => {
            let b = pop!();
            let a = pop!();
            let ty = if op % 2 == 1 { Ty::Long } else { Ty::Int };
            let bop = match op {
                0x78 | 0x79 => BinOp::Shl,
                0x7a | 0x7b => BinOp::Shr,
                0x7c | 0x7d => BinOp::UShr,
                0x7e | 0x7f => BinOp::And,
                0x80 | 0x81 => BinOp::Or,
                _ => BinOp::Xor,
            };
            stack.push(assign!(ty, Rvalue::Bin(bop, a, b)));
        }
        0x84 => {
            let slot = ((n.imm >> 16) & 0xffff) as u16;
            let delta = if n.wide {
                (n.imm & 0xffff) as u16 as i16 as i32
            } else {
                (n.imm as i16) as i32
            };
            let v = lf.local(slot, Ty::Int);
            let sum = assign!(
                Ty::Int,
                Rvalue::Bin(BinOp::Add, Operand::Var(v), Operand::int(delta))
            );
            stmts.push(Stmt::Assign(v, Rvalue::Use(sum)));
        }
        // Primitive conversions.
        0x85..=0x93 => {
            let a = pop!();
            let ty = match op {
                0x85 | 0x8c | 0x8f => Ty::Long,
                0x86 | 0x89 | 0x90 => Ty::Float,
                0x87 | 0x8a | 0x8d => Ty::Double,
                _ => Ty::Int,
            };
            stack.push(assign!(ty, Rvalue::Cast(ty, a)));
        }
        // lcmp / fcmp / dcmp.
        0x94..=0x98 => {
            let b = pop!();
            let a = pop!();
            stack.push(assign!(Ty::Int, Rvalue::Cmp(a, b)));
        }

        // Branches.
        0x99..=0x9e => {
            let a = pop!();
            let bop = [
                BinOp::Eq,
                BinOp::Ne,
                BinOp::Lt,
                BinOp::Ge,
                BinOp::Gt,
                BinOp::Le,
            ][(op - 0x99) as usize];
            let cond = assign!(Ty::Int, Rvalue::Bin(bop, a, Operand::int(0)));
            spill(lf, stmts, stack);
            branch!(cond);
        }
        0x9f..=0xa4 => {
            let b = pop!();
            let a = pop!();
            let bop = [
                BinOp::Eq,
                BinOp::Ne,
                BinOp::Lt,
                BinOp::Ge,
                BinOp::Gt,
                BinOp::Le,
            ][(op - 0x9f) as usize];
            let cond = assign!(Ty::Int, Rvalue::Bin(bop, a, b));
            spill(lf, stmts, stack);
            branch!(cond);
        }
        0xa5 | 0xa6 => {
            let b = pop!();
            let a = pop!();
            let bop = if op == 0xa5 { BinOp::Eq } else { BinOp::Ne };
            let cond = assign!(Ty::Int, Rvalue::Bin(bop, a, b));
            spill(lf, stmts, stack);
            branch!(cond);
        }
        0xc6 | 0xc7 => {
            let a = pop!();
            let bop = if op == 0xc6 { BinOp::Eq } else { BinOp::Ne };
            let cond = assign!(Ty::Int, Rvalue::Bin(bop, a, Operand::Const(Const::Null)));
            spill(lf, stmts, stack);
            branch!(cond);
        }
        0xa7 | 0xc8 => {
            let t = *block_of.get(&n.targets[0]).ok_or("bad goto target")?;
            spill(lf, stmts, stack);
            return Ok(Some((
                Terminator::Goto(t),
                vec![(t.0 as usize, stack.len() as u16)],
            )));
        }
        // Switches.
        0xaa | 0xab => {
            let value = pop!();
            let default = *block_of.get(&n.targets[0]).ok_or("bad switch default")?;
            let mut cases = Vec::new();
            let h = stack.len() as u16;
            let mut succs = vec![(default.0 as usize, h)];
            for (k, t) in n.keys.iter().zip(n.targets.iter().skip(1)) {
                let b = *block_of.get(t).ok_or("bad switch case")?;
                cases.push((*k, b));
                succs.push((b.0 as usize, h));
            }
            spill(lf, stmts, stack);
            return Ok(Some((
                Terminator::Switch {
                    value,
                    cases,
                    default,
                },
                succs,
            )));
        }

        // Returns.
        0xb1 => return Ok(Some((Terminator::Return(None), vec![]))),
        0xac..=0xb0 => {
            let v = pop!();
            return Ok(Some((Terminator::Return(Some(v)), vec![])));
        }

        // Static fields.
        0xb2 => {
            let r = lf.cf.member_ref(n.imm as u16)?;
            if r.name == "$assertionsDisabled" {
                // javac guards every `assert` with this synthetic flag.
                // SV-COMP runs with -ea, so it is pinned to false deliberately.
                stack.push(Operand::int(0));
            } else {
                let ty = ty_of_field_desc(&r.desc);
                let k = FieldKey {
                    class: r.owner,
                    name: r.name,
                    desc: r.desc,
                };
                stack.push(assign!(ty, Rvalue::GetStatic(k)));
            }
        }
        0xb3 => {
            let r = lf.cf.member_ref(n.imm as u16)?;
            let v = pop!();
            stmts.push(Stmt::PutStatic(
                FieldKey {
                    class: r.owner,
                    name: r.name,
                    desc: r.desc,
                },
                v,
            ));
        }
        // Instance fields.
        0xb4 => {
            let r = lf.cf.member_ref(n.imm as u16)?;
            let obj = pop!();
            nullcheck!(obj);
            let ty = ty_of_field_desc(&r.desc);
            let field = FieldKey {
                class: r.owner,
                name: r.name,
                desc: r.desc,
            };
            stack.push(assign!(ty, Rvalue::GetField { obj, field }));
        }
        0xb5 => {
            let r = lf.cf.member_ref(n.imm as u16)?;
            let val = pop!();
            let obj = pop!();
            nullcheck!(obj);
            stmts.push(Stmt::PutField {
                obj,
                field: FieldKey {
                    class: r.owner,
                    name: r.name,
                    desc: r.desc,
                },
                val,
            });
        }

        // Calls.
        0xb6..=0xb9 => {
            let r = lf.cf.member_ref(n.imm as u16)?;
            let (argc, ret) = parse_desc(&r.desc);
            let mut args = Vec::new();
            for _ in 0..argc {
                args.push(pop!());
            }
            args.reverse();
            let receiver = if op == 0xb8 { None } else { Some(pop!()) };

            let target = MethodKey {
                class: r.owner.clone(),
                name: r.name.clone(),
                desc: r.desc.clone(),
            };

            match models::model_for(&r.owner, &r.name, &r.desc) {
                CallModel::Assume => stmts.push(Stmt::Assume(args[0].clone())),
                CallModel::NoOp => {}
                CallModel::Nondet(t) => {
                    let ty = t.unwrap_or(Ty::Int);
                    stack.push(assign!(ty, Rvalue::Nondet(ty)));
                }
                CallModel::Pure(t) => {
                    if let Some(obj) = receiver.clone() {
                        nullcheck!(obj);
                    }
                    if let Some(ty) = t {
                        stack.push(assign!(ty, Rvalue::Nondet(ty)));
                    }
                }
                CallModel::StrCall(t) => {
                    // Keep as Rvalue::Call so the concrete engine can evaluate
                    // string/StringBuilder methods against tracked values.
                    if let Some(obj) = receiver.clone() {
                        nullcheck!(obj);
                    }
                    let is_virtual = op != 0xb8 && op != 0xb7;
                    let mut all = Vec::new();
                    if let Some(o) = receiver {
                        all.push(o);
                    }
                    all.extend(args);
                    let rv = Rvalue::Call {
                        target,
                        args: all,
                        is_virtual,
                    };
                    // Use Ty::Ref for String-returning methods (Str value flows
                    // through the concrete engine's str_store, not the IR type).
                    let ret_ty = t.map(|ty| if ty == Ty::Str { Ty::Ref } else { ty });
                    match ret_ty {
                        Some(ty) => stack.push(assign!(ty, rv)),
                        None => {
                            let t = lf.temp(Ty::Int);
                            stmts.push(Stmt::Assign(t, rv));
                        }
                    }
                }
                CallModel::EnumInit => {
                    // Enum.<init>(this, name, ordinal): store ordinal to
                    // synthetic $$ordinal field so ordinal() can read it.
                    let this = receiver.unwrap_or_else(|| args.remove(0));
                    // args layout after receiver removal: [name, ordinal]
                    let ordinal = if args.len() >= 2 {
                        args[1].clone()
                    } else {
                        Operand::int(0)
                    };
                    stmts.push(Stmt::PutField {
                        obj: this,
                        field: FieldKey {
                            class: "java/lang/Enum".into(),
                            name: models::ENUM_ORDINAL_FIELD.into(),
                            desc: "I".into(),
                        },
                        val: ordinal,
                    });
                }
                CallModel::EnumOrdinal => {
                    // Enum.ordinal(): read ordinal from synthetic $$ordinal field.
                    let this = receiver.unwrap_or_else(|| args.remove(0));
                    nullcheck!(this);
                    stack.push(assign!(
                        Ty::Int,
                        Rvalue::GetField {
                            obj: this,
                            field: FieldKey {
                                class: "java/lang/Enum".into(),
                                name: models::ENUM_ORDINAL_FIELD.into(),
                                desc: "I".into(),
                            },
                        }
                    ));
                }
                CallModel::Unmodelled => {
                    if let Some(obj) = receiver.clone() {
                        nullcheck!(obj);
                    }
                    let is_virtual = op != 0xb8 && op != 0xb7;
                    let mut all = Vec::new();
                    if let Some(o) = receiver {
                        all.push(o);
                    }
                    all.extend(args);
                    let rv = Rvalue::Call {
                        target,
                        args: all,
                        is_virtual,
                    };
                    match ret {
                        Some(ty) => stack.push(assign!(ty, rv)),
                        None => {
                            let t = lf.temp(Ty::Int);
                            stmts.push(Stmt::Assign(t, rv));
                        }
                    }
                }
            }
        }
        // Lambdas and Java 9+ string concatenation. Rare in this benchmark set
        // (4 of 176 tasks), so it stays a divergence for now.
        0xba => return Err("invokedynamic not modelled".into()),

        // Allocation.
        0xbb => {
            let cls = lf.cf.class_name(n.imm as u16)?;
            let t = lf.temp(Ty::Ref);
            stmts.push(Stmt::Assign(t, Rvalue::New(cls.clone())));
            lf.new_classes.insert(t, cls);
            stack.push(Operand::Var(t));
        }
        0xbc | 0xbd => {
            let len = pop!();
            let nonneg = assign!(
                Ty::Int,
                Rvalue::Bin(BinOp::Ge, len.clone(), Operand::int(0))
            );
            let id = lf.obligation(ObligationKind::NegArraySize, nonneg, off);
            stmts.push(Stmt::Check(id));
            let elem = if op == 0xbd {
                lf.cf
                    .class_name(n.imm as u16)
                    .unwrap_or_else(|_| "?".into())
            } else {
                primitive_array_elem(n.imm).to_string()
            };
            stack.push(assign!(Ty::Ref, Rvalue::NewArray { elem, len }));
        }
        0xc5 => {
            let dims = n.keys.first().copied().unwrap_or(1).max(1);
            for _ in 0..dims {
                let len = pop!();
                let nonneg = assign!(Ty::Int, Rvalue::Bin(BinOp::Ge, len, Operand::int(0)));
                let id = lf.obligation(ObligationKind::NegArraySize, nonneg, off);
                stmts.push(Stmt::Check(id));
            }
            stack.push(assign!(Ty::Ref, Rvalue::Nondet(Ty::Ref)));
        }
        0xbe => {
            let arr = pop!();
            nullcheck!(arr);
            stack.push(assign!(Ty::Int, Rvalue::ArrayLength(arr)));
        }
        0xc0 => {
            let obj = pop!();
            let class = lf.cf.class_name(n.imm as u16)?;
            let isinst = assign!(
                Ty::Int,
                Rvalue::InstanceOf {
                    obj: obj.clone(),
                    class
                }
            );
            let isnull = assign!(
                Ty::Int,
                Rvalue::Bin(BinOp::Eq, obj.clone(), Operand::Const(Const::Null))
            );
            // A cast of null always succeeds.
            let ok = assign!(Ty::Int, Rvalue::Bin(BinOp::Or, isnull, isinst));
            let id = lf.obligation(ObligationKind::ClassCast, ok, off);
            stmts.push(Stmt::Check(id));
            stack.push(obj);
        }
        0xc1 => {
            let obj = pop!();
            let class = lf.cf.class_name(n.imm as u16)?;
            stack.push(assign!(Ty::Int, Rvalue::InstanceOf { obj, class }));
        }
        // Single-threaded benchmark set: monitors are no-ops beyond the check.
        0xc2 | 0xc3 => {
            let obj = pop!();
            nullcheck!(obj);
        }

        0xbf => {
            let v = pop!();
            let thrown = match &v {
                Operand::Var(id) => lf.new_classes.get(id).cloned(),
                _ => None,
            };
            if thrown.as_deref() == Some(models::ASSERTION_ERROR) {
                // The assert property is exactly "is an AssertionError throw
                // reachable". A safety condition of `false` says: violated if
                // control ever gets here.
                let id = lf.obligation(ObligationKind::Assertion, Operand::int(0), off);
                stmts.push(Stmt::Check(id));
            }
            return Ok(Some((Terminator::Throw(v), vec![])));
        }

        other => return Err(format!("unsupported opcode 0x{other:02x} at {off}")),
    }

    Ok(None)
}

/// Numeric opcodes are laid out int/long/float/double in blocks of four.
fn arith_ty(op: u8) -> Ty {
    match op % 4 {
        0 => Ty::Int,
        1 => Ty::Long,
        2 => Ty::Float,
        _ => Ty::Double,
    }
}

fn primitive_array_elem(atype: i32) -> &'static str {
    match atype {
        4 => "boolean",
        5 => "char",
        6 => "float",
        7 => "double",
        8 => "byte",
        9 => "short",
        10 => "int",
        11 => "long",
        _ => "?",
    }
}

/// Lift every method in a class into the program.
pub fn lift_class(cf: &ClassFile, prog: &mut Program) {
    debug!("lift: processing class {}", cf.this_class);
    if let Some(sup) = &cf.super_class {
        prog.supers.insert(cf.this_class.clone(), sup.clone());
    }
    prog.interfaces
        .insert(cf.this_class.clone(), cf.interfaces.clone());

    for m in &cf.methods {
        if m.code.is_none() {
            continue;
        }
        let key = MethodKey {
            class: cf.this_class.clone(),
            name: m.name.clone(),
            desc: m.desc.clone(),
        };
        match lift_method(cf, &m.name, &m.desc) {
            Ok(body) => {
                debug!("lift: lifted {}.{}{}", cf.this_class, m.name, m.desc);
                prog.bodies.insert(body.key.clone(), body);
            }
            Err(e) => {
                // Record the failure as a diverging body rather than dropping
                // the method: a missing body would look like an unreachable
                // callee, which is the kind of silent unsoundness this whole
                // design tries to make impossible.
                warn!(
                    "lift: could not fully lift {}.{}{}: {e}",
                    cf.this_class, m.name, m.desc
                );
                prog.bodies.insert(
                    key.clone(),
                    Body {
                        key,
                        entry: BlockId(0),
                        blocks: vec![diverging_block(BlockId(0), 0, e)],
                        vars: vec![],
                        obligations: vec![],
                    },
                );
            }
        }
    }
}
