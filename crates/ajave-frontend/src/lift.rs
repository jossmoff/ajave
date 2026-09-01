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
use ajave_ir::*;
use ajave_models::{self as models, CallModel};

/// Is `class` a known `RuntimeException` subclass (excluding `AssertionError`,
/// which is handled by the `Assertion` obligation kind)?
fn is_runtime_exception(class: &str) -> bool {
    matches!(
        class,
        "java/lang/RuntimeException"
            | "java/lang/IllegalArgumentException"
            | "java/lang/IllegalStateException"
            | "java/lang/UnsupportedOperationException"
            | "java/lang/NumberFormatException"
            | "java/lang/NullPointerException"
            | "java/lang/IndexOutOfBoundsException"
            | "java/lang/ArrayIndexOutOfBoundsException"
            | "java/lang/StringIndexOutOfBoundsException"
            | "java/lang/ArithmeticException"
            | "java/lang/ClassCastException"
            | "java/lang/NegativeArraySizeException"
            | "java/lang/SecurityException"
            | "java/lang/ConcurrentModificationException"
            | "java/util/NoSuchElementException"
            | "java/lang/ClassNotFoundException"
            | "java/util/ConcurrentModificationException"
            | "java/lang/ArrayStoreException"
            | "java/util/EmptyStackException"
            | "java/lang/StackOverflowError"
    )
}

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
    /// Lambdas seen while lifting this method: (synthetic class, SAM name,
    /// implementation, capture count). Bodies for them are synthesised after
    /// the method is lifted, since they are new methods rather than statements.
    pending_lambdas: Vec<(String, String, crate::classfile::MemberRef, usize)>,
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

    /// Could a *runtime* exception raised here be caught inside this method?
    ///
    /// Only handlers that can actually catch `RuntimeException` (or a
    /// supertype like `Exception`/`Throwable`) count.  A handler for a
    /// checked exception (e.g. `IOException`) does *not* catch NPE/AIOOBE/etc.
    fn guarded_at(&self, off: u16) -> bool {
        self.handlers.iter().any(|h| {
            if off < h.start || off >= h.end {
                return false;
            }
            if h.catch_type == 0 {
                return true; // catch-all / finally
            }
            let Ok(name) = self.cf.class_name(h.catch_type) else {
                return false; // unresolvable → assume checked
            };
            matches!(
                name.as_str(),
                "java/lang/Throwable"
                    | "java/lang/Exception"
                    | "java/lang/RuntimeException"
            )
        })
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
fn is_wide_operand(op: &Operand, lifter: &Lifter) -> bool {
    match op {
        Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => true,
        Operand::Var(v) => lifter.vars[v.0 as usize].ty.is_wide(),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Pass 2/3: leaders and lifting
// ---------------------------------------------------------------------------

/// Whether to emit obligations for library-call preconditions.
///
/// These obligations are all runtime-exception kinds (NullDeref, ArrayBounds,
/// DivByZero, ExplicitThrow), so `--property assert` seeds none of them — but
/// the lifter still emits the statements that compute them: a materialised
/// `length()` call, its comparisons, and the `Check` itself, for every indexed
/// or null-sensitive library call in the program.
///
/// That is pure overhead for valid-assert, and it is not small. Enabling this
/// unconditionally cost 30 additional timeouts on a full valid-assert run,
/// concentrated exactly where you would expect: `autostub` (+11), which is
/// nothing but JDK calls, and `alarm` (+9), whose methods are enormous.
///
/// A static switch rather than a parameter because it is set once per process,
/// before any lifting, and threading it through `lift_class` -> `lift_method`
/// -> `Lifter` -> `BlockLifter` would touch every call site to express a
/// single global fact.
pub use ajave_models::SEED_CALL_PRECONDITIONS;

/// A lambda seen while lifting: the synthetic class standing in for it, the
/// functional-interface method name, the implementation, and how many values
/// it captured.
pub type PendingLambda = (String, String, crate::classfile::MemberRef, usize);

pub fn lift_method(cf: &ClassFile, name: &str, desc: &str) -> Result<Body, String> {
    lift_method_with_lambdas(cf, name, desc).map(|(b, _)| b)
}

pub fn lift_method_with_lambdas(
    cf: &ClassFile,
    name: &str,
    desc: &str,
) -> Result<(Body, Vec<PendingLambda>), String> {
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

    let mut lifter = Lifter {
        cf,
        vars: Vec::new(),
        local_map: HashMap::new(),
        stack_map: HashMap::new(),
        obligations: Vec::new(),
        new_classes: HashMap::new(),
        pending_lambdas: Vec::new(),
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
            .map(|d| Operand::Var(lifter.stack_slot(d)))
            .collect();
        let mut term: Option<Terminator> = None;
        let mut succs: Vec<(usize, u16)> = Vec::new();

        let mut ii = index[&start];
        while ii < insns.len() && insns[ii].off < end {
            let n = insns[ii].clone();
            let mut context = InsnContext {
                lifter: &mut lifter,
                stack: &mut stack,
                stmts: &mut stmts,
                block_of: &block_of,
                insn: &n,
                code_len: code.bytes.len(),
            };
            match context.lift() {
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
            spill(&mut lifter, &mut stmts, &stack);
        }

        // Exceptional successors: every handler covering any instruction in
        // this block.
        let mut exceptional = Vec::new();
        for h in &lifter.handlers.clone() {
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

    let lambdas = std::mem::take(&mut lifter.pending_lambdas);
    let mut body = Body {
        key,
        entry: BlockId(0),
        blocks,
        vars: lifter.vars,
        obligations: lifter.obligations,
    };

    // `synchronized` on a method is the ACC_SYNCHRONIZED access flag, not
    // monitorenter/monitorexit bytecode — the JVM acquires the monitor as part
    // of invocation. A lifter that only watches for the opcodes therefore sees
    // a synchronized method as completely unlocked.
    //
    // That is not merely imprecise: a concurrency explorer would interleave
    // two calls to a synchronized method freely and report a data race that
    // cannot happen, which is a wrong FALSE. (It did exactly that on
    // `SynchronizedCounter`.)
    //
    // Make the implicit lock explicit: acquire on entry, release before every
    // return. The monitor is `this` for an instance method; static
    // synchronized methods lock the class object, which we do not model, so
    // those are left alone rather than locked against the wrong thing.
    const ACC_SYNCHRONIZED: u16 = 0x0020;
    const ACC_STATIC: u16 = 0x0008;
    if m.access & ACC_SYNCHRONIZED != 0 && m.access & ACC_STATIC == 0 {
        if let Some(this) = body
            .vars
            .iter()
            .position(|vi| matches!(vi.kind, VarKind::Local(0)))
            .map(|i| Operand::Var(VarId(i as u32)))
        {
            body.blocks[0]
                .stmts
                .insert(0, Stmt::MonitorEnter(this.clone()));
            for b in body.blocks.iter_mut() {
                if matches!(b.term, Terminator::Return(_) | Terminator::Throw(_)) {
                    b.stmts.push(Stmt::MonitorExit(this.clone()));
                }
            }
        }
    }

    Ok((body, lambdas))
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

fn spill(lifter: &mut Lifter, stmts: &mut Vec<Stmt>, stack: &[Operand]) {
    let mut temps: Vec<(u16, Operand)> = Vec::new();
    for (d, op) in stack.iter().enumerate() {
        let canonical = lifter.stack_slot(d as u16);
        if let Operand::Var(v) = op {
            if *v == canonical {
                continue;
            }
        }
        let t = lifter.temp(Ty::Int);
        lifter.copy_class(t, op);
        stmts.push(Stmt::Assign(t, Rvalue::Use(op.clone())));
        temps.push((d as u16, Operand::Var(t)));
    }
    for (d, t) in temps {
        let canonical = lifter.stack_slot(d);
        lifter.copy_class(canonical, &t);
        stmts.push(Stmt::Assign(canonical, Rvalue::Use(t)));
    }
}

type LiftOut = Option<(Terminator, Vec<(usize, u16)>)>;

// ---------------------------------------------------------------------------
// Instruction lifting context — replaces the former macro-heavy `lift_insn`.
// ---------------------------------------------------------------------------

struct InsnContext<'a, 'b> {
    lifter: &'a mut Lifter<'b>,
    stack: &'a mut Vec<Operand>,
    stmts: &'a mut Vec<Stmt>,
    block_of: &'a HashMap<usize, BlockId>,
    insn: &'a Insn,
    code_len: usize,
}

impl<'a, 'b> InsnContext<'a, 'b> {
    fn pop(&mut self) -> Result<Operand, String> {
        self.stack.pop().ok_or_else(|| "stack underflow".to_string())
    }

    fn assign(&mut self, ty: Ty, rvalue: Rvalue) -> Operand {
        let temp = self.lifter.temp(ty);
        self.stmts.push(Stmt::Assign(temp, rvalue));
        Operand::Var(temp)
    }

    fn nullcheck(&mut self, obj: &Operand) {
        let guard = self.assign(
            Ty::Int,
            Rvalue::Bin(BinOp::Ne, obj.clone(), Operand::Const(Const::Null)),
        );
        let id = self.lifter.obligation(ObligationKind::NullDeref, guard, self.insn.off as u16);
        self.stmts.push(Stmt::Check(id));
    }

    fn boundscheck(&mut self, arr: &Operand, idx: &Operand) {
        let len = self.assign(Ty::Int, Rvalue::ArrayLength(arr.clone()));
        let lo = self.assign(
            Ty::Int,
            Rvalue::Bin(BinOp::Ge, idx.clone(), Operand::int(0)),
        );
        let hi = self.assign(Ty::Int, Rvalue::Bin(BinOp::Lt, idx.clone(), len));
        let in_bounds = self.assign(Ty::Int, Rvalue::Bin(BinOp::And, lo, hi));
        let id = self.lifter.obligation(ObligationKind::ArrayBounds, in_bounds, self.insn.off as u16);
        self.stmts.push(Stmt::Check(id));
    }

    /// The synthetic `$$coll_size` field key.
    fn coll_size_field() -> FieldKey {
        FieldKey {
            class: "$$coll".into(),
            name: models::COLL_SIZE_FIELD.into(),
            desc: "I".into(),
        }
    }

    /// Materialise `seq.length()` for a String or CharSequence receiver.
    ///
    /// Returns `None` for owners with no length method we model, in which case
    /// the caller seeds nothing and the precondition keeps blocking.
    fn seq_length(&mut self, owner: &str, seq: &Operand) -> Option<Operand> {
        let (class, desc) = match owner {
            "java/lang/String" => ("java/lang/String", "()I"),
            "java/lang/CharSequence" => ("java/lang/CharSequence", "()I"),
            "java/lang/StringBuilder" => ("java/lang/StringBuilder", "()I"),
            "java/lang/StringBuffer" => ("java/lang/StringBuffer", "()I"),
            // Collections carry their length in a tracked field rather than a
            // modelled call, so read it directly.
            "java/util/List" | "java/util/ArrayList" | "java/util/LinkedList"
            | "java/util/AbstractList" | "java/util/Vector" => {
                return Some(self.assign(
                    Ty::Int,
                    Rvalue::GetField { obj: seq.clone(), field: Self::coll_size_field() },
                ));
            }
            _ => return None,
        };
        let target = MethodKey {
            class: class.to_string(),
            name: "length".to_string(),
            desc: desc.to_string(),
        };
        Some(self.assign(
            Ty::Int,
            Rvalue::Call { target, args: vec![seq.clone()], is_virtual: true },
        ))
    }

    /// Emit `Check` obligations for a call's declared preconditions.
    ///
    /// Argument indices in a contract include the receiver at 0, matching
    /// `Rvalue::Call::args`. Only the kinds `Precondition::is_seeded` reports
    /// are emitted here, and that predicate is what the verdict guard trusts
    /// when it stands down — the two must stay in lockstep.
    fn seed_call_preconditions(
        &mut self,
        target: &MethodKey,
        receiver: Option<&Operand>,
        args: &[Operand],
    ) {
        if !SEED_CALL_PRECONDITIONS.load(std::sync::atomic::Ordering::Relaxed) {
            return;
        }
        let Some(contract) =
            models::contract_of(&target.class, &target.name, &target.desc)
        else {
            return;
        };
        if contract.requires.is_empty() {
            return;
        }
        let mut all: Vec<Operand> = Vec::new();
        if let Some(r) = receiver {
            all.push(r.clone());
        }
        all.extend(args.iter().cloned());

        for req in contract.requires {
            match req {
                models::Precondition::NonNull(n) => {
                    if let Some(arg) = all.get(*n as usize).cloned() {
                        self.nullcheck(&arg);
                    }
                }
                models::Precondition::NonNegative(n) => {
                    if let Some(arg) = all.get(*n as usize).cloned() {
                        let ok = self.assign(
                            Ty::Int,
                            Rvalue::Bin(BinOp::Ge, arg, Operand::Const(Const::Int(0))),
                        );
                        let id = self.lifter.obligation(
                            ObligationKind::NegArraySize, ok, self.insn.off as u16,
                        );
                        self.stmts.push(Stmt::Check(id));
                    }
                }
                models::Precondition::NonZero(n) => {
                    if let Some(arg) = all.get(*n as usize).cloned() {
                        let ok = self.assign(
                            Ty::Int,
                            Rvalue::Bin(BinOp::Ne, arg, Operand::Const(Const::Int(0))),
                        );
                        let id = self.lifter.obligation(
                            ObligationKind::DivByZero, ok, self.insn.off as u16,
                        );
                        self.stmts.push(Stmt::Check(id));
                    }
                }
                models::Precondition::IndexInRange { index, seq } => {
                    if let (Some(idx), Some(s)) = (
                        all.get(*index as usize).cloned(),
                        all.get(*seq as usize).cloned(),
                    ) {
                        // Materialise `seq.length()`. It carries a total
                        // contract, so it introduces no obligation of its own,
                        // and the BMC's string theory models it exactly —
                        // which is what makes `0 <= i < len` provable rather
                        // than merely stated.
                        if let Some(len) = self.seq_length(&target.class, &s) {
                            let lo = self.assign(
                                Ty::Int,
                                Rvalue::Bin(BinOp::Ge, idx.clone(), Operand::Const(Const::Int(0))),
                            );
                            let hi = self.assign(
                                Ty::Int,
                                Rvalue::Bin(BinOp::Lt, idx, len),
                            );
                            let ok = self.assign(
                                Ty::Int,
                                Rvalue::Bin(BinOp::And, lo, hi),
                            );
                            let id = self.lifter.obligation(
                                ObligationKind::ArrayBounds, ok, self.insn.off as u16,
                            );
                            self.stmts.push(Stmt::Check(id));
                        }
                    }
                }
                models::Precondition::RangeInBounds { start, end, seq } => {
                    if let (Some(b), Some(s)) = (
                        all.get(*start as usize).cloned(),
                        all.get(*seq as usize).cloned(),
                    ) {
                        if let Some(len) = self.seq_length(&target.class, &s) {
                            // `substring(b)` requires `0 <= b <= len`; the
                            // upper bound is inclusive, unlike an index.
                            let lo = self.assign(
                                Ty::Int,
                                Rvalue::Bin(BinOp::Ge, b.clone(), Operand::Const(Const::Int(0))),
                            );
                            let hi = self.assign(
                                Ty::Int,
                                Rvalue::Bin(BinOp::Le, b, len),
                            );
                            let ok = self.assign(Ty::Int, Rvalue::Bin(BinOp::And, lo, hi));
                            let id = self.lifter.obligation(
                                ObligationKind::ArrayBounds, ok, self.insn.off as u16,
                            );
                            self.stmts.push(Stmt::Check(id));
                            let _ = end; // the two-argument form is not seeded yet
                        }
                    }
                }
                models::Precondition::NoOverflow { a, b, op, width } => {
                    // Overflow is only observable at a wider type: at the
                    // original width the arithmetic silently wraps, which is
                    // exactly what `Math.addExact` exists to detect. Widen to
                    // long, compute there, and require the result to fit back
                    // into 32 bits. (A 64-bit `addExact` has no wider type
                    // available, so it stays unseeded and keeps blocking.)
                    if *width == 32 {
                        if let (Some(x), Some(y)) = (
                            all.get(*a as usize).cloned(),
                            all.get(*b as usize).cloned(),
                        ) {
                            let xw = self.assign(Ty::Long, Rvalue::Cast(Ty::Long, Ty::Int, x));
                            let yw = self.assign(Ty::Long, Rvalue::Cast(Ty::Long, Ty::Int, y));
                            let r = self.assign(Ty::Long, Rvalue::Bin(*op, xw, yw));
                            let lo = self.assign(
                                Ty::Int,
                                Rvalue::Bin(
                                    BinOp::Ge,
                                    r.clone(),
                                    Operand::Const(Const::Long(i32::MIN as i64)),
                                ),
                            );
                            let hi = self.assign(
                                Ty::Int,
                                Rvalue::Bin(
                                    BinOp::Le,
                                    r,
                                    Operand::Const(Const::Long(i32::MAX as i64)),
                                ),
                            );
                            let ok = self.assign(Ty::Int, Rvalue::Bin(BinOp::And, lo, hi));
                            let id = self.lifter.obligation(
                                ObligationKind::DivByZero, ok, self.insn.off as u16,
                            );
                            self.stmts.push(Stmt::Check(id));
                        }
                    }
                }
                models::Precondition::NonEmpty => {
                    // The receiver is at index 0. Emptiness is expressible now
                    // that element counts live in `$$coll_size`, so `next()` on
                    // an exhausted iterator becomes a checkable obligation
                    // rather than an unanalysable call.
                    if let Some(recv) = all.first().cloned() {
                        let n = self.assign(
                            Ty::Int,
                            Rvalue::GetField { obj: recv, field: Self::coll_size_field() },
                        );
                        let ok = self.assign(
                            Ty::Int,
                            Rvalue::Bin(BinOp::Gt, n, Operand::Const(Const::Int(0))),
                        );
                        // `ExplicitThrow` rather than `ArrayBounds`: an empty
                        // receiver raises `NoSuchElementException` or
                        // `EmptyStackException`, and replay accepts the whole
                        // RuntimeException family for that kind. Using a
                        // bounds kind here would make replay demand an index
                        // exception the JVM never throws, refuting a witness
                        // that is actually correct.
                        let id = self.lifter.obligation(
                            ObligationKind::ExplicitThrow, ok, self.insn.off as u16,
                        );
                        self.stmts.push(Stmt::Check(id));
                    }
                }
                models::Precondition::Unexpressible => {}
            }
        }
    }

    fn branch(&mut self, cond: Operand) -> Result<LiftOut, String> {
        let then_block = *self.block_of.get(&self.insn.targets[0]).ok_or("bad branch target")?;
        let next = self.insn.off + self.insn.len;
        if next >= self.code_len {
            return Err("conditional branch at end of code".into());
        }
        let else_block = *self
            .block_of
            .get(&next)
            .ok_or_else(|| format!("no block at fallthrough {next}"))?;
        let height = self.stack.len() as u16;
        Ok(Some((
            Terminator::Branch {
                cond,
                then_: then_block,
                else_: else_block,
            },
            vec![(then_block.0 as usize, height), (else_block.0 as usize, height)],
        )))
    }

    // -----------------------------------------------------------------------
    // Top-level dispatch
    // -----------------------------------------------------------------------

    fn lift(&mut self) -> Result<LiftOut, String> {
        match self.insn.op {
            0x00 => Ok(None),
            0x01..=0x14 => self.lift_const_load(),
            0x15..=0x2d => self.lift_local_load(),
            0x2e..=0x35 => self.lift_array_load(),
            0x36..=0x4e => self.lift_store(),
            0x4f..=0x56 => self.lift_array_store(),
            0x57..=0x5f => self.lift_stack_shuffle(),
            0x60..=0x98 => self.lift_arithmetic(),
            0x99..=0xab | 0xc6..=0xc8 => self.lift_branch_or_jump(),
            0xac..=0xb1 => self.lift_return(),
            0xb2..=0xb5 => self.lift_field(),
            0xb6..=0xba => self.lift_invoke(),
            0xbb..=0xc5 => self.lift_allocation(),
            other => Err(format!("unsupported opcode 0x{other:02x} at {}", self.insn.off)),
        }
    }

    // -----------------------------------------------------------------------
    // Constants and constant-pool loads (0x01..=0x14)
    // -----------------------------------------------------------------------

    fn lift_const_load(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        match op {
            0x01 => self.stack.push(Operand::Const(Const::Null)),
            0x02..=0x08 => self.stack.push(Operand::int(op as i32 - 3)),
            0x09 | 0x0a => self.stack.push(Operand::Const(Const::Long(op as i64 - 9))),
            0x0b..=0x0d => self.stack.push(Operand::Const(Const::Float(op as f32 - 11.0))),
            0x0e | 0x0f => self.stack.push(Operand::Const(Const::Double(op as f64 - 14.0))),
            0x10 | 0x11 => self.stack.push(Operand::int(self.insn.imm)),
            0x12..=0x14 => match self.lifter.cf.constant(self.insn.imm as u16) {
                Some(Cp::Int(v)) => self.stack.push(Operand::Const(Const::Int(*v))),
                Some(Cp::Long(v)) => self.stack.push(Operand::Const(Const::Long(*v))),
                Some(Cp::Float(v)) => self.stack.push(Operand::Const(Const::Float(*v))),
                Some(Cp::Double(v)) => self.stack.push(Operand::Const(Const::Double(*v))),
                Some(Cp::Str(idx)) => {
                    let s = match self.lifter.cf.cp.get(*idx as usize) {
                        Some(Cp::Utf8(s)) => s.clone(),
                        _ => String::new(),
                    };
                    self.stack.push(Operand::Const(Const::Str(s)));
                }
                Some(Cp::Class(_)) => self.stack.push(Operand::Const(Const::Class("<class>".into()))),
                _ => return Err(format!("unsupported ldc at {}", self.insn.off)),
            },
            _ => unreachable!(),
        }
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Local variable loads (0x15..=0x2d)
    // -----------------------------------------------------------------------

    fn lift_local_load(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        match op {
            0x15..=0x19 => {
                let ty = [Ty::Int, Ty::Long, Ty::Float, Ty::Double, Ty::Ref][(op - 0x15) as usize];
                let v = self.lifter.local(self.insn.imm as u16, ty);
                self.stack.push(Operand::Var(v));
            }
            0x1a..=0x2d => {
                let (base, ty) = match op {
                    0x1a..=0x1d => (0x1a, Ty::Int),
                    0x1e..=0x21 => (0x1e, Ty::Long),
                    0x22..=0x25 => (0x22, Ty::Float),
                    0x26..=0x29 => (0x26, Ty::Double),
                    _ => (0x2a, Ty::Ref),
                };
                let v = self.lifter.local((op - base) as u16, ty);
                self.stack.push(Operand::Var(v));
            }
            _ => unreachable!(),
        }
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Array loads (0x2e..=0x35)
    // -----------------------------------------------------------------------

    fn lift_array_load(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        let idx = self.pop()?;
        let arr = self.pop()?;
        self.nullcheck(&arr);
        self.boundscheck(&arr, &idx);
        let ty = match op {
            0x2f => Ty::Long,
            0x30 => Ty::Float,
            0x31 => Ty::Double,
            0x32 => Ty::Ref,
            _ => Ty::Int,
        };
        let result = self.assign(ty, Rvalue::ArrayLoad { arr, idx });
        self.stack.push(result);
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Stores (0x36..=0x4e)
    // -----------------------------------------------------------------------

    fn lift_store(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        match op {
            0x36..=0x3a => {
                let ty = [Ty::Int, Ty::Long, Ty::Float, Ty::Double, Ty::Ref][(op - 0x36) as usize];
                let val = self.pop()?;
                let v = self.lifter.local(self.insn.imm as u16, ty);
                self.lifter.copy_class(v, &val);
                self.stmts.push(Stmt::Assign(v, Rvalue::Use(val)));
            }
            0x3b..=0x4e => {
                let (base, ty) = match op {
                    0x3b..=0x3e => (0x3b, Ty::Int),
                    0x3f..=0x42 => (0x3f, Ty::Long),
                    0x43..=0x46 => (0x43, Ty::Float),
                    0x47..=0x4a => (0x47, Ty::Double),
                    _ => (0x4b, Ty::Ref),
                };
                let val = self.pop()?;
                let v = self.lifter.local((op - base) as u16, ty);
                self.lifter.copy_class(v, &val);
                self.stmts.push(Stmt::Assign(v, Rvalue::Use(val)));
            }
            _ => unreachable!(),
        }
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Array stores (0x4f..=0x56)
    // -----------------------------------------------------------------------

    fn lift_array_store(&mut self) -> Result<LiftOut, String> {
        let val = self.pop()?;
        let idx = self.pop()?;
        let arr = self.pop()?;
        self.nullcheck(&arr);
        self.boundscheck(&arr, &idx);
        self.stmts.push(Stmt::ArrayStore { arr, idx, val });
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Stack shuffling (0x57..=0x5f)
    // -----------------------------------------------------------------------

    fn lift_stack_shuffle(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        match op {
            0x57 | 0x58 => {
                self.pop()?;
            }
            0x59 => {
                let t = self.stack.last().cloned().ok_or("dup on empty stack")?;
                self.stack.push(t);
            }
            0x5a => {
                let a = self.pop()?;
                let b = self.pop()?;
                self.stack.push(a.clone());
                self.stack.push(b);
                self.stack.push(a);
            }
            0x5b => {
                let a = self.pop()?;
                let b = self.pop()?;
                let c = self.pop()?;
                self.stack.push(a.clone());
                self.stack.push(c);
                self.stack.push(b);
                self.stack.push(a);
            }
            // dup2 depends on the width of the top value. With one entry per
            // value in our abstract stack, a category-2 top (long/double)
            // degrades to a plain dup; a category-1 top duplicates the *pair*
            // beneath it. Getting this wrong silently mislifts every `dup2` over
            // two ints (e.g. `arr[i]++`-shaped bytecode) without diverging --
            // exactly the class of bug the "loud failure over silent wrong"
            // design is meant to catch, and this one slipped through initially.
            0x5c => {
                let top = self.stack.last().ok_or("dup2 on empty stack")?.clone();
                if is_wide_operand(&top, self.lifter) {
                    self.stack.push(top);
                } else {
                    let b = self.pop()?; // value1 (top)
                    let a = self.pop()?; // value2
                    self.stack.push(a.clone());
                    self.stack.push(b.clone());
                    self.stack.push(a);
                    self.stack.push(b);
                }
            }
            0x5f => {
                let a = self.pop()?;
                let b = self.pop()?;
                self.stack.push(a);
                self.stack.push(b);
            }
            _ => return Err(format!("unsupported stack op 0x{op:02x}")),
        }
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Arithmetic, conversions, comparisons (0x60..=0x98)
    // -----------------------------------------------------------------------

    fn lift_arithmetic(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        let off = self.insn.off as u16;
        match op {
            // Add / sub / mul / neg across the four numeric types.
            0x60..=0x6b | 0x74..=0x77 => {
                let ty = arith_ty(op);
                if (0x74..=0x77).contains(&op) {
                    let a = self.pop()?;
                    let result = self.assign(ty, Rvalue::Neg(a));
                    self.stack.push(result);
                } else {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let binop = match op {
                        0x60..=0x63 => BinOp::Add,
                        0x64..=0x67 => BinOp::Sub,
                        _ => BinOp::Mul,
                    };
                    let result = self.assign(ty, Rvalue::Bin(binop, a, b));
                    self.stack.push(result);
                }
            }
            // Integral division and remainder carry the implicit obligation.
            0x6c | 0x6d | 0x70 | 0x71 => {
                let b = self.pop()?;
                let a = self.pop()?;
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
                let guard = self.assign(Ty::Int, Rvalue::Bin(BinOp::Ne, b.clone(), zero));
                let id = self.lifter.obligation(ObligationKind::DivByZero, guard, off);
                self.stmts.push(Stmt::Check(id));
                let binop = if matches!(op, 0x6c | 0x6d) {
                    BinOp::Div
                } else {
                    BinOp::Rem
                };
                let result = self.assign(ty, Rvalue::Bin(binop, a, b));
                self.stack.push(result);
            }
            // Floating division and remainder cannot throw.
            0x6e | 0x6f | 0x72 | 0x73 => {
                let b = self.pop()?;
                let a = self.pop()?;
                let ty = arith_ty(op);
                let binop = if matches!(op, 0x6e | 0x6f) {
                    BinOp::Div
                } else {
                    BinOp::Rem
                };
                let result = self.assign(ty, Rvalue::Bin(binop, a, b));
                self.stack.push(result);
            }
            // Shifts and bitwise ops.
            0x78..=0x83 => {
                let b = self.pop()?;
                let a = self.pop()?;
                let ty = if op % 2 == 1 { Ty::Long } else { Ty::Int };
                let binop = match op {
                    0x78 | 0x79 => BinOp::Shl,
                    0x7a | 0x7b => BinOp::Shr,
                    0x7c | 0x7d => BinOp::UShr,
                    0x7e | 0x7f => BinOp::And,
                    0x80 | 0x81 => BinOp::Or,
                    _ => BinOp::Xor,
                };
                let result = self.assign(ty, Rvalue::Bin(binop, a, b));
                self.stack.push(result);
            }
            // iinc
            0x84 => {
                let slot = ((self.insn.imm >> 16) & 0xffff) as u16;
                let delta = if self.insn.wide {
                    (self.insn.imm & 0xffff) as u16 as i16 as i32
                } else {
                    (self.insn.imm as i16) as i32
                };
                let v = self.lifter.local(slot, Ty::Int);
                let sum = self.assign(
                    Ty::Int,
                    Rvalue::Bin(BinOp::Add, Operand::Var(v), Operand::int(delta)),
                );
                self.stmts.push(Stmt::Assign(v, Rvalue::Use(sum)));
            }
            // Primitive conversions.
            0x85..=0x93 => {
                let a = self.pop()?;
                match op {
                    // i2b: sign-extend byte — (x << 24) >> 24
                    0x91 => {
                        let shifted = self.assign(
                            Ty::Int,
                            Rvalue::Bin(BinOp::Shl, a.clone(), Operand::int(24)),
                        );
                        let result = self.assign(
                            Ty::Int,
                            Rvalue::Bin(BinOp::Shr, shifted, Operand::int(24)),
                        );
                        self.stack.push(result);
                    }
                    // i2c: zero-extend char — x & 0xFFFF
                    0x92 => {
                        let result = self.assign(
                            Ty::Int,
                            Rvalue::Bin(BinOp::And, a, Operand::int(0xFFFF)),
                        );
                        self.stack.push(result);
                    }
                    // i2s: sign-extend short — (x << 16) >> 16
                    0x93 => {
                        let shifted = self.assign(
                            Ty::Int,
                            Rvalue::Bin(BinOp::Shl, a.clone(), Operand::int(16)),
                        );
                        let result = self.assign(
                            Ty::Int,
                            Rvalue::Bin(BinOp::Shr, shifted, Operand::int(16)),
                        );
                        self.stack.push(result);
                    }
                    // Other conversions: i2l, l2i, i2f, i2d, l2f, l2d, f2i, f2l, f2d, d2i, d2l, d2f
                    _ => {
                        let (dst, src) = match op {
                            0x85 => (Ty::Long, Ty::Int),    // i2l
                            0x86 => (Ty::Float, Ty::Int),   // i2f
                            0x87 => (Ty::Double, Ty::Int),  // i2d
                            0x88 => (Ty::Int, Ty::Long),    // l2i
                            0x89 => (Ty::Float, Ty::Long),  // l2f
                            0x8a => (Ty::Double, Ty::Long),  // l2d
                            0x8b => (Ty::Int, Ty::Float),   // f2i
                            0x8c => (Ty::Long, Ty::Float),  // f2l
                            0x8d => (Ty::Double, Ty::Float), // f2d
                            0x8e => (Ty::Int, Ty::Double),  // d2i
                            0x8f => (Ty::Long, Ty::Double), // d2l
                            0x90 => (Ty::Float, Ty::Double), // d2f
                            _ => (Ty::Int, Ty::Int),
                        };
                        let result = self.assign(dst, Rvalue::Cast(dst, src, a));
                        self.stack.push(result);
                    }
                }
            }
            // lcmp / fcmpl / fcmpg / dcmpl / dcmpg.
            0x94..=0x98 => {
                let b = self.pop()?;
                let a = self.pop()?;
                let kind = match op {
                    0x94 => CmpKind::Long,
                    0x95 | 0x97 => CmpKind::FloatL,
                    0x96 | 0x98 => CmpKind::FloatG,
                    _ => unreachable!(),
                };
                let result = self.assign(Ty::Int, Rvalue::Cmp(kind, a, b));
                self.stack.push(result);
            }
            _ => unreachable!(),
        }
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Branches, gotos, switches (0x99..=0xab, 0xc6..=0xc8)
    // -----------------------------------------------------------------------

    fn lift_branch_or_jump(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        match op {
            0x99..=0x9e => {
                let a = self.pop()?;
                let binop = [
                    BinOp::Eq,
                    BinOp::Ne,
                    BinOp::Lt,
                    BinOp::Ge,
                    BinOp::Gt,
                    BinOp::Le,
                ][(op - 0x99) as usize];
                let cond = self.assign(Ty::Int, Rvalue::Bin(binop, a, Operand::int(0)));
                spill(self.lifter, self.stmts, self.stack);
                self.branch(cond)
            }
            0x9f..=0xa4 => {
                let b = self.pop()?;
                let a = self.pop()?;
                let binop = [
                    BinOp::Eq,
                    BinOp::Ne,
                    BinOp::Lt,
                    BinOp::Ge,
                    BinOp::Gt,
                    BinOp::Le,
                ][(op - 0x9f) as usize];
                let cond = self.assign(Ty::Int, Rvalue::Bin(binop, a, b));
                spill(self.lifter, self.stmts, self.stack);
                self.branch(cond)
            }
            0xa5 | 0xa6 => {
                let b = self.pop()?;
                let a = self.pop()?;
                let binop = if op == 0xa5 { BinOp::Eq } else { BinOp::Ne };
                let cond = self.assign(Ty::Int, Rvalue::Bin(binop, a, b));
                spill(self.lifter, self.stmts, self.stack);
                self.branch(cond)
            }
            0xc6 | 0xc7 => {
                let a = self.pop()?;
                let binop = if op == 0xc6 { BinOp::Eq } else { BinOp::Ne };
                let cond = self.assign(Ty::Int, Rvalue::Bin(binop, a, Operand::Const(Const::Null)));
                spill(self.lifter, self.stmts, self.stack);
                self.branch(cond)
            }
            0xa7 | 0xc8 => {
                let target = *self.block_of.get(&self.insn.targets[0]).ok_or("bad goto target")?;
                spill(self.lifter, self.stmts, self.stack);
                Ok(Some((
                    Terminator::Goto(target),
                    vec![(target.0 as usize, self.stack.len() as u16)],
                )))
            }
            // Switches.
            0xaa | 0xab => {
                let value = self.pop()?;
                let default = *self.block_of.get(&self.insn.targets[0]).ok_or("bad switch default")?;
                let mut cases = Vec::new();
                let height = self.stack.len() as u16;
                let mut succs = vec![(default.0 as usize, height)];
                for (k, t) in self.insn.keys.iter().zip(self.insn.targets.iter().skip(1)) {
                    let b = *self.block_of.get(t).ok_or("bad switch case")?;
                    cases.push((*k, b));
                    succs.push((b.0 as usize, height));
                }
                spill(self.lifter, self.stmts, self.stack);
                Ok(Some((
                    Terminator::Switch {
                        value,
                        cases,
                        default,
                    },
                    succs,
                )))
            }
            _ => unreachable!(),
        }
    }

    // -----------------------------------------------------------------------
    // Returns (0xac..=0xb1)
    // -----------------------------------------------------------------------

    fn lift_return(&mut self) -> Result<LiftOut, String> {
        if self.insn.op == 0xb1 {
            Ok(Some((Terminator::Return(None), vec![])))
        } else {
            let v = self.pop()?;
            Ok(Some((Terminator::Return(Some(v)), vec![])))
        }
    }

    // -----------------------------------------------------------------------
    // Static and instance fields (0xb2..=0xb5)
    // -----------------------------------------------------------------------

    fn lift_field(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        match op {
            // getstatic
            0xb2 => {
                let r = self.lifter.cf.member_ref(self.insn.imm as u16)?;
                if r.name == "$assertionsDisabled" {
                    // javac guards every `assert` with this synthetic flag.
                    // SV-COMP runs with -ea, so it is pinned to false deliberately.
                    self.stack.push(Operand::int(0));
                } else {
                    let ty = ty_of_field_desc(&r.desc);
                    let key = FieldKey {
                        class: r.owner,
                        name: r.name,
                        desc: r.desc,
                    };
                    let result = self.assign(ty, Rvalue::GetStatic(key));
                    self.stack.push(result);
                }
            }
            // putstatic
            0xb3 => {
                let r = self.lifter.cf.member_ref(self.insn.imm as u16)?;
                let v = self.pop()?;
                self.stmts.push(Stmt::PutStatic(
                    FieldKey {
                        class: r.owner,
                        name: r.name,
                        desc: r.desc,
                    },
                    v,
                ));
            }
            // getfield
            0xb4 => {
                let r = self.lifter.cf.member_ref(self.insn.imm as u16)?;
                let obj = self.pop()?;
                self.nullcheck(&obj);
                let ty = ty_of_field_desc(&r.desc);
                let field = FieldKey {
                    class: r.owner,
                    name: r.name,
                    desc: r.desc,
                };
                let result = self.assign(ty, Rvalue::GetField { obj, field });
                self.stack.push(result);
            }
            // putfield
            0xb5 => {
                let r = self.lifter.cf.member_ref(self.insn.imm as u16)?;
                let val = self.pop()?;
                let obj = self.pop()?;
                self.nullcheck(&obj);
                self.stmts.push(Stmt::PutField {
                    obj,
                    field: FieldKey {
                        class: r.owner,
                        name: r.name,
                        desc: r.desc,
                    },
                    val,
                });
            }
            _ => unreachable!(),
        }
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Method invocations (0xb6..=0xba)
    // -----------------------------------------------------------------------

    fn lift_invoke(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;

        // invokedynamic is handled separately.
        if op == 0xba {
            return self.lift_invokedynamic();
        }

        let r = self.lifter.cf.member_ref(self.insn.imm as u16)?;
        let (argc, ret) = parse_desc(&r.desc);
        let mut args = Vec::new();
        for _ in 0..argc {
            args.push(self.pop()?);
        }
        args.reverse();
        let receiver = if op == 0xb8 { None } else { Some(self.pop()?) };

        let target = MethodKey {
            class: r.owner.clone(),
            name: r.name.clone(),
            desc: r.desc.clone(),
        };

        // Seed the call's stated preconditions before dispatching on how the
        // call itself is modelled. This has to happen for *every* path, not
        // just the unmodelled one: `new StringBuilder(-1)` throws, but
        // StringBuilder is a string-owner class and so takes the `StrCall`
        // path, which would otherwise skip the check entirely.
        //
        // A library method that throws only under a nameable condition is not
        // a dead end — seeding that condition lets the analysis prove the call
        // safe instead of forcing the program to UNKNOWN. Conditions we cannot
        // state are deliberately not seeded; those keep blocking, which is the
        // honest answer.
        self.seed_call_preconditions(&target, receiver.as_ref(), &args);

        match models::model_for(&r.owner, &r.name, &r.desc) {
            CallModel::Assume => self.stmts.push(Stmt::Assume(args[0].clone())),
            CallModel::NoOp => {}
            CallModel::Nondet(t, jvm_byte) => {
                let ty = t.unwrap_or(Ty::Int);
                let result = self.assign(ty, Rvalue::Nondet(ty, Some(jvm_byte)));
                self.stack.push(result);
            }
            CallModel::Pure(t) => {
                if let Some(obj) = receiver.clone() {
                    self.nullcheck(&obj);
                }
                if let Some(ty) = t {
                    let result = self.assign(ty, Rvalue::Havoc(ty));
                    self.stack.push(result);
                }
            }
            CallModel::MathCall(t) => {
                // Keep as Rvalue::Call so the SMT engine can model
                // Math/Integer/Long methods precisely.
                let is_virtual = op != 0xb8 && op != 0xb7;
                let mut all = Vec::new();
                if let Some(o) = receiver {
                    all.push(o);
                }
                all.extend(args);
                let rvalue = Rvalue::Call {
                    target,
                    args: all,
                    is_virtual,
                };
                match t {
                    Some(ty) => {
                        let result = self.assign(ty, rvalue);
                        self.stack.push(result);
                    }
                    None => {
                        let tmp = self.lifter.temp(Ty::Int);
                        self.stmts.push(Stmt::Assign(tmp, rvalue));
                    }
                }
            }
            CallModel::StrCall(t) => {
                // Keep as Rvalue::Call so the concrete engine can evaluate
                // string/StringBuilder methods against tracked values.
                if let Some(obj) = receiver.clone() {
                    self.nullcheck(&obj);
                }
                let is_virtual = op != 0xb8 && op != 0xb7;
                let mut all = Vec::new();
                if let Some(o) = receiver {
                    all.push(o);
                }
                all.extend(args);
                let rvalue = Rvalue::Call {
                    target,
                    args: all,
                    is_virtual,
                };
                // Use Ty::Ref for String-returning methods (Str value flows
                // through the concrete engine's str_store, not the IR type).
                let ret_ty = t.map(|ty| if ty == Ty::Str { Ty::Ref } else { ty });
                match ret_ty {
                    Some(ty) => {
                        let result = self.assign(ty, rvalue);
                        self.stack.push(result);
                    }
                    None => {
                        let tmp = self.lifter.temp(Ty::Int);
                        self.stmts.push(Stmt::Assign(tmp, rvalue));
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
                self.stmts.push(Stmt::PutField {
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
                self.nullcheck(&this);
                let result = self.assign(
                    Ty::Int,
                    Rvalue::GetField {
                        obj: this,
                        field: FieldKey {
                            class: "java/lang/Enum".into(),
                            name: models::ENUM_ORDINAL_FIELD.into(),
                            desc: "I".into(),
                        },
                    },
                );
                self.stack.push(result);
            }
            CallModel::BoxStore(ty) => {
                // T.valueOf(primitive): allocate a new ref and store the
                // argument into a synthetic $$value field.
                let val = args.into_iter().next().unwrap_or(Operand::int(0));
                let obj = self.lifter.temp(Ty::Ref);
                self.stmts.push(Stmt::Assign(obj, Rvalue::New(target.class.clone())));
                self.stmts.push(Stmt::PutField {
                    obj: Operand::Var(obj),
                    field: FieldKey {
                        class: target.class.clone(),
                        name: models::BOX_VALUE_FIELD.into(),
                        desc: ty.descriptor().into(),
                    },
                    val,
                });
                self.stack.push(Operand::Var(obj));
            }
            CallModel::Unbox(ty) => {
                // T.*Value(): read the $$value field from the receiver.
                let this = receiver.unwrap_or_else(|| args.remove(0));
                self.nullcheck(&this);
                let field_val = self.assign(
                    ty,
                    Rvalue::GetField {
                        obj: this,
                        field: FieldKey {
                            class: target.class.clone(),
                            name: models::BOX_VALUE_FIELD.into(),
                            desc: ty.descriptor().into(),
                        },
                    },
                );
                // If the storage type differs from the method's return type,
                // insert an explicit cast (narrowing or widening).
                let ret_char = target.desc.as_bytes().get(target.desc.len() - 1).copied().unwrap_or(b'I');
                let ret_ty = match ret_char {
                    b'J' => Ty::Long,
                    b'D' => Ty::Double,
                    b'F' => Ty::Float,
                    _ => Ty::Int,
                };
                let result = if ty.is_wide() != ret_ty.is_wide() {
                    self.assign(ret_ty, Rvalue::Cast(ret_ty, ty, field_val))
                } else {
                    field_val
                };
                self.stack.push(result);
            }
            CallModel::StaticBinOp(binop) => {
                // Static binary method: result = arg0 op arg1.
                let a = args.get(0).cloned().unwrap_or(Operand::int(0));
                let b = args.get(1).cloned().unwrap_or(Operand::int(0));
                let result = self.assign(Ty::Int, Rvalue::Bin(binop, a, b));
                self.stack.push(result);
            }
            CallModel::AssertionsEnabled => {
                // SV-COMP: assertions always enabled → return 1.
                self.stack.push(Operand::int(1));
            }
            CallModel::CollectionStore(elem_idx) => {
                // add(elem) / put(key, elem) / set(idx, elem):
                // Store the element to synthetic $$coll_last field on receiver.
                let this = receiver.unwrap_or_else(|| args.remove(0));
                let this_for_size = this.clone();
                let name_is_growing = r.name != "set";
                let elem = args
                    .get(elem_idx as usize)
                    .cloned()
                    .unwrap_or(Operand::int(0));
                self.stmts.push(Stmt::PutField {
                    obj: this,
                    field: FieldKey {
                        class: "$$coll".into(),
                        name: models::COLL_LAST_FIELD.into(),
                        desc: "Ljava/lang/Object;".into(),
                    },
                    val: elem,
                });
                // Growing operations bump the tracked element count. `set`
                // replaces rather than appends, so it leaves the size alone.
                if name_is_growing {
                    let old = self.assign(
                        Ty::Int,
                        Rvalue::GetField { obj: this_for_size.clone(), field: Self::coll_size_field() },
                    );
                    let inc = self.assign(
                        Ty::Int,
                        Rvalue::Bin(BinOp::Add, old, Operand::Const(Const::Int(1))),
                    );
                    self.stmts.push(Stmt::PutField {
                        obj: this_for_size,
                        field: Self::coll_size_field(),
                        val: inc,
                    });
                }

                // add() returns boolean true; put()/set()/remove() return old value (null).
                if let Some(ty) = ret {
                    let result = match ty {
                        Ty::Int => Operand::int(1), // add() → true
                        _ => Operand::int(0),        // put()/set() → null
                    };
                    self.stack.push(result);
                }
            }
            CallModel::CollectionLoad(t) => {
                // get(idx) / getLast() / next() / Map.get(key):
                // Read from synthetic $$coll_last field on receiver.
                let this = receiver.unwrap_or_else(|| args.remove(0));
                self.nullcheck(&this);
                let result = self.assign(
                    t.unwrap_or(Ty::Ref),
                    Rvalue::GetField {
                        obj: this,
                        field: FieldKey {
                            class: "$$coll".into(),
                            name: models::COLL_LAST_FIELD.into(),
                            desc: "Ljava/lang/Object;".into(),
                        },
                    },
                );
                self.stack.push(result);
            }
            CallModel::CollectionIterator => {
                // iterator() / values() / keySet() / entrySet():
                // Return the collection itself so next() reads $$coll_last.
                let this = receiver.unwrap_or_else(|| args.remove(0));
                self.stack.push(this);
            }
            CallModel::CollectionSize => {
                let this = receiver.unwrap_or_else(|| args.remove(0));
                let n = self.assign(
                    Ty::Int,
                    Rvalue::GetField { obj: this, field: Self::coll_size_field() },
                );
                self.stack.push(n);
            }
            CallModel::CollectionIsEmpty => {
                let this = receiver.unwrap_or_else(|| args.remove(0));
                let n = self.assign(
                    Ty::Int,
                    Rvalue::GetField { obj: this, field: Self::coll_size_field() },
                );
                let empty = self.assign(
                    Ty::Int,
                    Rvalue::Bin(BinOp::Eq, n, Operand::Const(Const::Int(0))),
                );
                self.stack.push(empty);
            }
            CallModel::Unmodelled => {
                if let Some(obj) = receiver.clone() {
                    self.nullcheck(&obj);
                }
                let is_virtual = op != 0xb8 && op != 0xb7;
                let mut all = Vec::new();
                if let Some(o) = receiver {
                    all.push(o);
                }
                all.extend(args);
                let rvalue = Rvalue::Call {
                    target,
                    args: all,
                    is_virtual,
                };
                match ret {
                    Some(ty) => {
                        let result = self.assign(ty, rvalue);
                        self.stack.push(result);
                    }
                    None => {
                        let tmp = self.lifter.temp(Ty::Int);
                        self.stmts.push(Stmt::Assign(tmp, rvalue));
                    }
                }
            }
        }
        Ok(None)
    }

    fn lift_invokedynamic(&mut self) -> Result<LiftOut, String> {
        // invokedynamic: lambdas, method references, string concatenation.
        //
        // A lambda used to become `Havoc(Ref)`: a reference with no class. The
        // body was lifted perfectly well as `lambda$main$0`, but nothing
        // connected the object to it, so anything that resolves behaviour from
        // an object's class -- a thread body, an executor task -- found
        // nothing. `new Thread(() -> ...)` was unanalysable.
        //
        // The `LambdaMetafactory` bootstrap names its implementation method in
        // its second static argument, so instead of havocing we allocate an
        // object of a synthetic class and give that class a body for the
        // functional-interface method which forwards to the implementation.
        // Everything downstream then works unchanged.
        let (name, desc, bsm) = self.lifter.cf.invoke_dynamic(self.insn.imm as u16)?;
        let (argc, ret) = parse_desc(&desc);
        let impl_ref = self.lifter.cf.lambda_impl(bsm).filter(|m| {
            // A method reference to an *instance* method binds a receiver we
            // would have to carry as a capture with the right type; only static
            // and synthetic-lambda targets are handled here.
            m.owner == self.lifter.cf.this_class
        });

        // Captured values are the invokedynamic's operands, popped innermost
        // last, and become the leading parameters of the implementation.
        let mut captured: Vec<Operand> = Vec::new();
        for _ in 0..argc {
            captured.push(self.pop()?);
        }
        captured.reverse();

        debug!("invokedynamic: {name} {desc}");
        let Some(imp) = impl_ref else {
            // Not a lambda we can resolve (string concatenation, a bootstrap we
            // do not model). Unchanged behaviour: havoc the result.
            if let Some(ty) = ret {
                let result = self.assign(ty, Rvalue::Havoc(ty));
                self.stack.push(result);
            }
            return Ok(None);
        };

        let synth = format!("$lambda${}${}", imp.owner, imp.name);
        let t = self.lifter.temp(Ty::Ref);
        self.stmts.push(Stmt::Assign(t, Rvalue::New(synth.clone())));
        self.lifter.new_classes.insert(t, synth.clone());
        // Captured values live on the object, exactly as javac stores them on
        // the generated class.
        for (i, c) in captured.iter().enumerate() {
            self.stmts.push(Stmt::PutField {
                obj: Operand::Var(t),
                field: FieldKey {
                    class: synth.clone(),
                    name: format!("$cap{i}"),
                    desc: "I".to_string(),
                },
                val: c.clone(),
            });
        }
        self.lifter
            .pending_lambdas
            .push((synth, name, imp, captured.len()));
        self.stack.push(Operand::Var(t));
        Ok(None)
    }

    // -----------------------------------------------------------------------
    // Allocation, instanceof, checkcast, monitors, athrow (0xbb..=0xc5, 0xbf)
    // -----------------------------------------------------------------------

    fn lift_allocation(&mut self) -> Result<LiftOut, String> {
        let op = self.insn.op;
        let off = self.insn.off as u16;
        match op {
            // new
            0xbb => {
                let cls = self.lifter.cf.class_name(self.insn.imm as u16)?;
                let t = self.lifter.temp(Ty::Ref);
                self.stmts.push(Stmt::Assign(t, Rvalue::New(cls.clone())));
                self.lifter.new_classes.insert(t, cls);
                self.stack.push(Operand::Var(t));
            }
            // newarray / anewarray
            0xbc | 0xbd => {
                let len = self.pop()?;
                let nonneg = self.assign(
                    Ty::Int,
                    Rvalue::Bin(BinOp::Ge, len.clone(), Operand::int(0)),
                );
                let id = self.lifter.obligation(ObligationKind::NegArraySize, nonneg, off);
                self.stmts.push(Stmt::Check(id));
                let elem = if op == 0xbd {
                    self.lifter
                        .cf
                        .class_name(self.insn.imm as u16)
                        .unwrap_or_else(|_| "?".into())
                } else {
                    primitive_array_elem(self.insn.imm).to_string()
                };
                let result = self.assign(Ty::Ref, Rvalue::NewArray { elem, len });
                self.stack.push(result);
            }
            // multianewarray
            0xc5 => {
                let dims = self.insn.keys.first().copied().unwrap_or(1).max(1);
                for _ in 0..dims {
                    let len = self.pop()?;
                    let nonneg = self.assign(Ty::Int, Rvalue::Bin(BinOp::Ge, len, Operand::int(0)));
                    let id = self.lifter.obligation(ObligationKind::NegArraySize, nonneg, off);
                    self.stmts.push(Stmt::Check(id));
                }
                let result = self.assign(Ty::Ref, Rvalue::Nondet(Ty::Ref, None));
                self.stack.push(result);
            }
            // arraylength
            0xbe => {
                let arr = self.pop()?;
                self.nullcheck(&arr);
                let result = self.assign(Ty::Int, Rvalue::ArrayLength(arr));
                self.stack.push(result);
            }
            // athrow
            0xbf => {
                let v = self.pop()?;
                let thrown = match &v {
                    Operand::Var(id) => self.lifter.new_classes.get(id).cloned(),
                    _ => None,
                };
                if let Some(cls) = &thrown {
                    if cls == models::ASSERTION_ERROR {
                        // The assert property is exactly "is an AssertionError throw
                        // reachable". A safety condition of `false` says: violated if
                        // control ever gets here.
                        let id = self.lifter.obligation(ObligationKind::Assertion, Operand::int(0), off);
                        self.stmts.push(Stmt::Check(id));
                    } else if is_runtime_exception(cls) {
                        // NRE property: an explicit throw of a RuntimeException
                        // subclass is a violation if reachable.
                        let id = self.lifter.obligation(ObligationKind::ExplicitThrow, Operand::int(0), off);
                        self.stmts.push(Stmt::Check(id));
                    }
                }
                return Ok(Some((Terminator::Throw(v), vec![])));
            }
            // checkcast
            0xc0 => {
                let obj = self.pop()?;
                let class = self.lifter.cf.class_name(self.insn.imm as u16)?;
                let is_instance = self.assign(
                    Ty::Int,
                    Rvalue::InstanceOf {
                        obj: obj.clone(),
                        class,
                    },
                );
                let is_null = self.assign(
                    Ty::Int,
                    Rvalue::Bin(BinOp::Eq, obj.clone(), Operand::Const(Const::Null)),
                );
                // A cast of null always succeeds.
                let ok = self.assign(Ty::Int, Rvalue::Bin(BinOp::Or, is_null, is_instance));
                let id = self.lifter.obligation(ObligationKind::ClassCast, ok, off);
                self.stmts.push(Stmt::Check(id));
                self.stack.push(obj);
            }
            // instanceof
            0xc1 => {
                let obj = self.pop()?;
                let class = self.lifter.cf.class_name(self.insn.imm as u16)?;
                let result = self.assign(Ty::Int, Rvalue::InstanceOf { obj, class });
                self.stack.push(result);
            }
            // monitorenter / monitorexit.
            //
            // Observationally no-ops for a single thread, and every current
            // engine ignores them — but they are recorded rather than
            // discarded so a concurrency analysis can see that a critical
            // section exists. Reconstructing one after the fact is not
            // possible; the information is simply gone.
            0xc2 | 0xc3 => {
                let obj = self.pop()?;
                self.nullcheck(&obj);
                self.stmts.push(if op == 0xc2 {
                    Stmt::MonitorEnter(obj)
                } else {
                    Stmt::MonitorExit(obj)
                });
            }
            _ => return Err(format!("unsupported alloc opcode 0x{op:02x}")),
        }
        Ok(None)
    }
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

/// Build the functional-interface method for a lambda: load the captured
/// values off the synthetic object and call the implementation with them.
///
/// This is what makes a lambda executable. javac generates a class with the
/// captures as fields and the interface method forwarding to the
/// implementation; this is that class, built directly rather than read from a
/// classfile that does not exist.
///
/// Only `()V` interface methods are synthesised, which is `Runnable` -- enough
/// for a thread body or an executor task, and the case that mattered. A lambda
/// with parameters or a return value keeps its old opaque handling.
fn lambda_forwarder(
    synth: &str,
    sam_key: &MethodKey,
    imp: &crate::classfile::MemberRef,
    ncap: usize,
) -> Option<Body> {
    // The implementation must take exactly the captured values.
    let (impl_argc, impl_ret) = parse_desc(&imp.desc);
    if impl_argc != ncap || impl_ret.is_some() {
        return None;
    }
    let mut vars = vec![VarInfo { kind: VarKind::Local(0), ty: Ty::Ref }];
    let mut stmts = Vec::new();
    let mut args = Vec::new();
    for i in 0..ncap {
        let v = VarId(vars.len() as u32);
        vars.push(VarInfo { kind: VarKind::Temp, ty: Ty::Int });
        stmts.push(Stmt::Assign(
            v,
            Rvalue::GetField {
                obj: Operand::Var(VarId(0)),
                field: FieldKey {
                    class: synth.to_string(),
                    name: format!("$cap{i}"),
                    desc: "I".to_string(),
                },
            },
        ));
        args.push(Operand::Var(v));
    }
    let dest = VarId(vars.len() as u32);
    vars.push(VarInfo { kind: VarKind::Temp, ty: Ty::Int });
    stmts.push(Stmt::Assign(
        dest,
        Rvalue::Call {
            target: MethodKey {
                class: imp.owner.clone(),
                name: imp.name.clone(),
                desc: imp.desc.clone(),
            },
            args,
            is_virtual: false,
        },
    ));
    Some(Body {
        key: sam_key.clone(),
        entry: BlockId(0),
        blocks: vec![Block {
            id: BlockId(0),
            bytecode_offset: 0,
            stmts,
            term: Terminator::Return(None),
            exceptional: vec![],
        }],
        vars,
        obligations: vec![],
    })
}

/// Lift every method in a class into the program.
pub fn lift_class(cf: &ClassFile, prog: &mut Program) {
    debug!("lift: processing class {}", cf.this_class);
    if let Some(sup) = &cf.super_class {
        prog.supers.insert(cf.this_class.clone(), sup.clone());
    }
    prog.interfaces
        .insert(cf.this_class.clone(), cf.interfaces.clone());
    for field in &cf.fields {
        prog.declared_fields.insert((
            cf.this_class.clone(),
            field.name.clone(),
            field.desc.clone(),
        ));
        // ACC_VOLATILE (JVMS 4.5, table 4.5-A).
        if field.access & 0x0040 != 0 {
            prog.volatile_fields.insert(ajave_ir::FieldKey {
                class: cf.this_class.clone(),
                name: field.name.clone(),
                desc: field.desc.clone(),
            });
        }
    }

    for m in &cf.methods {
        if m.code.is_none() {
            continue;
        }
        let key = MethodKey {
            class: cf.this_class.clone(),
            name: m.name.clone(),
            desc: m.desc.clone(),
        };
        match lift_method_with_lambdas(cf, &m.name, &m.desc) {
            Ok((body, lambdas)) => {
                debug!("lift: lifted {}.{}{}", cf.this_class, m.name, m.desc);
                prog.bodies.insert(body.key.clone(), body);
                for (synth, sam, imp, ncap) in lambdas {
                    let sam_key = MethodKey {
                        class: synth.clone(),
                        name: sam.clone(),
                        desc: "()V".to_string(),
                    };
                    if prog.bodies.contains_key(&sam_key) {
                        continue;
                    }
                    if let Some(b) = lambda_forwarder(&synth, &sam_key, &imp, ncap) {
                        debug!("lift: synthesised {synth}.{sam} -> {}.{}", imp.owner, imp.name);
                        prog.bodies.insert(sam_key, b);
                    }
                }
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

#[cfg(test)]
mod volatile_tests {
    use super::*;
    use crate::classfile::{ClassFile, Field};

    fn cf_with(fields: Vec<Field>) -> ClassFile {
        ClassFile {
            cp: vec![],
            this_class: "C".into(),
            super_class: None,
            interfaces: vec![],
            fields,
            methods: vec![],
            bootstrap_methods: vec![],
        }
    }

    #[test]
    fn volatile_fields_are_recorded_and_plain_ones_are_not() {
        // ACC_VOLATILE is 0x0040. The flag was dropped entirely until race
        // detection needed it, so this pins that it survives lifting.
        let mut prog = Program::default();
        lift_class(
            &cf_with(vec![
                Field { name: "v".into(), desc: "I".into(), access: 0x0040 | 0x0008 },
                Field { name: "plain".into(), desc: "I".into(), access: 0x0008 },
            ]),
            &mut prog,
        );
        let vol = ajave_ir::FieldKey { class: "C".into(), name: "v".into(), desc: "I".into() };
        let plain = ajave_ir::FieldKey { class: "C".into(), name: "plain".into(), desc: "I".into() };
        assert!(prog.volatile_fields.contains(&vol));
        assert!(!prog.volatile_fields.contains(&plain));
    }
}
