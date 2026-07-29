//! roast-ir: the program representation.
//!
//! Zero internal dependencies by design -- every other crate depends on
//! this one, never the reverse. If code here ever needs to import from
//! `roast-core` or `roast-frontend`, that's a sign the boundary has been
//! drawn in the wrong place.
//!
//! ## The IR itself
//!
//! Design decisions worth stating, because they are hard to reverse later:
//!
//! * **Not a stack machine.** The JVM operand stack is eliminated at lift time
//!   by simulating it abstractly and materialising entries into registers
//!   `s0, s1, ...`. Invariant inference over a stack machine is miserable;
//!   over registers it is routine. This is Jimple's trick and it is the right one.
//! * **Not SSA yet.** Non-SSA three-address is enough through stage 6. SSA
//!   arrives with loops, where phi nodes start earning their keep. Deferring it
//!   keeps the lifter debuggable while the frontend is still the risky part.
//! * **Implicit exceptions are explicit.** A division emits a `DivByZero`
//!   obligation; an array access emits a `ArrayBounds` obligation. Both SV-COMP
//!   Java specifications then reduce to reachability of an obligation violation,
//!   so the core never needs to know which property it is checking.
//! * **Arena indices, not pointers.** `BlockId`/`VarId` are `u32` newtypes into
//!   flat vectors. No `Rc`, no lifetimes threaded through the analyses.

pub mod verdict;

use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct VarId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct BlockId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ObligationId(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Ty {
    Int,
    Long,
    Float,
    Double,
    Ref,
    /// A concrete `java.lang.String` value whose content may be known to
    /// engines that track strings. Represented as a reference at the JVM level
    /// but distinguished so the concrete engine can pick from a string pool.
    Str,
}

impl Ty {
    /// Category-2 types occupy two slots on the stack and in the local array.
    pub fn is_wide(self) -> bool {
        matches!(self, Ty::Long | Ty::Double)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Const {
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    Null,
    Str(String),
    Class(String),
}

impl Const {
    pub fn ty(&self) -> Ty {
        match self {
            Const::Int(_) => Ty::Int,
            Const::Long(_) => Ty::Long,
            Const::Float(_) => Ty::Float,
            Const::Double(_) => Ty::Double,
            Const::Null | Const::Str(_) | Const::Class(_) => Ty::Ref,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operand {
    Var(VarId),
    Const(Const),
}

impl Operand {
    pub fn int(v: i32) -> Operand {
        Operand::Const(Const::Int(v))
    }
    pub fn is_false(&self) -> bool {
        matches!(self, Operand::Const(Const::Int(0)))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    UShr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        use BinOp::*;
        match self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            Rem => "%",
            And => "&",
            Or => "|",
            Xor => "^",
            Shl => "<<",
            Shr => ">>",
            UShr => ">>>",
            Eq => "==",
            Ne => "!=",
            Lt => "<",
            Le => "<=",
            Gt => ">",
            Ge => ">=",
        }
    }
}

/// Fully-qualified method identity. Internal (slash-separated) class names.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MethodKey {
    pub class: String,
    pub name: String,
    pub desc: String,
}

impl fmt::Display for MethodKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}{}", self.class, self.name, self.desc)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FieldKey {
    pub class: String,
    pub name: String,
    pub desc: String,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Rvalue {
    Use(Operand),
    Bin(BinOp, Operand, Operand),
    Neg(Operand),
    /// A fresh unconstrained value of the given type. This is how
    /// `Verifier.nondet*()` is modelled — and also how any unmodelled pure
    /// call degrades soundly, since havoc over-approximates every result.
    Nondet(Ty),
    GetStatic(FieldKey),
    GetField {
        obj: Operand,
        field: FieldKey,
    },
    ArrayLoad {
        arr: Operand,
        idx: Operand,
    },
    ArrayLength(Operand),
    NewArray {
        elem: String,
        len: Operand,
    },
    InstanceOf {
        obj: Operand,
        class: String,
    },
    /// Primitive conversion (`i2l`, `l2i`, `i2b`, ...).
    Cast(Ty, Operand),
    /// Three-way comparison (`lcmp`, `fcmpl`, `dcmpg`): -1 / 0 / 1.
    Cmp(Operand, Operand),
    New(String),
    Call {
        target: MethodKey,
        args: Vec<Operand>,
        is_virtual: bool,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Assign(VarId, Rvalue),
    PutStatic(FieldKey, Operand),
    PutField {
        obj: Operand,
        field: FieldKey,
        val: Operand,
    },
    ArrayStore {
        arr: Operand,
        idx: Operand,
        val: Operand,
    },
    /// Constrain the path. `Verifier.assume` lowers to this; so does the
    /// branch condition when an engine follows a specific edge.
    Assume(Operand),
    /// Reaching this statement obliges the analysis to show the referenced
    /// obligation's safety condition holds.
    Check(ObligationId),
    Nop,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Terminator {
    Goto(BlockId),
    Branch {
        cond: Operand,
        then_: BlockId,
        else_: BlockId,
    },
    Return(Option<Operand>),
    Switch {
        value: Operand,
        cases: Vec<(i32, BlockId)>,
        default: BlockId,
    },
    Throw(Operand),
    /// Control leaves the analysed fragment and does not come back —
    /// `Verifier.assume(false)` lowers to this.
    Halt,
    /// We could not lift past here. Anything an over-approximating engine
    /// wants to conclude about states dominated by this must be `Unknown`.
    /// Kept as an explicit node rather than a silent truncation precisely so
    /// that unsoundness is impossible to introduce by omission.
    Diverge(String),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ObligationKind {
    /// An `AssertionError` throw is reachable (the `assert.prp` property).
    Assertion,
    DivByZero,
    NullDeref,
    ArrayBounds,
    NegArraySize,
    ClassCast,
}

impl ObligationKind {
    /// Which SV-COMP Java property this obligation belongs to. The core does
    /// not care; the reporter filters on it.
    pub fn is_assertion(self) -> bool {
        matches!(self, ObligationKind::Assertion)
    }
}

#[derive(Clone, Debug)]
pub struct Obligation {
    pub id: ObligationId,
    pub kind: ObligationKind,
    /// The *safety* condition: the obligation is violated at a reachable state
    /// where this evaluates to false. A constant `0` therefore means "violated
    /// if this point is reachable at all", which is exactly the shape of an
    /// `AssertionError` throw.
    pub cond: Operand,
    pub bytecode_offset: u16,
    /// Source line from the classfile's LineNumberTable, for witnesses and
    /// for reading the IR next to the original program.
    pub line: Option<u16>,
    /// True when an exception raised here could be caught by a handler in this
    /// method. Such an obligation is not a runtime-exception-property violation
    /// even if it fires, because the exception never escapes `main`.
    pub guarded: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VarKind {
    /// JVM local variable slot.
    Local(u16),
    /// Materialised operand-stack slot at a given depth.
    Stack(u16),
    /// Compiler-introduced temporary.
    Temp,
}

#[derive(Clone, Debug)]
pub struct VarInfo {
    pub kind: VarKind,
    pub ty: Ty,
}

/// An exceptional control-flow edge derived from the method's exception table.
/// `class` is `None` for a catch-all (`finally`).
#[derive(Clone, Debug)]
pub struct ExcEdge {
    pub class: Option<String>,
    pub target: BlockId,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub id: BlockId,
    pub bytecode_offset: u16,
    pub stmts: Vec<Stmt>,
    pub term: Terminator,
    /// Where control goes if anything in this block throws. Computed at block
    /// granularity, which over-approximates: more edges means more reachable
    /// states, which is the safe direction for a TRUE claim.
    pub exceptional: Vec<ExcEdge>,
}

#[derive(Clone, Debug)]
pub struct Body {
    pub key: MethodKey,
    pub entry: BlockId,
    pub blocks: Vec<Block>,
    pub vars: Vec<VarInfo>,
    pub obligations: Vec<Obligation>,
}

impl Body {
    pub fn block(&self, id: BlockId) -> &Block {
        &self.blocks[id.0 as usize]
    }
    pub fn obligation(&self, id: ObligationId) -> &Obligation {
        &self.obligations[id.0 as usize]
    }

    /// Where a given obligation's `Check` statement lives. Used by any engine
    /// that needs to evaluate or route around a specific check -- the interval
    /// domain to read its abstract state there, the concrete engine to know
    /// which block's exceptional edges apply when it fails.
    pub fn var(&self, id: VarId) -> &VarInfo {
        &self.vars[id.0 as usize]
    }
    /// True when the body contains no `Diverge`. Over-approximating engines
    /// may only report `TRUE` for bodies where this holds.
    pub fn is_fully_lifted(&self) -> bool {
        !self
            .blocks
            .iter()
            .any(|b| matches!(b.term, Terminator::Diverge(_)))
    }
}

/// A single CFG edge, which is what a `Cpa` transfer relation runs over.
#[derive(Clone, Debug)]
pub enum Edge {
    /// Execute one statement, staying in the same block.
    Stmt(BlockId, usize),
    /// Leave a block along a terminator, optionally assuming the branch
    /// condition holds (`Some(true)` = then-edge, `Some(false)` = else-edge).
    Term(BlockId, Option<bool>, BlockId),
    /// Terminal edge with no successor.
    Exit(BlockId),
}

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub bodies: HashMap<MethodKey, Body>,
    /// class -> superclass, for hierarchy analysis and devirtualisation.
    pub supers: HashMap<String, String>,
    /// class -> declared interfaces.
    pub interfaces: HashMap<String, Vec<String>>,
    pub entry: Option<MethodKey>,
}

impl Program {
    pub fn body(&self, k: &MethodKey) -> Option<&Body> {
        self.bodies.get(k)
    }

    /// Is `sub` a subtype of `sup`, as far as the loaded hierarchy shows?
    /// Unknown classes answer `true`: not knowing must not let us rule an
    /// exceptional edge out.
    pub fn is_subtype(&self, sub: &str, sup: &str) -> bool {
        if sub == sup || sup == "java/lang/Object" {
            return true;
        }
        let mut cur = sub.to_string();
        loop {
            if let Some(ifs) = self.interfaces.get(&cur) {
                if ifs.iter().any(|i| i == sup || self.is_subtype(i, sup)) {
                    return true;
                }
            }
            match self.supers.get(&cur) {
                Some(next) if next != &cur => {
                    if next == sup {
                        return true;
                    }
                    cur = next.clone();
                }
                // Hierarchy runs out before we reach a class we loaded.
                _ => return !self.supers.contains_key(sub),
            }
        }
    }

    /// Concrete receivers for a virtual call: every loaded class that is a
    /// subtype of the declared owner and defines the method.
    pub fn devirtualise(&self, declared: &MethodKey) -> Vec<MethodKey> {
        let mut out = Vec::new();
        for k in self.bodies.keys() {
            if k.name == declared.name
                && k.desc == declared.desc
                && self.is_subtype(&k.class, &declared.class)
            {
                out.push(k.clone());
            }
        }
        out
    }

    /// Bodies transitively reachable from the entry point. `<clinit>` and
    /// `<init>` are deliberately *not* roots: we model class initialisation
    /// away (see `ASSERTIONS_DISABLED` in the lifter), so their unlifted
    /// bodies must not poison an otherwise complete proof.
    pub fn reachable_from_entry(&self) -> Vec<MethodKey> {
        let Some(entry) = &self.entry else {
            return self.bodies.keys().cloned().collect();
        };
        let mut seen: Vec<MethodKey> = Vec::new();
        let mut work = vec![entry.clone()];
        while let Some(k) = work.pop() {
            if seen.contains(&k) {
                continue;
            }
            seen.push(k.clone());
            let Some(body) = self.bodies.get(&k) else {
                continue;
            };
            for b in &body.blocks {
                for s in &b.stmts {
                    if let Stmt::Assign(_, Rvalue::Call { target, .. }) = s {
                        work.push(target.clone());
                    }
                }
            }
        }
        seen
    }

    /// Every obligation in the program, as (method, obligation id).
    pub fn obligations(&self) -> Vec<(MethodKey, ObligationId)> {
        let mut out = Vec::new();
        let mut keys: Vec<_> = self.bodies.keys().cloned().collect();
        keys.sort();
        for k in keys {
            let b = &self.bodies[&k];
            for o in &b.obligations {
                out.push((k.clone(), o.id));
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Pretty printing. Worth the lines: almost every frontend bug is found by
// reading the lifted IR next to `javap -c` output.
// ---------------------------------------------------------------------------

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Var(v) => write!(f, "v{}", v.0),
            Operand::Const(c) => write!(f, "{c}"),
        }
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Const::Int(i) => write!(f, "{i}"),
            Const::Long(i) => write!(f, "{i}L"),
            Const::Float(x) => write!(f, "{x}f"),
            Const::Double(x) => write!(f, "{x}d"),
            Const::Null => write!(f, "null"),
            Const::Str(s) => write!(f, "{s:?}"),
            Const::Class(c) => write!(f, "{c}.class"),
        }
    }
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rvalue::Use(o) => write!(f, "{o}"),
            Rvalue::Bin(op, a, b) => write!(f, "{a} {} {b}", op.symbol()),
            Rvalue::Neg(a) => write!(f, "-{a}"),
            Rvalue::Nondet(t) => write!(f, "nondet<{t:?}>()"),
            Rvalue::GetStatic(k) => write!(f, "{}.{}", k.class, k.name),
            Rvalue::GetField { obj, field } => write!(f, "{obj}.{}", field.name),
            Rvalue::ArrayLoad { arr, idx } => write!(f, "{arr}[{idx}]"),
            Rvalue::ArrayLength(a) => write!(f, "{a}.length"),
            Rvalue::NewArray { elem, len } => write!(f, "new {elem}[{len}]"),
            Rvalue::InstanceOf { obj, class } => write!(f, "{obj} instanceof {class}"),
            Rvalue::Cast(t, o) => write!(f, "({t:?}) {o}"),
            Rvalue::Cmp(a, b) => write!(f, "cmp({a}, {b})"),
            Rvalue::New(c) => write!(f, "new {c}"),
            Rvalue::Call { target, args, .. } => {
                let a: Vec<String> = args.iter().map(|x| x.to_string()).collect();
                write!(f, "call {}({})", target, a.join(", "))
            }
        }
    }
}

impl Body {
    pub fn render(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("method {} {{\n", self.key));
        for b in &self.blocks {
            s.push_str(&format!("  bb{}:  // @{}\n", b.id.0, b.bytecode_offset));
            for st in &b.stmts {
                s.push_str("    ");
                match st {
                    Stmt::Assign(v, r) => s.push_str(&format!("v{} = {r}", v.0)),
                    Stmt::PutStatic(k, o) => s.push_str(&format!("{}.{} = {o}", k.class, k.name)),
                    Stmt::PutField { obj, field, val } => {
                        s.push_str(&format!("{obj}.{} = {val}", field.name))
                    }
                    Stmt::ArrayStore { arr, idx, val } => {
                        s.push_str(&format!("{arr}[{idx}] = {val}"))
                    }
                    Stmt::Assume(o) => s.push_str(&format!("assume {o}")),
                    Stmt::Check(id) => {
                        let ob = self.obligation(*id);
                        s.push_str(&format!(
                            "check #{} {:?} requires {}",
                            id.0, ob.kind, ob.cond
                        ))
                    }
                    Stmt::Nop => s.push_str("nop"),
                }
                s.push('\n');
            }
            s.push_str("    ");
            match &b.term {
                Terminator::Goto(t) => s.push_str(&format!("goto bb{}", t.0)),
                Terminator::Branch { cond, then_, else_ } => {
                    s.push_str(&format!("if {cond} then bb{} else bb{}", then_.0, else_.0))
                }
                Terminator::Return(None) => s.push_str("return"),
                Terminator::Return(Some(o)) => s.push_str(&format!("return {o}")),
                Terminator::Switch {
                    value,
                    cases,
                    default,
                } => {
                    let cs: Vec<String> = cases
                        .iter()
                        .map(|(v, b)| format!("{v}=>bb{}", b.0))
                        .collect();
                    s.push_str(&format!(
                        "switch {value} [{}] default bb{}",
                        cs.join(", "),
                        default.0
                    ))
                }
                Terminator::Throw(o) => s.push_str(&format!("throw {o}")),
                Terminator::Halt => s.push_str("halt"),
                Terminator::Diverge(r) => s.push_str(&format!("DIVERGE({r})")),
            }
            if !b.exceptional.is_empty() {
                let es: Vec<String> = b
                    .exceptional
                    .iter()
                    .map(|e| format!("{} -> bb{}", e.class.as_deref().unwrap_or("*"), e.target.0))
                    .collect();
                s.push_str(&format!("    ! exc: {}\n", es.join(", ")));
            }
            s.push('\n');
        }
        s.push_str("}\n");
        s
    }
}
