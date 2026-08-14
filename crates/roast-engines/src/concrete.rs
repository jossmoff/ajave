//! Concrete interpreter: runs the program once with default (all-zero) nondet
//! values. This catches trivial bugs quickly without a solver.
//!
//! **Design rule:** This engine must NOT contain hardcoded nondet choice
//! patterns or magic values. Finding the right inputs to trigger a violation
//! is the SMT BMC engine's job. Adding patterns here is overfitting to
//! specific test cases and amounts to cheating.
//!
//! String tracking: `nondetString()` produces a `Nondet(Ty::Str)` rvalue in
//! the IR. The engine defaults to the empty string, allocates a fresh
//! reference ID, and records the content in `str_store`. String method calls
//! remain in the IR as `Rvalue::Call` (via `CallModel::StrCall`) so this
//! interpreter can evaluate them against the tracked content instead of
//! returning Unknown.

use std::collections::{HashMap, HashSet};

use log::{debug, info};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::verdict::{NondetEntry, NondetValue, Witness};
use roast_ir::*;
use roast_models as models;

use crate::math_eval::{eval_math_call, is_concrete_math_call};
use crate::str_eval::eval_str_call;

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Value {
    I32(i32),
    I64(i64),
    /// Unique allocation identity.  0 = null; 1 = non-null constant (string
    /// literals, class objects, any opaque non-null ref we didn't allocate
    /// ourselves); values ≥ 2 are fresh allocations from `alloc_id`.
    Ref(u64),
    Unknown,
}

impl Value {
    fn as_i64(self) -> i64 {
        match self {
            Value::I32(v) => v as i64,
            Value::I64(v) => v,
            _ => 0,
        }
    }
    fn nonzero(self) -> bool {
        match self {
            Value::I32(v) => v != 0,
            Value::I64(v) => v != 0,
            Value::Ref(id) => id != 0,
            Value::Unknown => false,
        }
    }
}

/// Outcome of running one concrete path to completion.
enum Outcome {
    /// Ran to a `Return` with nothing amiss.
    Clean,
    /// Ran to a `Return` carrying a value.
    ReturnedValue(Value),
    /// `Verifier.assume` failed: this path is uninteresting, not unsafe.
    Halted,
    /// A `Check` failed with nothing able to catch it.
    Violated {
        method: MethodKey,
        oid: ObligationId,
        witness: Vec<i64>,
        entries: Vec<NondetEntry>,
    },
    /// Ran out of budget or hit something we can't interpret.
    Inconclusive,
    /// Method threw an exception of this class.
    Threw(String),
}

/// Result of inlining a method call.
enum InlineResult {
    Returned(Value),
    Halted,
    Violated {
        method: MethodKey,
        oid: ObligationId,
        witness: Vec<i64>,
        entries: Vec<NondetEntry>,
    },
    Threw(String),
}

/// Result of evaluating a Check obligation.
enum CheckResult {
    /// Route to an exception handler block.
    Route(BlockId),
    /// Exit run_body with this outcome.
    Exit(Outcome),
}

/// The evaluator for everything except `Nondet` and string method `Call`s,
/// which `run_with_choices` intercepts before they ever reach here.
struct Run {
    store: HashMap<VarId, Value>,
}

impl Run {
    fn eval(&self, op: &Operand) -> Value {
        match op {
            Operand::Var(v) => self.store.get(v).copied().unwrap_or(Value::Unknown),
            Operand::Const(Const::Int(n)) => Value::I32(*n),
            Operand::Const(Const::Long(n)) => Value::I64(*n),
            Operand::Const(Const::Null) => Value::Ref(0),
            // String literals and class constants are non-null, but we don't
            // allocate a unique ID for them (they're interned constants).
            Operand::Const(_) => Value::Ref(1),
        }
    }

    fn eval_rvalue(&mut self, rv: &Rvalue) -> Value {
        match rv {
            Rvalue::Use(o) => self.eval(o),
            Rvalue::Neg(o) => match self.eval(o) {
                Value::I32(v) => Value::I32(v.wrapping_neg()),
                Value::I64(v) => Value::I64(v.wrapping_neg()),
                _ => Value::Unknown,
            },
            Rvalue::Bin(op, a, b) => self.eval_bin(*op, self.eval(a), self.eval(b)),
            Rvalue::New(_cls) => Value::Unknown, // handled in run_with_choices
            Rvalue::NewArray { .. } => Value::Ref(0), // handled in run_with_choices
            Rvalue::GetStatic(_) | Rvalue::GetField { .. } | Rvalue::ArrayLoad { .. } => {
                Value::Unknown
            }
            Rvalue::ArrayLength(_) => Value::Unknown,
            Rvalue::InstanceOf { .. } => Value::Unknown,
            // String/StringBuilder calls are intercepted in run_with_choices
            // before reaching here. Any remaining Call (unmodelled code that
            // survived the lifter without diverging) returns Unknown.
            Rvalue::Call { .. } => Value::Unknown,
            Rvalue::Cast(ty, o) => match (ty, self.eval(o)) {
                (Ty::Int, Value::I64(v)) => Value::I32(v as i32),
                (Ty::Long, Value::I32(v)) => Value::I64(v as i64),
                (_, v) => v,
            },
            Rvalue::Cmp(kind, a, b) => {
                let av = self.eval(a);
                let bv = self.eval(b);
                if matches!(av, Value::Unknown) || matches!(bv, Value::Unknown) {
                    return Value::Unknown;
                }
                let (x, y) = (av.as_i64(), bv.as_i64());
                match kind {
                    CmpKind::Long => Value::I32(x.cmp(&y) as i32),
                    CmpKind::FloatL | CmpKind::FloatG => {
                        // For concrete, we can't easily do float compare
                        // since values are stored as i64. Just use integer cmp.
                        Value::I32(x.cmp(&y) as i32)
                    }
                }
            }
            Rvalue::Nondet(..) | Rvalue::Havoc(_) => {
                unreachable!("Nondet/Havoc is handled in run_with_choices")
            }
        }
    }

    fn eval_bin(&self, op: BinOp, a: Value, b: Value) -> Value {
        use BinOp::*;

        // Unknown propagation: any unknown operand yields an unknown result.
        if matches!(a, Value::Unknown) || matches!(b, Value::Unknown) {
            return Value::Unknown;
        }

        let wide = matches!(a, Value::I64(_)) || matches!(b, Value::I64(_));
        match op {
            Eq | Ne | Lt | Le | Gt | Ge => {
                if let (Value::Ref(na), Value::Ref(nb)) = (a, b) {
                    let eq = na == nb;
                    return Value::I32(match op {
                        Eq => eq as i32,
                        Ne => !eq as i32,
                        _ => 0,
                    });
                }
                let (x, y) = (a.as_i64(), b.as_i64());
                let r = match op {
                    Eq => x == y,
                    Ne => x != y,
                    Lt => x < y,
                    Le => x <= y,
                    Gt => x > y,
                    Ge => x >= y,
                    _ => unreachable!(),
                };
                Value::I32(r as i32)
            }
            Add | Sub | Mul | Div | Rem if wide => {
                let (x, y) = (a.as_i64(), b.as_i64());
                Value::I64(match op {
                    Add => x.wrapping_add(y),
                    Sub => x.wrapping_sub(y),
                    Mul => x.wrapping_mul(y),
                    Div => x.checked_div(y).unwrap_or(0),
                    Rem => x.checked_rem(y).unwrap_or(0),
                    _ => unreachable!(),
                })
            }
            Add | Sub | Mul | Div | Rem => {
                let (x, y) = (a.as_i64() as i32, b.as_i64() as i32);
                Value::I32(match op {
                    Add => x.wrapping_add(y),
                    Sub => x.wrapping_sub(y),
                    Mul => x.wrapping_mul(y),
                    Div => x.checked_div(y).unwrap_or(0),
                    Rem => x.checked_rem(y).unwrap_or(0),
                    _ => unreachable!(),
                })
            }
            And | Or | Xor | Shl | Shr | UShr if wide => {
                let (x, y) = (a.as_i64(), b.as_i64());
                Value::I64(match op {
                    And => x & y,
                    Or => x | y,
                    Xor => x ^ y,
                    Shl => x.wrapping_shl(y as u32),
                    Shr => x.wrapping_shr(y as u32),
                    UShr => ((x as u64) >> (y as u32 & 63)) as i64,
                    _ => unreachable!(),
                })
            }
            And | Or | Xor | Shl | Shr | UShr => {
                let (x, y) = (a.as_i64() as i32, b.as_i64() as i32);
                Value::I32(match op {
                    And => x & y,
                    Or => x | y,
                    Xor => x ^ y,
                    Shl => x.wrapping_shl(y as u32),
                    Shr => x.wrapping_shr(y as u32),
                    UShr => ((x as u32) >> (y as u32 & 31)) as i32,
                    _ => unreachable!(),
                })
            }
        }
    }
}

/// Find a handler in `block`'s exceptional edges matching `class`, preferring
/// the first that covers it (mirrors JVM handler-table ordering: first match
/// wins).
fn route(prog: &Program, block: &Block, class: &str) -> Option<BlockId> {
    for e in &block.exceptional {
        match &e.class {
            None => return Some(e.target),
            Some(c) if prog.is_subtype(class, c) => return Some(e.target),
            _ => {}
        }
    }
    None
}


// String eval (`eval_str_call`) moved to str_eval.rs
// Math eval (`eval_math_call`, `is_concrete_math_call`) moved to math_eval.rs
/// Shared mutable state for a concrete execution — threaded through call
/// inlining so field reads/writes and allocations are visible across frames.
struct ConcreteState<'a> {
    prog: &'a Program,
    choices: &'a [i64],
    choice_idx: usize,
    trace: Vec<i64>,
    entries: Vec<NondetEntry>,
    steps: u64,
    alloc_id: u64,
    alloc_types: HashMap<u64, String>,
    array_lengths: HashMap<u64, i64>,
    str_store: HashMap<u64, String>,
    sb_store: HashMap<u64, String>,
    /// Instance fields: (alloc_id, field_name) -> Value.
    inst_fields: HashMap<(u64, String), Value>,
    /// Static fields: (class, field_name) -> Value.
    static_fields: HashMap<(String, String), Value>,
    /// Current call depth for bounding inlining.
    call_depth: u32,
    /// Classes whose `<clinit>` has already been executed.
    initialized_classes: HashSet<String>,
}

/// Maximum call inlining depth to prevent infinite recursion.
const MAX_CALL_DEPTH: u32 = 20;

impl<'a> ConcreteState<'a> {
    fn new(prog: &'a Program, choices: &'a [i64], step_budget: u64) -> Self {
        ConcreteState {
            prog,
            choices,
            choice_idx: 0,
            trace: Vec::new(),
            entries: Vec::new(),
            steps: step_budget,
            alloc_id: 2,
            alloc_types: HashMap::new(),
            array_lengths: HashMap::new(),
            str_store: HashMap::new(),
            sb_store: HashMap::new(),
            inst_fields: HashMap::new(),
            static_fields: HashMap::new(),
            call_depth: 0,
            initialized_classes: HashSet::new(),
        }
    }

    fn eval_op(&self, op: &Operand, store: &HashMap<VarId, Value>) -> Value {
        match op {
            Operand::Var(v) => store.get(v).copied().unwrap_or(Value::Unknown),
            Operand::Const(Const::Int(n)) => Value::I32(*n),
            Operand::Const(Const::Long(n)) => Value::I64(*n),
            Operand::Const(Const::Null) => Value::Ref(0),
            Operand::Const(_) => Value::Ref(1),
        }
    }

    /// Run `<clinit>` for `class` if it hasn't been run yet. This initialises
    /// static fields (enum constants, $assertionsDisabled, etc.) so that
    /// subsequent `GetStatic` reads return concrete values rather than Unknown.
    fn ensure_clinit(&mut self, class: &str) {
        if self.initialized_classes.contains(class) {
            return;
        }
        // Mark as initialized *before* running to prevent infinite recursion
        // (a <clinit> may reference its own class's statics).
        self.initialized_classes.insert(class.to_string());

        let clinit_key = MethodKey {
            class: class.to_string(),
            name: "<clinit>".to_string(),
            desc: "()V".to_string(),
        };
        if let Some(body) = self.prog.body(&clinit_key) {
            let body = body.clone();
            self.call_depth += 1;
            let _ = self.run_body(&body, HashMap::new());
            self.call_depth -= 1;
        }
    }

    /// Try to inline a user method call. Returns Some(return_value) on success.
    fn try_inline_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
        caller_store: &HashMap<VarId, Value>,
    ) -> Option<InlineResult> {
        if self.call_depth >= MAX_CALL_DEPTH {
            return None;
        }
        let body = self.prog.body(target)?;

        // Build callee's local store by mapping args to local slots.
        let mut callee_store: HashMap<VarId, Value> = HashMap::new();
        let mut slot = 0u16;
        for arg in args {
            let val = self.eval_op(arg, caller_store);
            if let Some((vid_idx, vinfo)) = body
                .vars
                .iter()
                .enumerate()
                .find(|(_, vi)| matches!(vi.kind, VarKind::Local(s) if s == slot))
            {
                callee_store.insert(VarId(vid_idx as u32), val);
                slot += if vinfo.ty.is_wide() { 2 } else { 1 };
            } else {
                slot += 1;
            }
        }

        self.call_depth += 1;
        let result = self.run_body(body, callee_store);
        self.call_depth -= 1;
        match result {
            Outcome::Clean => Some(InlineResult::Returned(Value::Unknown)),
            Outcome::ReturnedValue(v) => Some(InlineResult::Returned(v)),
            Outcome::Halted => Some(InlineResult::Halted),
            Outcome::Violated {
                method,
                oid,
                witness,
                entries,
            } => Some(InlineResult::Violated {
                method,
                oid,
                witness,
                entries,
            }),
            Outcome::Inconclusive => None,
            Outcome::Threw(cls) => Some(InlineResult::Threw(cls)),
        }
    }

    /// Execute a body to completion. The `store` is the callee's local variable
    /// map; heap state is shared through `self`.
    /// Evaluate an rvalue in the context of a concrete store.
    /// Returns `Ok(value)` for the computed result, or `Err(outcome)` for early termination.
    fn eval_assign(&mut self, rv: &Rvalue, store: &mut HashMap<VarId, Value>) -> Result<Value, Outcome> {
        match rv {
            Rvalue::Nondet(ty, _) => Ok(self.eval_nondet(ty)),
            Rvalue::Havoc(ty) => Ok(self.eval_havoc(ty)),
            Rvalue::New(cls) => {
                let aid = self.alloc_id;
                self.alloc_id += 1;
                self.alloc_types.insert(aid, cls.clone());
                if cls == "java/lang/StringBuilder" || cls == "java/lang/StringBuffer" {
                    self.sb_store.insert(aid, String::new());
                }
                Ok(Value::Ref(aid))
            }
            Rvalue::NewArray { len, .. } => {
                let len_val = self.eval_op(len, store);
                let aid = self.alloc_id;
                self.alloc_id += 1;
                if let Value::I32(n) = len_val {
                    self.array_lengths.insert(aid, n as i64);
                }
                Ok(Value::Ref(aid))
            }
            Rvalue::InstanceOf { obj, class } => {
                let obj_val = self.eval_op(obj, store);
                Ok(match obj_val {
                    Value::Ref(0) => Value::I32(0),
                    Value::Ref(aid) => match self.alloc_types.get(&aid) {
                        Some(known) if self.prog.supers.contains_key(known.as_str()) => {
                            Value::I32(self.prog.is_subtype(known, class) as i32)
                        }
                        Some(_) => Value::I32(0),
                        None => Value::Unknown,
                    },
                    _ => Value::Unknown,
                })
            }
            Rvalue::ArrayLength(arr) => {
                let aid = match arr {
                    Operand::Var(vid) => match store.get(vid) {
                        Some(Value::Ref(aid)) => Some(*aid),
                        _ => None,
                    },
                    _ => None,
                };
                Ok(match aid.and_then(|a| self.array_lengths.get(&a)) {
                    Some(&len) => Value::I32(len as i32),
                    None => Value::Unknown,
                })
            }
            Rvalue::Call { target, args, .. }
                if is_concrete_math_call(&target.class, &target.name) =>
            {
                Ok(eval_math_call(target, args, store))
            }
            Rvalue::Call { target, args, .. }
                if models::STR_OWNERS.contains(&target.class.as_str()) =>
            {
                Ok(eval_str_call(
                    target, args, store,
                    &mut self.str_store, &mut self.sb_store, &mut self.alloc_id,
                ))
            }
            Rvalue::Call { target, args, .. } => {
                match self.try_inline_call(target, args, store) {
                    Some(InlineResult::Returned(rv)) => Ok(rv),
                    Some(InlineResult::Halted) => Err(Outcome::Halted),
                    Some(InlineResult::Violated { method, oid, witness, entries }) => {
                        Err(Outcome::Violated { method, oid, witness, entries })
                    }
                    Some(InlineResult::Threw(cls)) => Err(Outcome::Threw(cls)),
                    None => {
                        let mut r = Run { store: std::mem::take(store) };
                        let val = r.eval_rvalue(rv);
                        *store = r.store;
                        Ok(val)
                    }
                }
            }
            Rvalue::GetField { obj, field } => {
                let obj_val = self.eval_op(obj, store);
                Ok(match obj_val {
                    Value::Ref(aid) if aid != 0 => self
                        .inst_fields
                        .get(&(aid, field.name.clone()))
                        .copied()
                        .unwrap_or(Value::Unknown),
                    _ => Value::Unknown,
                })
            }
            Rvalue::GetStatic(fk) => {
                if fk.name == "$assertionsDisabled" {
                    return Ok(Value::I32(0));
                }
                self.ensure_clinit(&fk.class);
                Ok(self.static_fields
                    .get(&(fk.class.clone(), fk.name.clone()))
                    .copied()
                    .unwrap_or_else(|| {
                        if self.prog.bodies.keys().any(|k| k.class == fk.class) {
                            match fk.desc.as_bytes().first() {
                                Some(b'J') => Value::I64(0),
                                Some(b'L') | Some(b'[') => Value::Ref(0),
                                _ => Value::I32(0),
                            }
                        } else {
                            Value::Unknown
                        }
                    }))
            }
            other => {
                let mut r = Run { store: std::mem::take(store) };
                let val = r.eval_rvalue(other);
                *store = r.store;
                Ok(val)
            }
        }
    }

    /// Evaluate a Nondet rvalue: pick a choice and record in trace.
    fn eval_nondet(&mut self, ty: &Ty) -> Value {
        let raw = self.choices.get(self.choice_idx).copied().unwrap_or(0);
        self.choice_idx += 1;
        let line: Option<u16> = None;
        match ty {
            Ty::Str => {
                self.trace.push(raw);
                let chosen = String::new();
                self.entries.push(NondetEntry {
                    value: NondetValue::Str(chosen.clone()),
                    nondet_method: "nondetString",
                    line,
                });
                let aid = self.alloc_id;
                self.alloc_id += 1;
                self.str_store.insert(aid, chosen);
                Value::Ref(aid)
            }
            Ty::Ref => {
                let aid = self.alloc_id;
                self.alloc_id += 1;
                Value::Ref(aid)
            }
            Ty::Long => {
                self.trace.push(raw);
                self.entries.push(NondetEntry {
                    value: NondetValue::Long(raw),
                    nondet_method: "nondetLong",
                    line,
                });
                Value::I64(raw)
            }
            _ => {
                self.trace.push(raw);
                self.entries.push(NondetEntry {
                    value: NondetValue::Int(raw as i32),
                    nondet_method: "nondetInt",
                    line,
                });
                Value::I32(raw as i32)
            }
        }
    }

    /// Evaluate a Havoc rvalue: default value without witness recording.
    fn eval_havoc(&mut self, ty: &Ty) -> Value {
        match ty {
            Ty::Long => Value::I64(0),
            Ty::Str | Ty::Ref => {
                let aid = self.alloc_id;
                self.alloc_id += 1;
                if *ty == Ty::Str {
                    self.str_store.insert(aid, String::new());
                }
                Value::Ref(aid)
            }
            _ => Value::I32(0),
        }
    }

    /// Evaluate a Check obligation. Returns `Some(outcome)` for early exit,
    /// `None` to continue, or `Some(Outcome::Goto(target))` for exception routing.
    fn eval_check(
        &mut self,
        body: &Body,
        block: &Block,
        oid: ObligationId,
        store: &mut HashMap<VarId, Value>,
    ) -> Option<CheckResult> {
        let ob = body.obligation(oid);
        let ok = match &ob.cond {
            Operand::Const(Const::Int(v)) => *v != 0,
            other => {
                let v = match other {
                    Operand::Var(vid) => store.get(vid).copied().unwrap_or(Value::Unknown),
                    _ => Value::Unknown,
                };
                if v == Value::Unknown {
                    return Some(CheckResult::Exit(Outcome::Inconclusive));
                }
                v.nonzero()
            }
        };
        if !ok {
            if let Some(class) = models::exception_class(ob.kind) {
                if let Some(target) = route(self.prog, block, class) {
                    if let Some(slot) = body
                        .vars.iter().enumerate()
                        .find(|(_, vi)| vi.kind == VarKind::Stack(0))
                        .map(|(i, _)| VarId(i as u32))
                    {
                        let aid = self.alloc_id;
                        self.alloc_id += 1;
                        store.insert(slot, Value::Ref(aid));
                    }
                    return Some(CheckResult::Route(target));
                }
            }
            return Some(CheckResult::Exit(Outcome::Violated {
                method: body.key.clone(),
                oid,
                witness: std::mem::take(&mut self.trace),
                entries: std::mem::take(&mut self.entries),
            }));
        }
        None
    }

    fn run_body(&mut self, body: &Body, mut store: HashMap<VarId, Value>) -> Outcome {
        let mut block = body.entry;
        let mut idx = 0usize;

        loop {
            if self.steps == 0 {
                return Outcome::Inconclusive;
            }
            self.steps -= 1;

            let b = body.block(block);
            if idx >= b.stmts.len() {
                match &b.term {
                    Terminator::Goto(t) => { block = *t; idx = 0; }
                    Terminator::Branch { cond, then_, else_ } => {
                        let cv = store
                            .get(match cond {
                                Operand::Var(v) => v,
                                _ => unreachable!("branch cond is always a temp"),
                            })
                            .copied()
                            .unwrap_or(Value::Unknown);
                        if cv == Value::Unknown { return Outcome::Inconclusive; }
                        block = if cv.nonzero() { *then_ } else { *else_ };
                        idx = 0;
                    }
                    Terminator::Switch { value, cases, default } => {
                        let v = match value {
                            Operand::Var(vid) => store.get(vid).copied().unwrap_or(Value::Unknown),
                            other => Value::I32(match other {
                                Operand::Const(Const::Int(n)) => *n,
                                _ => 0,
                            }),
                        }.as_i64() as i32;
                        block = cases.iter().find(|(k, _)| *k == v).map(|(_, t)| *t).unwrap_or(*default);
                        idx = 0;
                    }
                    Terminator::Return(ret) => {
                        if let Some(op) = ret {
                            let v = self.eval_op(op, &store);
                            return Outcome::ReturnedValue(v);
                        }
                        return Outcome::Clean;
                    }
                    Terminator::Halt => return Outcome::Halted,
                    Terminator::Throw(op) => {
                        let thrown_class = match op {
                            Operand::Var(v) => {
                                if let Some(Value::Ref(aid)) = store.get(v) {
                                    self.alloc_types.get(aid).cloned()
                                } else { None }
                            }
                            _ => None,
                        };
                        match thrown_class {
                            Some(cls) => {
                                if let Some(target) = route(self.prog, b, &cls) {
                                    block = target;
                                    idx = 0;
                                    continue;
                                }
                                return Outcome::Threw(cls);
                            }
                            None => return Outcome::Inconclusive,
                        }
                    }
                    Terminator::Diverge(_) => return Outcome::Inconclusive,
                }
                continue;
            }

            let stmt = b.stmts[idx].clone();
            match &stmt {
                Stmt::Assign(v, rv) => {
                    match self.eval_assign(rv, &mut store) {
                        Ok(val) => { store.insert(*v, val); }
                        Err(Outcome::Threw(cls)) => {
                            if let Some(target) = route(self.prog, b, &cls) {
                                block = target;
                                idx = 0;
                                continue;
                            }
                            return Outcome::Threw(cls);
                        }
                        Err(outcome) => return outcome,
                    }
                }
                Stmt::Assume(op) => {
                    let v = store
                        .get(match op {
                            Operand::Var(v) => v,
                            _ => unreachable!("assume operand is always a temp"),
                        })
                        .copied()
                        .unwrap_or(Value::Unknown);
                    if !v.nonzero() { return Outcome::Halted; }
                }
                Stmt::PutField { obj, field, val } => {
                    let obj_val = self.eval_op(obj, &store);
                    let v = self.eval_op(val, &store);
                    if let Value::Ref(aid) = obj_val {
                        if aid != 0 {
                            self.inst_fields.insert((aid, field.name.clone()), v);
                        }
                    }
                }
                Stmt::PutStatic(fk, val) => {
                    self.ensure_clinit(&fk.class);
                    let v = self.eval_op(val, &store);
                    self.static_fields.insert((fk.class.clone(), fk.name.clone()), v);
                }
                Stmt::ArrayStore { .. } => {}
                Stmt::Check(oid) => {
                    if let Some(result) = self.eval_check(body, b, *oid, &mut store) {
                        match result {
                            CheckResult::Route(target) => {
                                block = target;
                                idx = 0;
                                continue;
                            }
                            CheckResult::Exit(outcome) => return outcome,
                        }
                    }
                }
                Stmt::Nop => {}
            }
            idx += 1;
        }
    }
}

/// Run the body once against a fully-predetermined sequence of nondet
/// choices. Choices beyond what's provided fall back to `0`.
fn run_with_choices(prog: &Program, body: &Body, choices: &[i64], step_budget: u64) -> Outcome {
    let mut state = ConcreteState::new(prog, choices, step_budget);
    state.run_body(body, HashMap::new())
}

/// Run a single all-zero probe. The concrete engine is a cheap first pass
/// that catches bugs reachable with default values — nothing more. Finding
/// the *right* nondet inputs to trigger a violation is the SMT engine's job.
///
/// **DO NOT** add hardcoded choice patterns here (e.g. boundary values,
/// alternating booleans). That is overfitting to specific test cases and
/// amounts to cheating. If a bug needs a particular nondet value to trigger,
/// the SMT BMC engine should find it via constraint solving.
fn search(prog: &Program, body: &Body) -> Vec<(MethodKey, ObligationId, Witness)> {
    let step_budget = 200_000u64;
    if let Outcome::Violated {
        method,
        oid,
        witness,
        entries,
    } = run_with_choices(prog, body, &[], step_budget)
    {
        vec![(
            method,
            oid,
            Witness {
                nondet_sequence: witness,
                entries,
            },
        )]
    } else {
        vec![]
    }
}

pub struct Concrete {
    done: bool,
}

impl Concrete {
    pub fn new() -> Self {
        Concrete { done: false }
    }
}

impl Engine for Concrete {
    fn id(&self) -> EngineId {
        EngineId("concrete")
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

        info!("concrete: probing with default values on {entry:?}");
        let violations = search(prog, body);
        debug!(
            "concrete: search complete, found {} violation(s)",
            violations.len()
        );

        let mut advanced = false;
        for (method, oid, witness) in violations {
            let oref = ObligationRef {
                method,
                id: oid,
            };
            debug!(
                "concrete: publishing violation at {oref:?}, witness={:?}",
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
