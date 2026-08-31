//! Stepping interpreter for interleaving exploration.
//!
//! `concrete.rs` runs a body to completion, which is the wrong shape here: an
//! explorer has to interrupt a thread between actions. Rather than refactor a
//! working engine, this is a separate interpreter over the same `Value` type,
//! covering the subset the concurrency benchmarks need and refusing anything
//! else.
//!
//! # Stepping granularity, and why it is sound
//!
//! A step is not one statement. Threads are interleaved only at **visible
//! actions**: a shared field access, a monitor operation, or a thread lifecycle
//! call. Between two visible actions a thread runs uninterrupted.
//!
//! This is sound because local computation is unobservable to other threads.
//! If thread A computes `t = x*2+1` into its own locals and then writes a
//! field, no interleaving of A's arithmetic with B changes what B can see —
//! only the position of the *write* matters. Interleaving at statement
//! granularity would multiply the state space by the length of every
//! straight-line run while producing exactly the same set of distinguishable
//! behaviours.
//!
//! Reads count as visible actions too. A read is where a thread observes
//! another's write, so `if (h.s != null) h.s.length()` must be interleavable
//! between the check and the use — that is precisely the racy-null-deref shape.
//!
//! # What it refuses
//!
//! Anything it cannot execute faithfully returns `Step::Unsupported`, and the
//! explorer turns that into "cannot analyse". For an engine that may publish
//! `Violated`, guessing at an unmodelled construct would mean inventing bugs.

use std::collections::HashMap;

use ajave_core::artifact::ProgramPoint;
use ajave_models as models;
use ajave_ir::verdict::ThreadId;
use ajave_ir::{
    BinOp, BlockId, Body, Const, MethodKey, ObligationId, Operand, Program, Rvalue, Stmt,
    Terminator, VarId,
};

use crate::concurrent_state::{GlobalState, ObjId, ThreadState, ThreadStatus};

/// A concrete value. Mirrors `concrete::Value` but local to this interpreter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Val {
    Int(i64),
    /// Allocation identity; 0 is null.
    Ref(u32),
}

impl Val {
    pub fn nonzero(self) -> bool {
        match self {
            Val::Int(v) => v != 0,
            Val::Ref(r) => r != 0,
        }
    }
    fn as_int(self) -> i64 {
        match self {
            Val::Int(v) => v,
            Val::Ref(r) => r as i64,
        }
    }
}

/// A shared-memory or synchronisation access made by one step.
///
/// DPOR needs to know what a transition touched in order to decide whether two
/// transitions are *dependent* — whether their order can change the outcome.
/// Without this the explorer can only enumerate every interleaving blindly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Access {
    /// Read or write of an instance field.
    Field { obj: ObjId, name: String, write: bool },
    /// Read or write of a static field.
    Static { class: String, name: String, write: bool },
    /// Acquire or release of a monitor. Two monitor operations on the same
    /// object are always dependent: their order decides who gets the lock.
    Monitor(ObjId),
    /// A thread lifecycle action. `start` and `join` create happens-before
    /// edges, so they are dependent with everything that thread does.
    Lifecycle(ThreadId),
}

impl Access {
    /// Do these two accesses conflict — can swapping their order change what
    /// the program observes?
    ///
    /// Two reads of the same location commute, which is where most of DPOR's
    /// reduction comes from. Everything else touching the same location does
    /// not.
    pub fn conflicts(&self, other: &Access) -> bool {
        match (self, other) {
            (
                Access::Field { obj: a, name: n, write: w1 },
                Access::Field { obj: b, name: m, write: w2 },
            ) => a == b && n == m && (*w1 || *w2),
            (
                Access::Static { class: c1, name: n1, write: w1 },
                Access::Static { class: c2, name: n2, write: w2 },
            ) => c1 == c2 && n1 == n2 && (*w1 || *w2),
            (Access::Monitor(a), Access::Monitor(b)) => a == b,
            (Access::Lifecycle(a), Access::Lifecycle(b)) => a == b,
            _ => false,
        }
    }
}

/// What happened when a thread was advanced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// Ran to the next visible action (or terminated); explorer may switch.
    /// Carries what the step accessed, for DPOR's dependency test.
    Advanced(Vec<Access>),
    /// Thread finished.
    Terminated,
    /// Could not proceed. `Some(monitor)` when the thread blocked trying to
    /// acquire that monitor; `None` for a `join` waiting on another thread.
    ///
    /// The monitor is carried because DPOR needs it. A blocked acquire is
    /// *dependent* with whoever holds or will acquire the same monitor — that
    /// dependency is the whole reason the deadlocking interleaving exists — and
    /// without it the backtrack computation never creates the point that would
    /// explore the other acquire order. That is why no-deadlock previously had
    /// to run unreduced.
    Blocked(Option<ObjId>),
    /// An obligation's condition evaluated false.
    Violated(ObligationId, MethodKey),
    /// A construct this interpreter does not model.
    Unsupported(String),
}

/// One thread's private frame stack and locals.
#[derive(Clone, Debug)]
pub struct Frame {
    pub at: ProgramPoint,
    pub locals: HashMap<VarId, Val>,
    /// Where the caller's result goes, if this frame was entered by a call.
    pub ret_to: Option<VarId>,
}

/// Interpreter over a `GlobalState`, holding the program and allocation counter.

/// Operands an rvalue reads, for taint propagation.
fn rvalue_operands(rv: &Rvalue) -> Vec<Operand> {
    match rv {
        Rvalue::Use(o) | Rvalue::Neg(o) | Rvalue::Cast(_, _, o) => vec![o.clone()],
        Rvalue::Bin(_, a, b) | Rvalue::Cmp(_, a, b) => vec![a.clone(), b.clone()],
        Rvalue::GetField { obj, .. } => vec![obj.clone()],
        Rvalue::ArrayLoad { arr, idx } => vec![arr.clone(), idx.clone()],
        Rvalue::ArrayLength(a) => vec![a.clone()],
        Rvalue::InstanceOf { obj, .. } => vec![obj.clone()],
        Rvalue::Call { args, .. } => args.clone(),
        _ => Vec::new(),
    }
}

/// Does this call return a reference? Used only to pick a placeholder of the
/// right shape for a call we stepped over; the value is tainted either way.
fn ret_is_reference(rv: &Rvalue) -> bool {
    match rv {
        Rvalue::Call { target, .. } => {
            let after = target.desc.rsplit(')').next().unwrap_or("");
            after.starts_with('L') || after.starts_with('[')
        }
        _ => false,
    }
}

pub struct Interp<'a> {
    pub prog: &'a Program,
    pub next_obj: u32,
    /// Per-thread frame stacks, indexed by `ThreadId.0`.
    pub frames: Vec<Vec<Frame>>,
    /// Budget shared across all threads, so a spinning thread cannot hang us.
    pub steps_left: u64,
    /// Locals holding a value invented for a call we could not model, per
    /// thread, and anything derived from one.
    ///
    /// A concurrency witness is a *schedule*, and `Certifier` returns
    /// Inconclusive for those — they are never replayed on a real JVM. So a
    /// violation resting on an invented value would be reported as FALSE with
    /// nothing to catch it: a wrong answer, not a precision loss. Checks whose
    /// condition is tainted therefore decline instead of reporting.
    pub tainted: Vec<std::collections::HashSet<VarId>>,
    /// How many bodyless calls have been stepped over, of any purity.
    ///
    /// Separate from `skipped_calls`, which records only the ones that cost
    /// completeness. Every stepped-over call needs its destination given a
    /// placeholder and marked tainted, whether or not the callee was pure —
    /// conflating the two left pure calls with an unassigned destination, and
    /// the path died on "unknown operand" one statement later.
    pub stepped_over: usize,
    /// Library calls with no body that were stepped over.
    ///
    /// Stepping over them lets an interleaving run to completion, which DPOR
    /// needs, but it means the search no longer covers everything: the callee's
    /// effects are unmodelled. The explorer reads this and marks the
    /// exploration incomplete, so an exhausted search that stepped over a call
    /// is never reported as a proof.
    pub skipped_calls: Vec<String>,
    /// Runtime Thread object -> the ThreadId it controls.
    ///
    /// Populated at `Thread.<init>`, in the order threads are constructed,
    /// which matches the order `threads::discover` reports them. Without this
    /// mapping `start()` and `join()` cannot tell *which* thread they refer
    /// to, and both would have to be no-ops.
    pub thread_objs: HashMap<u32, ThreadId>,
    /// ThreadId -> the Runnable object its `run()` executes against.
    ///
    /// The worker's `this` must be the very object main passed to
    /// `new Thread(r)`. Fabricating a fresh identity instead makes the thread
    /// write to a different object than main reads, so a write that should be
    /// visible after `join()` silently is not — which looked exactly like a
    /// missing happens-before edge.
    pub runnable_objs: HashMap<ThreadId, u32>,
    /// Next ThreadId to hand out at `Thread.<init>`.
    pub next_tid: u32,
}

impl<'a> Interp<'a> {
    pub fn new(prog: &'a Program, steps: u64) -> Self {
        Interp {
            prog,
            next_obj: 1,
            frames: Vec::new(),
            steps_left: steps,
            skipped_calls: Vec::new(),
            tainted: Vec::new(),
            stepped_over: 0,
            thread_objs: HashMap::new(),
            runnable_objs: HashMap::new(),
            next_tid: 1,
        }
    }

    fn eval(&self, f: &Frame, op: &Operand) -> Option<Val> {
        Some(match op {
            Operand::Var(v) => *f.locals.get(v)?,
            Operand::Const(Const::Int(n)) => Val::Int(*n as i64),
            Operand::Const(Const::Long(n)) => Val::Int(*n),
            Operand::Const(Const::Null) => Val::Ref(0),
            // A string or class literal is a non-null opaque reference.
            Operand::Const(Const::Str(_) | Const::Class(_)) => Val::Ref(1),
            _ => return None,
        })
    }

    /// Is this statement a visible action — a point where another thread's
    /// interleaving could be observed?
    fn ensure_taint_slot(&mut self, tid: ThreadId) {
        while self.tainted.len() <= tid.0 as usize {
            self.tainted.push(std::collections::HashSet::new());
        }
    }

    fn is_tainted(&self, tid: ThreadId, v: VarId) -> bool {
        self.tainted
            .get(tid.0 as usize)
            .map(|s| s.contains(&v))
            .unwrap_or(false)
    }

    fn mark_tainted(&mut self, tid: ThreadId, v: VarId) {
        self.ensure_taint_slot(tid);
        self.tainted[tid.0 as usize].insert(v);
    }

    fn clear_tainted(&mut self, tid: ThreadId, v: VarId) {
        if let Some(s) = self.tainted.get_mut(tid.0 as usize) {
            s.remove(&v);
        }
    }

    fn is_visible(stmt: &Stmt) -> bool {
        match stmt {
            Stmt::PutField { .. } | Stmt::PutStatic(..) => true,
            Stmt::MonitorEnter(_) | Stmt::MonitorExit(_) => true,
            Stmt::Assign(_, rv) => matches!(
                rv,
                Rvalue::GetField { .. } | Rvalue::GetStatic(_) | Rvalue::Call { .. }
            ),
            _ => false,
        }
    }

    /// Advance `tid` to just past its next visible action.
    ///
    /// Runs invisible statements eagerly: they cannot be observed by another
    /// thread, so interleaving them would only enlarge the search.
    pub fn advance(&mut self, g: &mut GlobalState, tid: ThreadId) -> Step {
        let mut accesses: Vec<Access> = Vec::new();
        loop {
            if self.steps_left == 0 {
                return Step::Unsupported("step budget exhausted".into());
            }
            self.steps_left -= 1;

            let ti = match g.threads.iter().position(|t| t.id == tid) {
                Some(i) => i,
                None => return Step::Terminated,
            };
            if g.threads[ti].status == ThreadStatus::Terminated {
                return Step::Terminated;
            }
            // A joiner whose target has finished becomes runnable and advances
            // past the join() call.
            if let ThreadStatus::Joining { on } = g.threads[ti].status {
                let done = g
                    .threads
                    .iter()
                    .find(|t| t.id == on)
                    .map(|t| t.status == ThreadStatus::Terminated)
                    .unwrap_or(true);
                if !done {
                    // Waiting on a thread, not a monitor.
                    return Step::Blocked(None);
                }
                g.threads[ti].status = ThreadStatus::Runnable;
                if let Some(f) = self.frames[tid.0 as usize].last_mut() {
                    f.at.index += 1;
                }
            }

            let Some(frame) = self.frames[tid.0 as usize].last().cloned() else {
                g.threads[ti].status = ThreadStatus::Terminated;
                return Step::Terminated;
            };
            let Some(body) = self.prog.body(&frame.at.method) else {
                return Step::Unsupported(format!("no body for {}", frame.at.method));
            };
            let block = body.block(frame.at.block);

            // At the terminator?
            if frame.at.index >= block.stmts.len() {
                match self.run_terminator(g, tid, body, block.id, &frame) {
                    Ok(Some(step)) => return step,
                    Ok(None) => continue,
                    Err(why) => return Step::Unsupported(why),
                }
            }

            let stmt = block.stmts[frame.at.index].clone();
            let visible = Self::is_visible(&stmt);
            self.record_access(g, &stmt, &frame, &mut accesses);
            match self.run_stmt(g, tid, &stmt, &frame) {
                Ok(Some(step)) => return step,
                Ok(None) => {}
                Err(why) => return Step::Unsupported(why),
            }
            // A statement that parked the thread must be *retried*, not
            // stepped past. `monitorenter` says so by returning a `Step`, but a
            // modelled call cannot -- `do_call` returns a value -- so those
            // models set the status and rely on this check. Without it the
            // generic advance below stepped a blocked thread straight past its
            // own `lock()` and into the critical section unlocked, and parked a
            // `wait()` past the call so phase 2 never ran.
            //
            // Status is therefore the single source of truth for parking, and
            // any future model (latches, semaphores, barriers) blocks correctly
            // just by setting it.
            if let Some(t) = g.threads.iter().find(|t| t.id == tid) {
                match t.status {
                    ThreadStatus::Blocked { monitor } | ThreadStatus::Waiting { monitor } => {
                        return Step::Blocked(Some(monitor));
                    }
                    _ => {}
                }
            }
            // Advance the program counter unless the statement moved it
            // itself (a call pushes a frame).
            if let Some(f) = self.frames[tid.0 as usize].last_mut() {
                if f.at == frame.at {
                    f.at.index += 1;
                }
            }
            if visible {
                return Step::Advanced(accesses);
            }
        }
    }

    /// Note what this statement touches, before executing it.
    fn record_access(
        &self,
        _g: &GlobalState,
        stmt: &Stmt,
        frame: &Frame,
        out: &mut Vec<Access>,
    ) {
        match stmt {
            Stmt::PutField { obj, field, .. } => {
                if let Some(Val::Ref(r)) = self.eval(frame, obj) {
                    out.push(Access::Field {
                        obj: ObjId(r),
                        name: field.name.clone(),
                        write: true,
                    });
                }
            }
            Stmt::PutStatic(fk, _) => out.push(Access::Static {
                class: fk.class.clone(),
                name: fk.name.clone(),
                write: true,
            }),
            Stmt::MonitorEnter(o) | Stmt::MonitorExit(o) => {
                if let Some(Val::Ref(r)) = self.eval(frame, o) {
                    out.push(Access::Monitor(ObjId(r)));
                }
            }
            Stmt::Assign(_, Rvalue::GetField { obj, field }) => {
                if let Some(Val::Ref(r)) = self.eval(frame, obj) {
                    out.push(Access::Field {
                        obj: ObjId(r),
                        name: field.name.clone(),
                        write: false,
                    });
                }
            }
            Stmt::Assign(_, Rvalue::GetStatic(fk)) => out.push(Access::Static {
                class: fk.class.clone(),
                name: fk.name.clone(),
                write: false,
            }),
            // A lock or atomic operation touches shared state and must be
            // visible to the dependency relation, or DPOR will happily commute
            // two updates to the same counter.
            Stmt::Assign(_, Rvalue::Call { target, args, .. })
                if target.class == "java/util/concurrent/locks/ReentrantLock" =>
            {
                if let Some(Val::Ref(r)) = args.first().and_then(|a| self.eval(frame, a)) {
                    out.push(Access::Monitor(ObjId(r)));
                }
            }
            Stmt::Assign(_, Rvalue::Call { target, args, .. })
                if target.class.starts_with("java/util/concurrent/atomic/") =>
            {
                if let Some(Val::Ref(r)) = args.first().and_then(|a| self.eval(frame, a)) {
                    out.push(Access::Field {
                        obj: ObjId(r),
                        name: "$value".to_string(),
                        // Conservatively a write: `get` alone commutes, but
                        // treating a read as a write only over-approximates the
                        // dependency, which costs exploration, never soundness.
                        write: true,
                    });
                }
            }
            // A synchronizer operation reads and writes state shared by every
            // party, so it must be dependent with every other operation on the
            // same object or DPOR would commute a countDown past an await.
            Stmt::Assign(_, Rvalue::Call { target, args, .. })
                if matches!(
                    target.class.as_str(),
                    "java/util/concurrent/CountDownLatch"
                        | "java/util/concurrent/Semaphore"
                        | "java/util/concurrent/CyclicBarrier"
                ) =>
            {
                if let Some(Val::Ref(r)) = args.first().and_then(|a| self.eval(frame, a)) {
                    out.push(Access::Field {
                        obj: ObjId(r),
                        name: "$sync".to_string(),
                        write: true,
                    });
                }
            }
            Stmt::Assign(_, Rvalue::Call { target, args, .. })
                if target.class == "java/lang/Thread" =>
            {
                if let Some(Val::Ref(r)) = args.first().and_then(|a| self.eval(frame, a)) {
                    if let Some(&t) = self.thread_objs.get(&r) {
                        out.push(Access::Lifecycle(t));
                    }
                }
            }
            _ => {}
        }
    }

    fn run_stmt(
        &mut self,
        g: &mut GlobalState,
        tid: ThreadId,
        stmt: &Stmt,
        frame: &Frame,
    ) -> Result<Option<Step>, String> {
        let ti = g.threads.iter().position(|t| t.id == tid).unwrap();
        match stmt {
            Stmt::Assign(v, rv) => {
                let before = self.stepped_over;
                let val = self.eval_rvalue(g, tid, rv, frame)?;
                let stepped_over = self.stepped_over > before;
                let from_tainted = rvalue_operands(rv)
                    .iter()
                    .any(|o| matches!(o, Operand::Var(x) if self.is_tainted(tid, *x)));
                if let Some(f) = self.frames[tid.0 as usize].last_mut() {
                    // A call pushed a frame; the assignment happens on return.
                    if f.at == frame.at {
                        if let Some(val) = val {
                            f.locals.insert(*v, val);
                        } else if stepped_over {
                            // An unmodelled call. Give the destination a value
                            // so the interleaving can finish -- DPOR needs
                            // maximal interleavings -- but mark it, so nothing
                            // downstream may be reported as a violation on the
                            // strength of a number we invented.
                            let placeholder = if ret_is_reference(rv) {
                                Val::Ref(0)
                            } else {
                                Val::Int(0)
                            };
                            f.locals.insert(*v, placeholder);
                        }
                    }
                }
                if stepped_over || from_tainted {
                    self.mark_tainted(tid, *v);
                } else {
                    self.clear_tainted(tid, *v);
                }
                Ok(None)
            }
            Stmt::PutField { obj, field, val } => {
                let o = self
                    .eval(frame, obj)
                    .ok_or_else(|| format!("unknown operand in putfield {field:?}"))?;
                let v = self
                    .eval(frame, val)
                    .ok_or_else(|| "unknown value in putfield".to_string())?;
                let Val::Ref(r) = o else {
                    return Err("putfield on a non-reference".into());
                };
                g.heap.insert(
                    (ObjId(r), field.name.clone()),
                    (matches!(v, Val::Ref(_)), v.as_int()),
                );
                Ok(None)
            }
            Stmt::PutStatic(fk, val) => {
                let v = self
                    .eval(frame, val)
                    .ok_or_else(|| "unknown value in putstatic".to_string())?;
                g.statics.insert(
                    (fk.class.clone(), fk.name.clone()),
                    (matches!(v, Val::Ref(_)), v.as_int()),
                );
                Ok(None)
            }
            Stmt::MonitorEnter(obj) => {
                let Some(Val::Ref(r)) = self.eval(frame, obj) else {
                    return Err("monitorenter on a non-reference".into());
                };
                let m = ObjId(r);
                match g.monitor_owner.get(&m) {
                    Some(&owner) if owner != tid => {
                        g.threads[ti].status = ThreadStatus::Blocked { monitor: m };
                        // Do NOT advance past the monitorenter: the thread
                        // must retry it once the monitor frees.
                        return Ok(Some(Step::Blocked(Some(m))));
                    }
                    _ => {
                        g.monitor_owner.insert(m, tid);
                        // Acquiring clears `Blocked`. A thread that reaches
                        // here after being blocked now *owns* the monitor, and
                        // leaving the status set makes `runnable()` treat it as
                        // still waiting on a monitor it holds — the state then
                        // looks deadlocked with nobody actually stuck.
                        //
                        // Only reachable once a thread can be blocked and later
                        // acquire, which is what `wait` releasing the monitor
                        // made routine.
                        g.threads[ti].status = ThreadStatus::Runnable;
                        g.threads[ti].enter(m);
                    }
                }
                Ok(None)
            }
            Stmt::MonitorExit(obj) => {
                let Some(Val::Ref(r)) = self.eval(frame, obj) else {
                    return Err("monitorexit on a non-reference".into());
                };
                let m = ObjId(r);
                if g.threads[ti].exit(m) {
                    g.monitor_owner.remove(&m);
                    // Threads blocked on this monitor become runnable again.
                    for t in g.threads.iter_mut() {
                        if t.status == (ThreadStatus::Blocked { monitor: m }) {
                            t.status = ThreadStatus::Runnable;
                        }
                    }
                }
                Ok(None)
            }
            Stmt::Assume(op) => {
                let v = self
                    .eval(frame, op)
                    .ok_or_else(|| "unknown operand in assume".to_string())?;
                if !v.nonzero() {
                    // Assumption failed: this execution is uninteresting.
                    g.threads[ti].status = ThreadStatus::Terminated;
                    return Ok(Some(Step::Terminated));
                }
                Ok(None)
            }
            Stmt::Check(oid) => {
                let body = self.prog.body(&frame.at.method).unwrap();
                let ob = body.obligation(*oid);
                // Never report a violation that rests on an invented value.
                if matches!(&ob.cond, Operand::Var(x) if self.is_tainted(tid, *x)) {
                    return Ok(None);
                }
                let holds = match &ob.cond {
                    Operand::Const(Const::Int(v)) => *v != 0,
                    other => self
                        .eval(frame, other)
                        .ok_or_else(|| "unknown operand in check".to_string())?
                        .nonzero(),
                };
                if holds {
                    Ok(None)
                } else {
                    Ok(Some(Step::Violated(*oid, frame.at.method.clone())))
                }
            }
            Stmt::Nop => Ok(None),
            other => Err(format!("unsupported statement {other:?}")),
        }
    }

    fn eval_rvalue(
        &mut self,
        g: &mut GlobalState,
        tid: ThreadId,
        rv: &Rvalue,
        frame: &Frame,
    ) -> Result<Option<Val>, String> {
        Ok(Some(match rv {
            Rvalue::Use(o) => self
                .eval(frame, o)
                .ok_or_else(|| format!("unknown operand {o:?}"))?,
            Rvalue::New(_) => {
                let id = self.next_obj;
                self.next_obj += 1;
                Val::Ref(id)
            }
            Rvalue::Bin(op, a, b) => {
                let (x, y) = (
                    self.eval(frame, a).ok_or("unknown lhs")?.as_int(),
                    self.eval(frame, b).ok_or("unknown rhs")?.as_int(),
                );
                Val::Int(match op {
                    BinOp::Add => x.wrapping_add(y),
                    BinOp::Sub => x.wrapping_sub(y),
                    BinOp::Mul => x.wrapping_mul(y),
                    BinOp::Div if y != 0 => x / y,
                    BinOp::Rem if y != 0 => x % y,
                    BinOp::Div | BinOp::Rem => return Err("division by zero".into()),
                    BinOp::And => x & y,
                    BinOp::Or => x | y,
                    BinOp::Xor => x ^ y,
                    BinOp::Eq => (x == y) as i64,
                    BinOp::Ne => (x != y) as i64,
                    BinOp::Lt => (x < y) as i64,
                    BinOp::Le => (x <= y) as i64,
                    BinOp::Gt => (x > y) as i64,
                    BinOp::Ge => (x >= y) as i64,
                    other => return Err(format!("unsupported binop {other:?}")),
                })
            }
            Rvalue::GetField { obj, field } => {
                let Some(Val::Ref(r)) = self.eval(frame, obj) else {
                    return Err("getfield on a non-reference".into());
                };
                // Unset fields read as their Java default: 0 for a primitive,
                // null for a reference. A reference-typed default must come
                // back as `Ref(0)` so a null check on it behaves correctly.
                match g.heap.get(&(ObjId(r), field.name.clone())) {
                    Some(&(true, v)) => Val::Ref(v as u32),
                    Some(&(false, v)) => Val::Int(v),
                    None => {
                        if field.desc.starts_with('L') || field.desc.starts_with('[') {
                            Val::Ref(0)
                        } else {
                            Val::Int(0)
                        }
                    }
                }
            }
            Rvalue::GetStatic(fk) => {
                match g.statics.get(&(fk.class.clone(), fk.name.clone())) {
                    Some(&(true, v)) => Val::Ref(v as u32),
                    Some(&(false, v)) => Val::Int(v),
                    None => {
                        if fk.desc.starts_with('L') || fk.desc.starts_with('[') {
                            Val::Ref(0)
                        } else {
                            Val::Int(0)
                        }
                    }
                }
            }
            Rvalue::Call { target, args, .. } => {
                let before = self.stepped_over;
                if let Some(v) = self.do_call(g, tid, target, args, frame)? {
                    // A modelled library call that produced a value.
                    return Ok(Some(v));
                }
                if self.stepped_over > before {
                    // Stepped over an unmodelled call: the destination must not
                    // keep whatever it held before, or a later read sees a stale
                    // value and proceeds on it. Returning `None` here leaves it
                    // unset, and `eval` declines on an unset local.
                    return Ok(None);
                }
                return Ok(None);
            }
            other => return Err(format!("unsupported rvalue {other:?}")),
        }))
    }

    /// Enter a callee by pushing a frame, or model it if there is no body.
    fn do_call(
        &mut self,
        g: &mut GlobalState,
        tid: ThreadId,
        target: &MethodKey,
        args: &[Operand],
        frame: &Frame,
    ) -> Result<Option<Val>, String> {
        // Thread lifecycle is handled by the explorer, not here.
        if target.class == "java/lang/Thread" {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) => r,
                _ => return Err("Thread call on a non-reference receiver".into()),
            };
            let ti = g.threads.iter().position(|t| t.id == tid).unwrap();
            return match target.name.as_str() {
                "<init>" => {
                    // Assign this Thread object the next ThreadId, in
                    // construction order.
                    if !self.thread_objs.contains_key(&recv) {
                        let t = ThreadId(self.next_tid);
                        self.thread_objs.insert(recv, t);
                        self.next_tid += 1;
                        // Record the Runnable argument, if there is one, so the
                        // worker runs against the same object main allocated.
                        if let Some(Val::Ref(r)) = args.get(1).and_then(|a| self.eval(frame, a)) {
                            self.runnable_objs.insert(t, r);
                        } else {
                            // `new Thread()` on a subclass: the receiver *is*
                            // the Runnable.
                            self.runnable_objs.insert(t, recv);
                        }
                    }
                    Ok(None)
                }
                "start" => {
                    let Some(&target_tid) = self.thread_objs.get(&recv) else {
                        return Err("start() on an unrecognised Thread object".into());
                    };
                    if let Some(t) = g.threads.iter_mut().find(|t| t.id == target_tid) {
                        // Only now does the thread become schedulable. Before
                        // this it is NotStarted, so no interleaving can run
                        // its body early.
                        if t.status == ThreadStatus::NotStarted {
                            t.status = ThreadStatus::Runnable;
                            // Bind the worker's `this` to the real object.
                            if let Some(&obj) = self.runnable_objs.get(&target_tid) {
                                if let Some(f) =
                                    self.frames[target_tid.0 as usize].last_mut()
                                {
                                    if let Some(body) = self.prog.body(&f.at.method) {
                                        if let Some((idx, _)) =
                                            body.vars.iter().enumerate().find(|(_, vi)| {
                                                matches!(vi.kind, ajave_ir::VarKind::Local(0))
                                            })
                                        {
                                            f.locals.insert(VarId(idx as u32), Val::Ref(obj));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Ok(None)
                }
                "join" => {
                    let Some(&target_tid) = self.thread_objs.get(&recv) else {
                        return Err("join() on an unrecognised Thread object".into());
                    };
                    let done = g
                        .threads
                        .iter()
                        .find(|t| t.id == target_tid)
                        .map(|t| t.status == ThreadStatus::Terminated)
                        .unwrap_or(true);
                    if !done {
                        // Block the joiner. This is the happens-before edge
                        // join() creates; without it the joiner could observe
                        // state from before the thread ran.
                        g.threads[ti].status = ThreadStatus::Joining { on: target_tid };
                    }
                    Ok(None)
                }
                other => Err(format!("unmodelled Thread.{other}")),
            };
        }
        // java.util.concurrent.locks.ReentrantLock.
        //
        // A ReentrantLock is a monitor with a different spelling: the same
        // owner map, the same reentrancy, the same blocking. Modelling it on
        // that machinery rather than a parallel one means DPOR's dependency
        // relation (`Access::Monitor`) already covers it.
        //
        // Not modelled: fairness, lockInterruptibly, newCondition, and the
        // timed tryLock. Those fall through and are refused, which is why the
        // class stays in UNMODELLED_PRIMITIVES for anything but these members.
        // Invariant for every modelled call below: do not touch the frame's
        // program counter. `advance` steps past the statement afterwards unless
        // the call parked the thread, which it detects from the thread status.
        //
        // Advancing here breaks both directions. `Stmt::Assign` stores a
        // returned value only while the frame has not moved, so a model that
        // advanced first silently dropped its own result (`tryLock`'s boolean,
        // `incrementAndGet`'s count) and the next read of it failed as an
        // unknown operand; and a model that parked and advanced sent the thread
        // past the very call it was blocked on.
        if target.class == "java/util/concurrent/locks/ReentrantLock" {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                _ => return Err("unresolved ReentrantLock receiver".into()),
            };
            let ti = tid.0 as usize;
            match target.name.as_str() {
                "<init>" => {
                    return Ok(None);
                }
                "lock" => {
                    match g.monitor_owner.get(&recv) {
                        Some(&owner) if owner != tid => {
                            g.threads[ti].status = ThreadStatus::Blocked { monitor: recv };
                            // Do not advance: retry once the lock frees.
                            return Ok(None);
                        }
                        _ => {
                            g.monitor_owner.insert(recv, tid);
                            g.threads[ti].status = ThreadStatus::Runnable;
                            g.threads[ti].enter(recv);
                            return Ok(None);
                        }
                    }
                }
                "unlock" => {
                    if !g.threads[ti].holds(recv) {
                        return Err("unlock() without holding the lock".into());
                    }
                    if g.threads[ti].exit(recv) {
                        g.monitor_owner.remove(&recv);
                        for t in g.threads.iter_mut() {
                            if t.status == (ThreadStatus::Blocked { monitor: recv }) {
                                t.status = ThreadStatus::Runnable;
                            }
                        }
                    }
                    return Ok(None);
                }
                "tryLock" if target.desc == "()Z" => {
                    // Never blocks: reports whether it got the lock.
                    let got = match g.monitor_owner.get(&recv) {
                        Some(&owner) => owner == tid,
                        None => true,
                    };
                    if got {
                        g.monitor_owner.insert(recv, tid);
                        g.threads[ti].enter(recv);
                    }
                    return Ok(Some(Val::Int(got as i64)));
                }
                "isLocked" => {
                    let locked = g.monitor_owner.contains_key(&recv);
                    return Ok(Some(Val::Int(locked as i64)));
                }
                _ => return Err(format!("unmodelled ReentrantLock.{}", target.name)),
            }
        }

        // java.util.concurrent.atomic.Atomic{Integer,Long,Boolean}.
        //
        // The value lives in a synthetic `$value` field so it shares the heap
        // and the dependency relation with ordinary fields; DPOR then sees two
        // atomic updates conflict exactly as two field writes do.
        //
        // Each operation is one transition, which is the whole point: a
        // read-modify-write that cannot be interleaved is what makes
        // `incrementAndGet` race-free where `n++` is not. The explorer's step
        // granularity gives that for free, since the call is a single statement.
        if matches!(
            target.class.as_str(),
            "java/util/concurrent/atomic/AtomicInteger"
                | "java/util/concurrent/atomic/AtomicLong"
                | "java/util/concurrent/atomic/AtomicBoolean"
        ) {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                _ => return Err("unresolved atomic receiver".into()),
            };
            let key = (recv, "$value".to_string());
            let cur = g.heap.get(&key).map(|&(_, v)| v).unwrap_or(0);
            let arg = |i: usize| -> Option<i64> {
                args.get(i).and_then(|a| self.eval(frame, a)).map(|v| match v {
                    Val::Int(n) => n,
                    Val::Ref(r) => r as i64,
                })
            };
            let (result, new) = match target.name.as_str() {
                "<init>" => (None, Some(arg(1).unwrap_or(0))),
                "get" | "intValue" | "longValue" => (Some(cur), None),
                "set" | "lazySet" => (None, Some(arg(1).ok_or("atomic set arg")?)),
                "incrementAndGet" => (Some(cur + 1), Some(cur + 1)),
                "decrementAndGet" => (Some(cur - 1), Some(cur - 1)),
                "getAndIncrement" => (Some(cur), Some(cur + 1)),
                "getAndDecrement" => (Some(cur), Some(cur - 1)),
                "addAndGet" => {
                    let d = arg(1).ok_or("atomic addAndGet arg")?;
                    (Some(cur + d), Some(cur + d))
                }
                "getAndAdd" => {
                    let d = arg(1).ok_or("atomic getAndAdd arg")?;
                    (Some(cur), Some(cur + d))
                }
                "getAndSet" => (Some(cur), Some(arg(1).ok_or("atomic getAndSet arg")?)),
                "compareAndSet" | "weakCompareAndSet" | "compareAndExchange" => {
                    let expect = arg(1).ok_or("atomic cas expected")?;
                    let update = arg(2).ok_or("atomic cas update")?;
                    if cur == expect {
                        (Some(1), Some(update))
                    } else {
                        (Some(0), None)
                    }
                }
                other => return Err(format!("unmodelled atomic.{other}")),
            };
            if let Some(v) = new {
                g.heap.insert(key, (false, v));
            }
            return Ok(result.map(Val::Int));
        }

        // Object.wait / notify / notifyAll.
        //
        // `wait` is not a call that can be stepped over: it releases the
        // monitor and parks the thread until someone signals. Stepping over it
        // makes a thread that waits forever appear to terminate, which reports
        // a hanging program as deadlock-free.
        if target.class == "java/lang/Object"
            && matches!(target.name.as_str(), "wait" | "notify" | "notifyAll")
        {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                // A null or untracked receiver: decline rather than guess. The
                // NPE is the lifter's precondition check, not ours.
                _ => return Err(format!("unresolved receiver for Object.{}", target.name)),
            };
            let ti = tid.0 as usize;
            match target.name.as_str() {
                "wait" => {
                    // Two phases at the same statement, because the thread
                    // stays parked on the `wait()` call while it is waiting.
                    //
                    // Phase 2 first: `wait_depth > 0` means this thread already
                    // waited here and has been notified, so it is resuming.
                    if g.threads[ti].wait_depth > 0 {
                        // Reacquire the monitor before continuing. A woken
                        // thread does not hold it -- `notify` does not transfer
                        // ownership, it only moves the waiter to the entry set
                        // -- and it must reacquire *every* level it released
                        // (JLS 17.2.1). Restoring one would silently drop the
                        // outer locks of a reentrant wait.
                        if g.monitor_owner.get(&recv).is_some_and(|&o| o != tid) {
                            g.threads[ti].status = ThreadStatus::Blocked { monitor: recv };
                            return Ok(None);
                        }
                        let depth = g.threads[ti].wait_depth;
                        g.monitor_owner.insert(recv, tid);
                        for _ in 0..depth {
                            g.threads[ti].enter(recv);
                        }
                        g.threads[ti].wait_depth = 0;
                        g.threads[ti].status = ThreadStatus::Runnable;
                        // Now step past the call, so the caller's loop
                        // re-tests its condition -- which is exactly why a wait
                        // must be written as `while (!cond) wait();`.
                        return Ok(None);
                    }

                    // Phase 1: park. `wait` releases the monitor *entirely*, so
                    // a notifier can enter the guarded region at all.
                    if !g.threads[ti].holds(recv) {
                        return Err("wait() without owning the monitor".into());
                    }
                    let depth = g.threads[ti].monitors.iter().filter(|&&m| m == recv).count();
                    g.threads[ti].monitors.retain(|&m| m != recv);
                    g.monitor_owner.remove(&recv);
                    g.threads[ti].wait_depth = depth;
                    g.threads[ti].status = ThreadStatus::Waiting { monitor: recv };
                    // Deliberately not advanced: the thread resumes on this
                    // same statement and takes phase 2.
                    return Ok(None);
                }
                // A signal with no waiter is *lost*, not remembered — which is
                // the whole of the missed-signal bug. Woken threads go to
                // `Blocked`, not `Runnable`: they must reacquire the monitor,
                // which the notifier still holds until it leaves the block.
                "notify" | "notifyAll" => {
                    let all = target.name == "notifyAll";
                    for t in g.threads.iter_mut() {
                        if t.status == (ThreadStatus::Waiting { monitor: recv }) {
                            t.status = ThreadStatus::Blocked { monitor: recv };
                            if !all {
                                break;
                            }
                        }
                    }
                    return Ok(None);
                }
                _ => unreachable!(),
            }
        }

        // java.util.concurrent synchronizers: CountDownLatch, Semaphore,
        // CyclicBarrier.
        //
        // All three park on `ThreadStatus::Waiting`, which `runnable()` never
        // makes runnable on its own, so a party that is never released leaves
        // the state with no runnable thread and unterminated threads -- exactly
        // `is_deadlocked()`. The missing countDown, the exhausted permit and
        // the absent third party are therefore all found by the existing
        // deadlock check rather than by anything specific to these classes.
        //
        // Parking does not advance the program counter, so a released thread
        // re-executes the same call and re-tests its condition. That makes
        // `await` and `acquire` naturally idempotent under wake-ups and is why
        // only the barrier needs extra state (below).
        //
        // The wait sets are shared with `Object.wait` but stay distinct because
        // a `wait()` parks with `wait_depth >= 1` (the monitor levels it must
        // restore) and these park with 0. Waking only `wait_depth == 0` threads
        // means `synchronized (latch) { latch.wait(); }` cannot be woken by a
        // `countDown`.
        if matches!(
            target.class.as_str(),
            "java/util/concurrent/CountDownLatch"
                | "java/util/concurrent/Semaphore"
                | "java/util/concurrent/CyclicBarrier"
        ) {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                _ => return Err("unresolved synchronizer receiver".into()),
            };
            let ti = tid.0 as usize;
            let arg = |i: usize| -> Option<i64> {
                args.get(i).and_then(|a| self.eval(frame, a)).map(|v| match v {
                    Val::Int(n) => n,
                    Val::Ref(r) => r as i64,
                })
            };
            let get = |g: &GlobalState, f: &str| -> i64 {
                g.heap.get(&(recv, f.to_string())).map(|&(_, v)| v).unwrap_or(0)
            };
            let set = |g: &mut GlobalState, f: &str, v: i64| {
                g.heap.insert((recv, f.to_string()), (false, v));
            };
            // Release every thread parked on this object by a synchronizer.
            let wake_all = |g: &mut GlobalState| {
                for t in g.threads.iter_mut() {
                    if t.status == (ThreadStatus::Waiting { monitor: recv }) && t.wait_depth == 0 {
                        t.status = ThreadStatus::Runnable;
                    }
                }
            };
            let park = |g: &mut GlobalState| {
                g.threads[ti].status = ThreadStatus::Waiting { monitor: recv };
            };

            match (target.class.as_str(), target.name.as_str()) {
                ("java/util/concurrent/CountDownLatch", "<init>") => {
                    let n = arg(1).ok_or("latch count")?;
                    if n < 0 {
                        return Err("negative latch count".into());
                    }
                    set(g, "$count", n);
                    return Ok(None);
                }
                ("java/util/concurrent/CountDownLatch", "countDown") => {
                    let c = get(g, "$count");
                    if c > 0 {
                        set(g, "$count", c - 1);
                        if c - 1 == 0 {
                            wake_all(g);
                        }
                    }
                    return Ok(None);
                }
                ("java/util/concurrent/CountDownLatch", "await") => {
                    // Only the untimed form. `await(long, TimeUnit)` can return
                    // false on timeout, which is a behaviour we cannot decide.
                    if target.desc != "()V" {
                        return Err("unmodelled timed CountDownLatch.await".into());
                    }
                    if get(g, "$count") == 0 {
                        return Ok(None);
                    }
                    park(g);
                    return Ok(None);
                }
                ("java/util/concurrent/CountDownLatch", "getCount") => {
                    return Ok(Some(Val::Int(get(g, "$count"))));
                }

                ("java/util/concurrent/Semaphore", "<init>") => {
                    set(g, "$permits", arg(1).ok_or("semaphore permits")?);
                    return Ok(None);
                }
                ("java/util/concurrent/Semaphore", "acquire")
                | ("java/util/concurrent/Semaphore", "acquireUninterruptibly") => {
                    let want = if target.desc.starts_with("(I)") {
                        arg(1).ok_or("semaphore acquire count")?
                    } else {
                        1
                    };
                    let have = get(g, "$permits");
                    if have >= want {
                        set(g, "$permits", have - want);
                        return Ok(None);
                    }
                    park(g);
                    return Ok(None);
                }
                ("java/util/concurrent/Semaphore", "release") => {
                    let n = if target.desc.starts_with("(I)") {
                        arg(1).ok_or("semaphore release count")?
                    } else {
                        1
                    };
                    set(g, "$permits", get(g, "$permits") + n);
                    wake_all(g);
                    return Ok(None);
                }
                ("java/util/concurrent/Semaphore", "tryAcquire") if target.desc == "()Z" => {
                    let have = get(g, "$permits");
                    if have >= 1 {
                        set(g, "$permits", have - 1);
                        return Ok(Some(Val::Int(1)));
                    }
                    return Ok(Some(Val::Int(0)));
                }
                ("java/util/concurrent/Semaphore", "availablePermits") => {
                    return Ok(Some(Val::Int(get(g, "$permits"))));
                }

                ("java/util/concurrent/CyclicBarrier", "<init>") => {
                    // `CyclicBarrier(int, Runnable)` runs a barrier action on
                    // the tripping thread. Executing it means pushing a frame
                    // from inside a model, which this does not do, so refuse.
                    if target.desc != "(I)V" {
                        return Err("unmodelled CyclicBarrier barrier action".into());
                    }
                    let n = arg(1).ok_or("barrier parties")?;
                    if n <= 0 {
                        return Err("non-positive barrier parties".into());
                    }
                    set(g, "$parties", n);
                    set(g, "$arrived", 0);
                    return Ok(None);
                }
                ("java/util/concurrent/CyclicBarrier", "await") => {
                    if target.desc != "()I" {
                        return Err("unmodelled timed CyclicBarrier.await".into());
                    }
                    // The barrier is the one synchronizer whose wait is not
                    // idempotent: re-running `await` after release would count
                    // the thread as arriving a second time. A per-thread
                    // release flag marks "you already arrived and the barrier
                    // tripped", which is the generation counter in miniature.
                    let flag = format!("$released_{}", ti);
                    if get(g, &flag) == 1 {
                        set(g, &flag, 0);
                        let idx = get(g, &format!("$idx_{}", ti));
                        return Ok(Some(Val::Int(idx)));
                    }
                    let parties = get(g, "$parties");
                    let arrived = get(g, "$arrived") + 1;
                    // Arrival index: getParties()-1 for the first to arrive,
                    // 0 for the last (the one that trips it).
                    let idx = parties - arrived;
                    set(g, &format!("$idx_{}", ti), idx);
                    if arrived == parties {
                        set(g, "$arrived", 0);
                        for t in g.threads.iter() {
                            if t.status == (ThreadStatus::Waiting { monitor: recv })
                                && t.wait_depth == 0
                            {
                                let other = t.id.0 as usize;
                                g.heap
                                    .insert((recv, format!("$released_{}", other)), (false, 1));
                            }
                        }
                        wake_all(g);
                        return Ok(Some(Val::Int(idx)));
                    }
                    set(g, "$arrived", arrived);
                    park(g);
                    return Ok(None);
                }
                ("java/util/concurrent/CyclicBarrier", "getParties") => {
                    return Ok(Some(Val::Int(get(g, "$parties"))));
                }
                ("java/util/concurrent/CyclicBarrier", "getNumberWaiting") => {
                    return Ok(Some(Val::Int(get(g, "$arrived"))));
                }

                (c, m) => return Err(format!("unmodelled {}.{}", c.rsplit('/').next().unwrap_or(c), m)),
            }
        }

        let Some(body) = self.prog.body(target) else {
            // A library call with no body. Step over it and record that we did.
            //
            // Refusing outright ends the whole *interleaving*, and DPOR needs
            // interleavings to be maximal: its backtrack sets grow from
            // executed transitions, so a thread that never gets to run has no
            // accesses to compare and no backtrack point is ever created for
            // it. In RacyNullDeref main walked into `String.length()` before it
            // ever terminated, so the worker never reached its write to `h.s`,
            // and the race was unreachable by construction.
            //
            // The earlier objection to skipping was right but is about the
            // *destination*, not the call: leaving the result unassigned lets
            // downstream code read a stale local and proceed on garbage, which
            // can fabricate or mask a violation. So the caller clears the
            // destination — `eval` then returns `None` for it and a check on it
            // declines rather than guessing.
            //
            // Whether this costs completeness depends on what the call does.
            //
            // A `Pure` call writes nothing we track, so it cannot affect what
            // another thread observes and cannot change the schedule space.
            // Stepping over it leaves the search complete, and recording it as
            // a gap would refuse proofs for no reason: `GuardedNullDeref` is
            // correctly synchronised and provable, and returned UNKNOWN only
            // because `String.length()` had been stepped over.
            //
            // Anything else may write shared state, which does change what
            // other threads can see, so the search no longer covers every
            // behaviour and must not be reported as a proof.
            //
            // Note `Pure` means "writes nothing we track", not "cannot throw" —
            // `String.charAt` is pure and throws on a bad index. That is safe
            // here because the lifter seeds a precondition obligation *before*
            // the call, so the throw is caught by a `Check` in the IR rather
            // than by executing the callee. Stepping over the body therefore
            // loses the callee's writes, which purity rules out, and nothing
            // else.
            //
            // The judgement comes from `contract_of`, the single table the
            // codebase already derives this from -- deliberately not a sixth
            // private list, which is how issues #48 and #49 happened.
            let pure = models::contract_of(&target.class, &target.name, &target.desc)
                .map(|c| matches!(c.effect, models::Effect::Pure))
                .unwrap_or(false);
            self.stepped_over += 1;
            if !pure {
                self.skipped_calls.push(target.to_string());
            }
            return Ok(None);
        };
        if self.frames[tid.0 as usize].len() > 32 {
            return Err("call depth exceeded".into());
        }
        // Bind arguments to callee locals by **JVM slot**, not by argument
        // index. The lifter assigns VarIds in its own order, so `VarId(i)` is
        // not the i'th parameter — mapping that way silently binds parameters
        // to unrelated locals, and the resulting garbage made the explorer
        // report violations on 1-slice schedules (i.e. with no interleaving at
        // all, which was the clue). `concrete.rs` gets this right; this
        // mirrors it.
        let mut locals = HashMap::new();
        let mut slot = 0u16;
        for a in args {
            let val = self.eval(frame, a);
            if let Some((idx, vi)) = body
                .vars
                .iter()
                .enumerate()
                .find(|(_, vi)| matches!(vi.kind, ajave_ir::VarKind::Local(s) if s == slot))
            {
                if let Some(v) = val {
                    locals.insert(VarId(idx as u32), v);
                }
                slot += if vi.ty.is_wide() { 2 } else { 1 };
            } else {
                slot += 1;
            }
        }
        let _ = g;
        self.frames[tid.0 as usize].push(Frame {
            at: ProgramPoint {
                method: target.clone(),
                block: body.entry,
                index: 0,
            },
            locals,
            ret_to: None,
        });
        Ok(None)
    }

    fn run_terminator(
        &mut self,
        g: &mut GlobalState,
        tid: ThreadId,
        body: &Body,
        block: BlockId,
        frame: &Frame,
    ) -> Result<Option<Step>, String> {
        let ti = g.threads.iter().position(|t| t.id == tid).unwrap();
        let term = body.block(block).term.clone();
        let f = self.frames[tid.0 as usize].last_mut().unwrap();
        match term {
            Terminator::Goto(t) => {
                f.at.block = t;
                f.at.index = 0;
                Ok(None)
            }
            Terminator::Branch { cond, then_, else_ } => {
                let c = self
                    .eval(frame, &cond)
                    .ok_or_else(|| "unknown branch condition".to_string())?;
                let f = self.frames[tid.0 as usize].last_mut().unwrap();
                f.at.block = if c.nonzero() { then_ } else { else_ };
                f.at.index = 0;
                Ok(None)
            }
            Terminator::Return(_) => {
                self.frames[tid.0 as usize].pop();
                if self.frames[tid.0 as usize].is_empty() {
                    g.threads[ti].status = ThreadStatus::Terminated;
                    return Ok(Some(Step::Terminated));
                }
                // Returning into the caller: skip past the call statement.
                if let Some(caller) = self.frames[tid.0 as usize].last_mut() {
                    caller.at.index += 1;
                }
                Ok(None)
            }
            Terminator::Throw(_) => {
                // An explicit throw with no handler terminates the thread. The
                // obligations that matter are already `Check`s.
                g.threads[ti].status = ThreadStatus::Terminated;
                Ok(Some(Step::Terminated))
            }
            other => Err(format!("unsupported terminator {other:?}")),
        }
    }

    /// Build the initial frame for a thread entering `method`.
    pub fn initial_frame(&self, method: &MethodKey, this: Option<Val>) -> Option<Frame> {
        let body = self.prog.body(method)?;
        // `this` occupies slot 0 of an instance method; find the VarId the
        // lifter gave that slot rather than assuming VarId(0).
        let mut locals = HashMap::new();
        if let Some(v) = this {
            if let Some((idx, _)) = body
                .vars
                .iter()
                .enumerate()
                .find(|(_, vi)| matches!(vi.kind, ajave_ir::VarKind::Local(0)))
            {
                locals.insert(VarId(idx as u32), v);
            }
        }
        Some(Frame {
            at: ProgramPoint {
                method: method.clone(),
                block: body.entry,
                index: 0,
            },
            locals,
            ret_to: None,
        })
    }
}

/// A fresh thread state parked at `method`'s entry.
///
/// `started` distinguishes the main thread (already running) from a worker,
/// which stays `NotStarted` until `start()` is reached. Spawning workers
/// Runnable would let the explorer run a thread body before the program
/// starts it — inventing interleavings, which for an Under engine means
/// inventing bugs.
pub fn spawn_state(
    id: ThreadId,
    method: &MethodKey,
    prog: &Program,
    started: bool,
) -> Option<ThreadState> {
    let body = prog.body(method)?;
    Some(ThreadState {
        wait_depth: 0,
        id,
        at: ProgramPoint {
            method: method.clone(),
            block: body.entry,
            index: 0,
        },
        status: if started {
            ThreadStatus::Runnable
        } else {
            ThreadStatus::NotStarted
        },
        locals: Default::default(),
        stack: Vec::new(),
        monitors: Vec::new(),
    })
}
