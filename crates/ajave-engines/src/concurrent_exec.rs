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

use ajave_ir::FieldKey;
use crate::vclock::SyncKey;
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

/// Two accesses to one location, by different threads, unordered by
/// happens-before, at least one a write. That is the JLS 17.4.5 definition of a
/// data race verbatim -- and note it is a property of the *relation*, not of the
/// schedule: in the schedule one access is simply before the other.
#[derive(Clone, Debug)]
pub struct Race {
    pub location: String,
    pub threads: (u32, u32),
}

/// What happened when a thread was advanced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// Ran to the next visible action (or terminated); explorer may switch.
    /// Carries what the step accessed, for DPOR's dependency test.
    Advanced(Vec<Access>),
    /// The thread reached a decision the *program* does not determine, with
    /// this many alternatives. The explorer must try each.
    ///
    /// Distinct from a thread interleaving: this is nondeterminism inside one
    /// thread's step -- whether a timed wait expired, and later which write a
    /// read observes. Unlike the interleaving choice it gets no partial-order
    /// reduction, because the alternatives are not independent transitions that
    /// might commute; they are different outcomes of the same one.
    Choice(u32),
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
    /// Maximum statements one uninterrupted thread segment may run. Applied
    /// per `advance` call, and *not* carried across calls: a thread diverges
    /// within a single segment, whereas exploring many interleavings is not
    /// divergence and is bounded by `Bounds::max_states` instead.
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
    /// Class of each allocated object, for resolving a Runnable's `run()`.
    pub obj_class: HashMap<u32, String>,
    /// Threads whose interrupt flag has been set.
    pub interrupted: std::collections::HashSet<ThreadId>,
    /// Tasks submitted to each executor, for `awaitTermination`.
    pub executor_tasks: HashMap<u32, Vec<ThreadId>>,
    /// The happens-before relation of the execution being explored.
    pub hb: crate::vclock::Hb,
    /// Last write and reads per memory location, for race detection.
    #[allow(clippy::type_complexity)]
    pub last_access: HashMap<(u32, String), (Option<(u32, crate::vclock::VClock)>, Vec<(u32, crate::vclock::VClock)>)>,
    /// The first data race found, if any.
    pub race: Option<Race>,
    /// Decisions taken on this path, in the order they were needed.
    ///
    /// A tape rather than a callback because the interpreter cannot ask the
    /// explorer anything mid-statement: it signals that a decision is needed,
    /// the explorer appends one and re-runs the statement, and the second run
    /// reads it from here. The same "do not advance, re-execute" shape that
    /// parking uses.
    pub choices: Vec<u32>,
    /// How much of the tape this path has consumed.
    pub choice_at: usize,
    /// Arity of a decision that was needed and not yet on the tape.
    pub pending_choice: Option<u32>,
    /// Spurious events used on this path, against `Bounds::max_spurious`.
    pub spurious_used: u32,
    pub max_spurious: u32,
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
            obj_class: HashMap::new(),
            interrupted: std::collections::HashSet::new(),
            executor_tasks: HashMap::new(),
            hb: Default::default(),
            last_access: HashMap::new(),
            race: None,
            choices: Vec::new(),
            choice_at: 0,
            pending_choice: None,
            spurious_used: 0,
            max_spurious: 2,
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
        let mut budget = self.steps_left;
        loop {
            if budget == 0 {
                return Step::Unsupported(
                    "a thread ran too long without a visible action".into(),
                );
            }
            budget -= 1;

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
                // Deliberately not advancing: the thread re-executes the call
                // it was parked on, exactly as a released `lock()` or `await()`
                // does. Advancing here instead skipped the call, which is
                // harmless for a void `join()` but silently dropped the result
                // of `Future.get()` -- the very value the joiner was waiting
                // for. Re-executing is idempotent: each of these calls tests
                // "is the target finished" and simply proceeds when it is.
            }

            let Some(frame) = self.frames[tid.0 as usize].last().cloned() else {
                // A terminating thread publishes everything it did, so a later
                // join() or Future.get() inherits it.
                self.hb.release(tid.0, SyncKey::Thread(tid.0));
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
            self.record_access(g, tid, &stmt, &frame, &mut accesses);
            match self.run_stmt(g, tid, &stmt, &frame) {
                Ok(Some(step)) => return step,
                Ok(None) => {}
                Err(why) => {
                    // A decision needed from deep inside expression evaluation
                    // unwinds as an error, because `eval` has no way to say
                    // "ask the explorer". It is not a failure: the statement is
                    // retried once a decision exists, exactly as for a model
                    // that requests one directly.
                    if let Some(n) = self.pending_choice.take() {
                        return Step::Choice(n);
                    }
                    return Step::Unsupported(why);
                }
            }
            // A decision the program does not determine: same contract as
            // parking -- the statement is retried, not stepped past, once the
            // explorer has chosen.
            if let Some(n) = self.pending_choice.take() {
                return Step::Choice(n);
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
                    // `join` parks the same way, and is covered here for the
                    // same reason: it sets `Joining` and leaves the counter
                    // alone, expecting the prologue above to step past the call
                    // once the target finishes. Advancing here as well made
                    // that two advances for one statement, silently skipping
                    // whatever followed the join.
                    ThreadStatus::Joining { .. } => return Step::Blocked(None),
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

    /// Does a `catch` of `caught` catch a thrown `thrown`?
    ///
    /// `None` is the catch-all the compiler emits for `finally`. Otherwise the
    /// thrown class must be the caught one or a subclass, walked through the
    /// hierarchy the lifter recorded.
    ///
    /// Returns `None` when the relation cannot be decided -- a class outside
    /// the analysed program, whose superclass chain we do not have. Neither
    /// answer is safe there: catching when we should not continues an execution
    /// that cannot happen, and failing to catch kills a thread that would have
    /// recovered. So the caller stops instead of guessing.
    fn handler_catches(&self, caught: &Option<String>, thrown: &str) -> Option<bool> {
        let Some(caught) = caught else { return Some(true) };
        let mut cur = thrown.to_string();
        loop {
            if &cur == caught {
                return Some(true);
            }
            // The roots: reaching one without a match means no match.
            if cur == "java/lang/Object" {
                return Some(false);
            }
            match self.prog.supers.get(&cur) {
                Some(next) => cur = next.clone(),
                None => {
                    // Outside the program. The JDK exception hierarchy we rely
                    // on is small and fixed, so it is known rather than guessed.
                    return jdk_exception_super(&cur).map(|sup| {
                        let mut c = sup.to_string();
                        loop {
                            if &c == caught {
                                return true;
                            }
                            match jdk_exception_super(&c) {
                                Some(n) => c = n.to_string(),
                                None => return false,
                            }
                        }
                    });
                }
            }
        }
    }

    /// Raise `class` in `tid`, transferring to a handler if one covers the
    /// current program point.
    ///
    /// Walks outward through the frame stack exactly as the JVM does: a frame
    /// with no matching handler is popped and the search continues in its
    /// caller. Running out of frames terminates the thread, which is what an
    /// uncaught exception in a `run()` does -- it kills that thread and no
    /// other.
    fn raise(&mut self, g: &mut GlobalState, tid: ThreadId, class: &str) -> Result<Step, String> {
        self.raise_from(g, tid, class, None)
    }

    /// As `raise`, but remembering the obligation that produced the exception.
    ///
    /// A `guarded` obligation is one whose exception *could* be caught here,
    /// and `synchronized` makes that true of everything inside it: javac wraps
    /// the block in a catch-all that releases the monitor. But a `finally`
    /// does not catch, it rethrows -- so the exception still escapes and the
    /// property is still violated. Reporting the violation only when nothing
    /// actually handles it is what distinguishes the two, and it is why this
    /// carries the obligation all the way out.
    fn raise_from(
        &mut self,
        g: &mut GlobalState,
        tid: ThreadId,
        class: &str,
        from: Option<(ObligationId, MethodKey)>,
    ) -> Result<Step, String> {
        let ti = tid.0 as usize;
        loop {
            let Some(frame) = self.frames[ti].last().cloned() else {
                self.hb.release(tid.0, SyncKey::Thread(tid.0));
                if let Some(t) = g.threads.iter_mut().find(|t| t.id == tid) {
                    t.status = ThreadStatus::Terminated;
                }
                // Escaped every frame: nothing handled it after all.
                if let Some((oid, method)) = from {
                    return Ok(Step::Violated(oid, method));
                }
                return Ok(Step::Terminated);
            };
            let Some(body) = self.prog.body(&frame.at.method) else {
                return Err(format!("no body for {}", frame.at.method));
            };
            let block = body.block(frame.at.block);
            let mut target = None;
            for edge in &block.exceptional {
                match self.handler_catches(&edge.class, class) {
                    Some(true) => {
                        target = Some(edge.target);
                        break;
                    }
                    Some(false) => continue,
                    None => {
                        return Err(format!(
                            "cannot tell whether a handler catches {class}"
                        ))
                    }
                }
            }
            if let Some(t) = target {
                // The handler expects the exception object on entry. A fresh
                // object of the thrown class is enough: the benchmarks that
                // matter read its type, not its fields.
                let id = self.next_obj;
                self.next_obj += 1;
                self.obj_class.insert(id, class.to_string());
                if let Some(f) = self.frames[ti].last_mut() {
                    f.at.block = t;
                    f.at.index = 0;
                    if let Some(b) = self.prog.body(&f.at.method) {
                        if let Some((idx, _)) = b
                            .vars
                            .iter()
                            .enumerate()
                            .find(|(_, vi)| matches!(vi.kind, ajave_ir::VarKind::Local(0)))
                        {
                            let _ = idx;
                        }
                    }
                    // The lifter's handler blocks read the caught value from
                    // whatever the first statement assigns; binding it by name
                    // is not possible here, so the object is published through
                    // the frame's scratch slot.
                    f.locals.insert(VarId(0), Val::Ref(id));
                }
                return Ok(Step::Advanced(Vec::new()));
            }
            // No handler here: unwind.
            self.frames[ti].pop();
        }
    }

    /// Take the next decision from the tape, or ask for one.
    ///
    /// `None` means "the explorer has not decided yet": the caller must leave
    /// the program counter alone and return, and will be re-run once a decision
    /// exists. Callers must therefore make the same sequence of `choose` calls
    /// on the re-run, which holds for a deterministic model.
    /// Offer a spurious alternative, if this path has budget for one.
    ///
    /// Returns `Some(true)` for "behave spuriously", `Some(false)` for "behave
    /// normally", and `None` when a decision is pending. Once the budget is
    /// spent the answer is simply "normally", so the search terminates.
    fn choose_spurious(&mut self) -> Option<bool> {
        if self.spurious_used >= self.max_spurious {
            return Some(false);
        }
        match self.choose(2) {
            None => None,
            Some(0) => {
                self.spurious_used += 1;
                Some(true)
            }
            _ => Some(false),
        }
    }

    fn choose(&mut self, alternatives: u32) -> Option<u32> {
        if self.choice_at < self.choices.len() {
            let v = self.choices[self.choice_at];
            self.choice_at += 1;
            return Some(v);
        }
        self.pending_choice = Some(alternatives);
        None
    }

    /// Note a memory access, and report a race if this one is unordered with a
    /// conflicting earlier access.
    ///
    /// A *volatile* access is skipped: it is a synchronising action, cannot
    /// take part in a race by definition (JLS 17.4.1), and instead contributes
    /// a happens-before edge here.
    fn note_access(&mut self, tid: u32, obj: u32, field: &FieldKey, write: bool) {
        log::trace!("access t{tid} obj{obj} {}.{} write={write}", field.class, field.name);
        if self.prog.volatile_fields.contains(field) {
            if write {
                self.hb.release(tid, SyncKey::Volatile(obj, field.name.clone()));
            } else {
                self.hb.acquire(tid, SyncKey::Volatile(obj, field.name.clone()));
            }
            return;
        }
        let clock = self.hb.clock(tid);
        let key = (obj, field.name.clone());
        let entry = self.last_access.entry(key).or_insert((None, Vec::new()));

        // A race needs a conflicting pair, so a read only conflicts with the
        // last write, while a write conflicts with the last write *and* every
        // read that is not yet ordered before it.
        if let Some((wt, wc)) = &entry.0 {
            if *wt != tid && !wc.happens_before(&clock) && self.race.is_none() {
                log::debug!(
                    "race: {}.{} prev-write t{wt} {:?} vs t{tid} {:?}",
                    field.class, field.name, wc, clock
                );
                self.race = Some(Race {
                    location: format!("{}.{}", field.class, field.name),
                    threads: (*wt, tid),
                });
            }
        }
        if write {
            for (rt, rc) in &entry.1 {
                if *rt != tid && !rc.happens_before(&clock) && self.race.is_none() {
                    self.race = Some(Race {
                        location: format!("{}.{}", field.class, field.name),
                        threads: (*rt, tid),
                    });
                }
            }
            entry.0 = Some((tid, clock));
            entry.1.clear();
        } else {
            entry.1.retain(|(rt, _)| *rt != tid);
            entry.1.push((tid, clock));
        }
    }

    fn record_access(
        &mut self,
        _g: &GlobalState,
        tid: ThreadId,
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
                    self.note_access(tid.0, r, field, true);
                }
            }
            Stmt::PutStatic(fk, _) => {
                out.push(Access::Static {
                    class: fk.class.clone(),
                    name: fk.name.clone(),
                    write: true,
                });
                // Statics have no receiver; object 0 is the class-level cell.
                self.note_access(tid.0, 0, fk, true);
            }
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
                    self.note_access(tid.0, r, field, false);
                }
            }
            Stmt::Assign(_, Rvalue::GetStatic(fk)) => {
                out.push(Access::Static {
                    class: fk.class.clone(),
                    name: fk.name.clone(),
                    write: false,
                });
                self.note_access(tid.0, 0, fk, false);
            }
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
                        | "java/util/concurrent/locks/Condition"
                        | "java/util/concurrent/ArrayBlockingQueue"
                        | "java/util/concurrent/LinkedBlockingQueue"
                        | "java/util/concurrent/BlockingQueue"
                        | "java/util/concurrent/LinkedBlockingDeque"
                ) || target
                    .class
                    .starts_with("java/util/concurrent/locks/ReentrantReadWriteLock") =>
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
                // Reference 0 is null, and is also what an untracked object
                // reads as. Locking it would make every such monitor the *same*
                // monitor, which can both invent and hide a deadlock. This is
                // the guard that makes concrete monitor identity safe enough to
                // have replaced the static allocation-site ambiguity check.
                if r == 0 {
                    return Err("monitorenter on a null or untracked reference".into());
                }
                let m = ObjId(r);
                match g.monitor_owner.get(&m) {
                    Some(&owner) if owner != tid => {
                        g.threads[ti].status = ThreadStatus::Blocked { monitor: m };
                        // Do NOT advance past the monitorenter: the thread
                        // must retry it once the monitor frees.
                        return Ok(Some(Step::Blocked(Some(m))));
                    }
                    _ => {
                        // Acquire: absorb whatever the last releaser of this
                        // monitor knew (JLS 17.4.4). This is what orders a
                        // guarded write before a later guarded read.
                        self.hb.acquire(tid.0, SyncKey::Monitor(m.0));
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
                // Release: publish what this thread knows to the monitor, so
                // the next acquirer inherits it. Only on the outermost exit --
                // a reentrant exit does not release the monitor and so
                // synchronises with nobody.
                if g.threads[ti].exit(m) {
                    self.hb.release(tid.0, SyncKey::Monitor(m.0));
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
                    return Ok(None);
                }
                // A *guarded* obligation is one whose exception a handler in
                // this method catches, so it is not a property violation --
                // the program recovers. It is also not a no-op: the exception
                // really is raised, and control goes to the handler rather than
                // continuing as though the check had passed.
                //
                // Ignoring the flag reported `throw new RuntimeException()`
                // inside a try/catch as a violation, in a program that catches
                // it and carries on.
                // `guarded` says an exception raised here *could* be caught in
                // this method, but it is computed from the exception edges and
                // so cannot tell a `catch` from a `finally`. Only `finally`
                // emits a class-less edge, and a finally does not handle
                // anything -- it runs its cleanup and rethrows -- so an
                // obligation covered by nothing else still escapes and is still
                // a violation.
                //
                // That distinction matters everywhere, because `synchronized`
                // compiles to try/finally: treating its catch-all as a handler
                // silently swallowed every assertion failure inside a
                // synchronized block. `SpuriousWakeupBreaksIfGuard` is the
                // benchmark.
                let typed_handler = self
                    .prog
                    .body(&frame.at.method)
                    .map(|b| b.block(frame.at.block))
                    .map(|blk| {
                        blk.exceptional.iter().any(|e| {
                            e.class.is_some()
                                && ajave_models::exception_class(ob.kind)
                                    .and_then(|c| self.handler_catches(&e.class, c))
                                    .unwrap_or(false)
                        })
                    })
                    .unwrap_or(false);
                if ob.guarded && typed_handler {
                    let class = ajave_models::exception_class(ob.kind)
                        .unwrap_or("java/lang/RuntimeException");
                    let step = self.raise_from(
                        g,
                        tid,
                        class,
                        Some((*oid, frame.at.method.clone())),
                    )?;
                    return Ok(Some(step));
                }
                Ok(Some(Step::Violated(*oid, frame.at.method.clone())))
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
            // A nondeterministic input.
            //
            // `Verifier.nondetBoolean()` has exactly two values, so branching
            // over both is *complete*: it supports a TRUE as well as a FALSE.
            // The descriptor byte the lifter kept (`b'Z'`) is what makes that
            // distinguishable from an int.
            //
            // Every wider type is deliberately left unsupported rather than
            // sampled. Trying a handful of values would find some violations,
            // but the exploration could no longer claim to have covered the
            // input space, and picking which values to try from the program's
            // own constants is the benchmark-fitting CLAUDE.md forbids. Those
            // belong to the solving engines, which is what #63 tracks.
            Rvalue::Nondet(_, Some(b'Z')) => {
                let Some(c) = self.choose(2) else {
                    return Err("$choice".into());
                };
                Val::Int(c as i64)
            }
            Rvalue::New(class) => {
                let id = self.next_obj;
                self.next_obj += 1;
                // Remember the class: `start()` resolves a thread's body from
                // the class of the Runnable it was actually given.
                self.obj_class.insert(id, class.clone());
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
            // Static members first: they have no receiver, so `args[0]` is an
            // argument and reading it as one is how `Thread.sleep(50)` came out
            // as "a call on a non-reference receiver".
            match target.name.as_str() {
                // `sleep` deliberately does nothing.
                //
                // It establishes no happens-before edge -- the JLS gives it no
                // memory-model meaning at all -- so modelling it as ordering
                // would let the explorer prove programs safe that are not.
                // `SleepIsNotSynchronization` is the case: a real JVM nearly
                // always makes it pass, and it is still a race.
                //
                // Doing nothing is also not a lost scheduling opportunity: the
                // explorer already considers a switch at every visible action,
                // so sleeping cannot enable an interleaving it would otherwise
                // miss.
                "sleep" | "yield" | "onSpinWait" => return Ok(None),
                "currentThread" => {
                    // The Thread object for the running thread, if one was
                    // constructed. Main has no Thread object in this model.
                    let obj = self
                        .thread_objs
                        .iter()
                        .find(|(_, &t)| t == tid)
                        .map(|(&o, _)| o);
                    return match obj {
                        Some(o) => Ok(Some(Val::Ref(o))),
                        None => Err("currentThread() on a thread with no Thread object".into()),
                    };
                }
                _ => {}
            }
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
                "isAlive" => {
                    let Some(&t) = self.thread_objs.get(&recv) else {
                        return Err("isAlive() on an unrecognised Thread object".into());
                    };
                    // Alive means started and not yet finished. A thread that
                    // has not been started is not alive either.
                    let alive = g
                        .threads
                        .iter()
                        .find(|x| x.id == t)
                        .map(|x| {
                            !matches!(
                                x.status,
                                ThreadStatus::Terminated | ThreadStatus::NotStarted
                            )
                        })
                        .unwrap_or(false);
                    return Ok(Some(Val::Int(alive as i64)));
                }
                "interrupt" => {
                    let Some(&t) = self.thread_objs.get(&recv) else {
                        return Err("interrupt() on an unrecognised Thread object".into());
                    };
                    self.interrupted.insert(t);
                    // Wake a thread parked in an interruptible wait so it
                    // re-runs the call and observes the flag, which raises.
                    //
                    // The flag alone is not enough, and getting that wrong was
                    // a wrong FALSE rather than a missing feature: the refusal
                    // this replaces only fired when the target was *already*
                    // parked, so interrupting before it parked set a flag the
                    // subsequent wait ignored, and the thread hung forever in a
                    // program the JVM completes. `InterruptWakesParkedThread`
                    // is the benchmark.
                    if let Some(x) = g.threads.iter_mut().find(|x| x.id == t) {
                        if matches!(x.status, ThreadStatus::Waiting { .. }) {
                            x.status = ThreadStatus::Runnable;
                            x.timed_wait = false;
                        }
                    }
                    return Ok(None);
                }
                "isInterrupted" => {
                    let Some(&t) = self.thread_objs.get(&recv) else {
                        return Err("isInterrupted() on an unrecognised Thread object".into());
                    };
                    return Ok(Some(Val::Int(self.interrupted.contains(&t) as i64)));
                }
                "start" => {
                    let Some(&target_tid) = self.thread_objs.get(&recv) else {
                        return Err("start() on an unrecognised Thread object".into());
                    };
                    // A start() we cannot carry out must not be ignored. When
                    // thread discovery under-counted threads this branch found
                    // no state for the identity and fell through silently, so
                    // the thread simply never ran and the explorer reported no
                    // deadlock for `DiningPhilosophers`, whose cycle needs all
                    // three. Silence on an unmodelled start is a wrong TRUE.
                    if !g.threads.iter().any(|t| t.id == target_tid) {
                        return Err(format!("start() on thread {} with no state", target_tid.0));
                    }
                    let obj = self.runnable_objs.get(&target_tid).copied();
                    // Bind the body from the Runnable *object*, not from the
                    // thread's position in the entry list. Entries are sorted
                    // for determinism while identities are assigned in
                    // construction order, so the two lists need not correspond
                    // -- pairing them by index gave a thread another thread's
                    // body whenever those orders differed.
                    if let Some(o) = obj {
                        if let Some(cls) = self.obj_class.get(&o).cloned() {
                            let run = MethodKey {
                                class: cls,
                                name: "run".to_string(),
                                desc: "()V".to_string(),
                            };
                            if self.prog.body(&run).is_some() {
                                match self.initial_frame(&run, Some(Val::Ref(o))) {
                                    Some(f) => {
                                        self.frames[target_tid.0 as usize] = vec![f];
                                        if let Some(t) =
                                            g.threads.iter_mut().find(|t| t.id == target_tid)
                                        {
                                            t.at = ProgramPoint {
                                                method: run.clone(),
                                                block: self.prog.body(&run).unwrap().entry,
                                                index: 0,
                                            };
                                        }
                                    }
                                    None => return Err(format!("no frame for {run}")),
                                }
                            }
                        }
                    }
                    self.hb.fork(tid.0, target_tid.0);
                    if let Some(t) = g.threads.iter_mut().find(|t| t.id == target_tid) {
                        // Only now does the thread become schedulable. Before
                        // this it is NotStarted, so no interleaving can run
                        // its body early.
                        if t.status == ThreadStatus::NotStarted {
                            // Everything the starter has done happens-before
                            // the started thread's first action (JLS 17.4.5).
                            t.status = ThreadStatus::Runnable;
                            // Bind the worker's `this` to the real object.
                            if let Some(o) = obj {
                                if let Some(f) = self.frames[target_tid.0 as usize].last_mut() {
                                    if let Some(body) = self.prog.body(&f.at.method) {
                                        if let Some((idx, _)) =
                                            body.vars.iter().enumerate().find(|(_, vi)| {
                                                matches!(vi.kind, ajave_ir::VarKind::Local(0))
                                            })
                                        {
                                            f.locals.insert(VarId(idx as u32), Val::Ref(o));
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
                    } else {
                        self.hb.acquire(tid.0, SyncKey::Thread(target_tid.0));
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
                            self.hb.acquire(tid.0, SyncKey::Monitor(recv.0));
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
                        self.hb.release(tid.0, SyncKey::Monitor(recv.0));
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
                "newCondition" => {
                    // A fresh object per call, matching the JDK: two calls give
                    // two independent wait sets. It remembers its lock in
                    // `$lock`, because `await` has to release and reacquire
                    // that lock while parking on the condition itself.
                    let id = self.next_obj;
                    self.next_obj += 1;
                    g.heap.insert((ObjId(id), "$lock".to_string()), (false, recv.0 as i64));
                    return Ok(Some(Val::Ref(id)));
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
                | "java/util/concurrent/atomic/AtomicReference"
        ) {
            // A reference cell shares all of this machinery -- the value is
            // just an ObjId rather than a number -- but its results must come
            // back as references. Handing an `Int` to code that compares it
            // against an object would silently compare the wrong kind of value.
            let is_ref = target.class == "java/util/concurrent/atomic/AtomicReference";
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
                "compareAndSet" | "compareAndExchange" => {
                    let expect = arg(1).ok_or("atomic cas expected")?;
                    let update = arg(2).ok_or("atomic cas update")?;
                    if cur == expect {
                        (Some(1), Some(update))
                    } else {
                        (Some(0), None)
                    }
                }
                // `weakCompareAndSet` is documented to fail spuriously: it may
                // report false even when the witness value matches. That is
                // what makes it cheaper than `compareAndSet`, and why its
                // contract says it must be used in a retry loop. Modelling it
                // as an exact CAS reports code that uses it once as correct.
                "weakCompareAndSet" | "weakCompareAndSetPlain"
                | "weakCompareAndSetAcquire" | "weakCompareAndSetRelease" => {
                    let expect = arg(1).ok_or("atomic cas expected")?;
                    let update = arg(2).ok_or("atomic cas update")?;
                    if cur != expect {
                        (Some(0), None)
                    } else {
                        match self.choose_spurious() {
                            None => return Ok(None),
                            Some(true) => (Some(0), None),
                            Some(false) => (Some(1), Some(update)),
                        }
                    }
                }
                // The arithmetic members do not exist on AtomicReference and
                // fall through to here, which is what we want.
                other => return Err(format!("unmodelled atomic.{other}")),
            };
            if let Some(v) = new {
                g.heap.insert(key, (false, v));
            }
            if is_ref {
                // `compareAndSet` still reports a boolean, not a reference.
                let boolean = matches!(
                    target.name.as_str(),
                    "compareAndSet" | "weakCompareAndSet"
                );
                return Ok(result.map(|v| {
                    if boolean {
                        Val::Int(v)
                    } else {
                        Val::Ref(v as u32)
                    }
                }));
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
                    // Interruption is checked first, at both phases: a thread
                    // interrupted before it parks must not park, and one
                    // interrupted while parked must throw rather than resume
                    // normally. The monitor is reacquired before throwing,
                    // exactly as a normal return from wait would (JLS 17.2.1).
                    if self.interrupted.remove(&tid) {
                        let depth = g.threads[ti].wait_depth;
                        if depth > 0 {
                            if g.monitor_owner.get(&recv).is_some_and(|&o| o != tid) {
                                self.interrupted.insert(tid);
                                g.threads[ti].status = ThreadStatus::Blocked { monitor: recv };
                                return Ok(None);
                            }
                            self.hb.acquire(tid.0, SyncKey::Monitor(recv.0));
                            g.monitor_owner.insert(recv, tid);
                            for _ in 0..depth {
                                g.threads[ti].enter(recv);
                            }
                            g.threads[ti].wait_depth = 0;
                        }
                        g.threads[ti].status = ThreadStatus::Runnable;
                        g.threads[ti].timed_wait = false;
                        // `raise` has already moved the program counter to the
                        // handler (or unwound the thread), so returning
                        // normally is correct: `advance` only steps past a
                        // statement whose frame did not move.
                        self.raise(g, tid, "java/lang/InterruptedException")?;
                        return Ok(None);
                    }
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
                        self.hb.acquire(tid.0, SyncKey::Monitor(recv.0));
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

                    // Phase 1: park -- or not.
                    //
                    // JLS 17.2.1 permits `wait` to return with no notify, no
                    // interrupt and no timeout: a *spurious wakeup*. It is not
                    // a rare implementation quirk to be ignored but the reason
                    // the specification requires a wait to sit inside a loop
                    // re-testing its condition, and a program guarding with
                    // `if` instead of `while` is incorrect because of it.
                    //
                    // Modelling it as a choice both finds that bug and keeps
                    // the loop-guarded version provable: the spurious branch
                    // re-tests and waits again. Refusing to model it reports
                    // `if`-guarded waits safe, which is a wrong TRUE against
                    // the language, however reliably a given JVM behaves.
                    if !g.threads[ti].holds(recv) {
                        return Err("wait() without owning the monitor".into());
                    }
                    match self.choose_spurious() {
                        // Woke spuriously: the monitor was never released, so
                        // there is nothing to reacquire. Fall through the call.
                        Some(true) => return Ok(None),
                        None => return Ok(None),
                        Some(false) => {}
                    }
                    let depth = g.threads[ti].monitors.iter().filter(|&&m| m == recv).count();
                    // Parking in wait() releases the monitor for real, so it
                    // publishes like any other release. `notify` itself needs
                    // no edge: the ordering comes from the notifier leaving the
                    // synchronized block, which is an ordinary monitor release.
                    self.hb.release(tid.0, SyncKey::Monitor(recv.0));
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
                    let waiters: Vec<ThreadId> = g
                        .threads
                        .iter()
                        .filter(|t| t.status == (ThreadStatus::Waiting { monitor: recv }))
                        .map(|t| t.id)
                        .collect();
                    if all {
                        for t in g.threads.iter_mut() {
                            if t.status == (ThreadStatus::Waiting { monitor: recv }) {
                                t.status = ThreadStatus::Blocked { monitor: recv };
                            }
                        }
                        return Ok(None);
                    }
                    // `notify` wakes exactly one waiter and the JLS does not
                    // say which. Waking a fixed one -- the first, as this did
                    // -- makes the verdict depend on the interpreter's
                    // iteration order rather than on the program: a signal that
                    // reaches the wrong waiter is spent, and the thread that
                    // needed it is stranded. That is the whole reason to prefer
                    // notifyAll, and `NotifyMayWakeWrongWaiter` is built on it.
                    //
                    // Chosen before anything is mutated, so re-running the call
                    // after the explorer decides is safe.
                    let chosen = match waiters.len() {
                        0 => return Ok(None),
                        1 => waiters[0],
                        n => match self.choose(n as u32) {
                            None => return Ok(None),
                            Some(i) => waiters[i as usize],
                        },
                    };
                    if let Some(t) = g.threads.iter_mut().find(|t| t.id == chosen) {
                        t.status = ThreadStatus::Blocked { monitor: recv };
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
            // Arguments are evaluated eagerly rather than through a closure
            // over `self`: the happens-before edges below need `&mut self`, and
            // a closure holding an immutable borrow of it would outlive them.
            let argv: Vec<Option<i64>> = args
                .iter()
                .map(|a| {
                    self.eval(frame, a).map(|v| match v {
                        Val::Int(n) => n,
                        Val::Ref(r) => r as i64,
                    })
                })
                .collect();
            let arg = |i: usize| -> Option<i64> { argv.get(i).copied().flatten() };
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
                        t.timed_wait = false;
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
                    self.hb.release(tid.0, SyncKey::Sync(recv.0));
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
                    // Timed form: the timeout may or may not expire, and the
                    // program does not decide which -- so it is a choice, not a
                    // computation. Both outcomes occur on a real JVM.
                    //
                    // Expiry is only offered while the latch is still up. Once
                    // the count reaches zero `await` returns true without
                    // consulting the clock, so a timeout branch there would
                    // invent a false the JVM cannot produce.
                    if target.desc != "()V" {
                        if get(g, "$count") == 0 {
                            self.hb.acquire(tid.0, SyncKey::Sync(recv.0));
                            return Ok(Some(Val::Int(1)));
                        }
                        let Some(c) = self.choose(2) else {
                            return Ok(None);
                        };
                        if c == 0 {
                            // Timed out: returns false, holding no ordering.
                            return Ok(Some(Val::Int(0)));
                        }
                        // Otherwise wait as the untimed form does, but flagged:
                        // this thread's timeout will fire, so a state holding it
                        // is not a deadlock even when nothing else can run.
                        park(g);
                        g.threads[ti].timed_wait = true;
                        return Ok(None);
                    }
                    if get(g, "$count") == 0 {
                        self.hb.acquire(tid.0, SyncKey::Sync(recv.0));
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
                        self.hb.acquire(tid.0, SyncKey::Sync(recv.0));
                        set(g, "$permits", have - want);
                        return Ok(None);
                    }
                    park(g);
                    return Ok(None);
                }
                ("java/util/concurrent/Semaphore", "release") => {
                    self.hb.release(tid.0, SyncKey::Sync(recv.0));
                    let n = if target.desc.starts_with("(I)") {
                        arg(1).ok_or("semaphore release count")?
                    } else {
                        1
                    };
                    set(g, "$permits", get(g, "$permits") + n);
                    wake_all(g);
                    return Ok(None);
                }
                // Timed tryAcquire: the timeout may expire before a permit is
                // released, and only the deadline decides which. Offered only
                // when no permit is free -- with one available the call returns
                // true without waiting.
                ("java/util/concurrent/Semaphore", "tryAcquire")
                    if target.desc.starts_with("(JL") =>
                {
                    let have = get(g, "$permits");
                    if have >= 1 {
                        self.hb.acquire(tid.0, SyncKey::Sync(recv.0));
                        set(g, "$permits", have - 1);
                        return Ok(Some(Val::Int(1)));
                    }
                    let Some(c) = self.choose(2) else { return Ok(None) };
                    if c == 0 {
                        return Ok(Some(Val::Int(0)));
                    }
                    park(g);
                    g.threads[ti].timed_wait = true;
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
                    // A timed await that expires does not merely return: it
                    // *breaks* the barrier, so every other party waiting on it
                    // fails too. Modelling expiry without that would release
                    // one thread and leave the rest waiting on a barrier that
                    // can never trip -- a deadlock the JVM does not have.
                    if target.desc != "()I" {
                        let Some(c) = self.choose(2) else { return Ok(None) };
                        if c == 0 {
                            set(g, "$broken", 1);
                            for t in g.threads.iter_mut() {
                                if t.status == (ThreadStatus::Waiting { monitor: recv })
                                    && t.wait_depth == 0
                                {
                                    t.status = ThreadStatus::Runnable;
                                    t.timed_wait = false;
                                }
                            }
                            self.raise(g, tid, "java/util/concurrent/BrokenBarrierException")?;
                            return Ok(None);
                        }
                    }
                    // A party arriving at an already-broken barrier fails
                    // immediately rather than waiting for a trip that cannot
                    // happen.
                    if get(g, "$broken") == 1 {
                        self.raise(g, tid, "java/util/concurrent/BrokenBarrierException")?;
                        return Ok(None);
                    }
                    // The barrier is the one synchronizer whose wait is not
                    // idempotent: re-running `await` after release would count
                    // the thread as arriving a second time. A per-thread
                    // release flag marks "you already arrived and the barrier
                    // tripped", which is the generation counter in miniature.
                    let flag = format!("$released_{}", ti);
                    self.hb.release(tid.0, SyncKey::Sync(recv.0));
                    self.hb.acquire(tid.0, SyncKey::Sync(recv.0));
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

        // java.util.concurrent.locks.Condition.
        //
        // Structurally this is `Object.wait`/`notify` with the wait set and the
        // lock separated: a thread parks on the *condition* but releases and
        // reacquires the *lock* the condition was created from. That is why the
        // condition object stores its lock in `$lock` -- `Waiting { monitor }`
        // carries one object, and here the two differ.
        //
        // Signals are not remembered. A `signal` with no waiter is lost, which
        // is the whole of the missed-signal bug and the reason a condition wait
        // is written `while (!cond) await();`.
        if target.class == "java/util/concurrent/locks/Condition" {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                _ => return Err("unresolved Condition receiver".into()),
            };
            let ti = tid.0 as usize;
            let lock = match g.heap.get(&(recv, "$lock".to_string())) {
                Some(&(_, l)) if l != 0 => ObjId(l as u32),
                _ => return Err("Condition with no owning lock".into()),
            };
            match target.name.as_str() {
                "await" => {
                    if target.desc != "()V" {
                        return Err("unmodelled timed Condition.await".into());
                    }
                    // Phase 2: already waited here and has been signalled.
                    // Reacquire every level of the lock that was released
                    // (JLS 17.2.1 for monitors; Condition.await is specified to
                    // restore the hold count identically).
                    if g.threads[ti].wait_depth > 0 {
                        if g.monitor_owner.get(&lock).is_some_and(|&o| o != tid) {
                            g.threads[ti].status = ThreadStatus::Blocked { monitor: lock };
                            return Ok(None);
                        }
                        let depth = g.threads[ti].wait_depth;
                        self.hb.acquire(tid.0, SyncKey::Monitor(lock.0));
                        g.monitor_owner.insert(lock, tid);
                        for _ in 0..depth {
                            g.threads[ti].enter(lock);
                        }
                        g.threads[ti].wait_depth = 0;
                        g.threads[ti].status = ThreadStatus::Runnable;
                        return Ok(None);
                    }
                    // Phase 1: release the lock entirely and park.
                    if !g.threads[ti].holds(lock) {
                        return Err("Condition.await without holding the lock".into());
                    }
                    let depth = g.threads[ti].monitors.iter().filter(|&&m| m == lock).count();
                    self.hb.release(tid.0, SyncKey::Monitor(lock.0));
                    g.threads[ti].monitors.retain(|&m| m != lock);
                    g.monitor_owner.remove(&lock);
                    g.threads[ti].wait_depth = depth;
                    g.threads[ti].status = ThreadStatus::Waiting { monitor: recv };
                    return Ok(None);
                }
                "signal" | "signalAll" => {
                    // Woken threads go to `Blocked` on the lock, not
                    // `Runnable`: the signaller still holds it until it leaves
                    // the guarded region.
                    //
                    // `signal` picks one waiter arbitrarily, exactly as
                    // `Object.notify` does, and for the same reason: a signal
                    // delivered to a waiter whose condition is still false is
                    // spent, stranding the one that needed it.
                    let all = target.name == "signalAll";
                    let waiters: Vec<ThreadId> = g
                        .threads
                        .iter()
                        .filter(|t| {
                            t.status == (ThreadStatus::Waiting { monitor: recv })
                                && t.wait_depth > 0
                        })
                        .map(|t| t.id)
                        .collect();
                    if all {
                        for t in g.threads.iter_mut() {
                            if waiters.contains(&t.id) {
                                t.status = ThreadStatus::Blocked { monitor: lock };
                            }
                        }
                        return Ok(None);
                    }
                    let chosen = match waiters.len() {
                        0 => return Ok(None),
                        1 => waiters[0],
                        n => match self.choose(n as u32) {
                            None => return Ok(None),
                            Some(i) => waiters[i as usize],
                        },
                    };
                    if let Some(t) = g.threads.iter_mut().find(|t| t.id == chosen) {
                        t.status = ThreadStatus::Blocked { monitor: lock };
                    }
                    return Ok(None);
                }
                other => return Err(format!("unmodelled Condition.{other}")),
            }
        }

        // Executors, thread pools and Futures.
        //
        // A submitted task is a thread whose `start()` happens inside the
        // library, so it reuses the thread machinery: an identity from the same
        // counter, a body resolved from the class of the Runnable actually
        // passed, and `Future.get`/`awaitTermination` as join edges.
        //
        // Pool size is a soundness condition, not a detail. A pool with fewer
        // workers than tasks runs some of them one after another, and treating
        // every task as concurrently runnable would invent interleavings the
        // JVM cannot produce -- a wrong FALSE. Rather than model the work
        // queue, a pool that could not run all its tasks at once is refused.
        if target.class == "java/util/concurrent/Executors" {
            let n = match target.name.as_str() {
                "newFixedThreadPool" | "newWorkStealingPool" => {
                    match args.first().and_then(|a| self.eval(frame, a)) {
                        Some(Val::Int(n)) if n > 0 => n,
                        _ => return Err("thread pool size is not a known positive int".into()),
                    }
                }
                "newSingleThreadExecutor" | "newSingleThreadScheduledExecutor" => 1,
                "newCachedThreadPool" => i64::MAX,
                other => return Err(format!("unmodelled Executors.{other}")),
            };
            let id = self.next_obj;
            self.next_obj += 1;
            self.obj_class
                .insert(id, "java/util/concurrent/ExecutorService".to_string());
            g.heap.insert((ObjId(id), "$workers".to_string()), (false, n));
            g.heap.insert((ObjId(id), "$submitted".to_string()), (false, 0));
            return Ok(Some(Val::Ref(id)));
        }

        if crate::threads::is_executor(&target.class) {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                _ => return Err("unresolved executor receiver".into()),
            };
            let ti = tid.0 as usize;
            match target.name.as_str() {
                "execute" | "submit" => {
                    let workers = g
                        .heap
                        .get(&(recv, "$workers".to_string()))
                        .map(|&(_, v)| v)
                        .unwrap_or(0);
                    let submitted = g
                        .heap
                        .get(&(recv, "$submitted".to_string()))
                        .map(|&(_, v)| v)
                        .unwrap_or(0)
                        + 1;
                    if submitted > workers {
                        return Err(format!(
                            "pool has {workers} worker(s) but {submitted} task(s): the queued \
                             ones cannot all run concurrently and the queue is not modelled"
                        ));
                    }
                    g.heap
                        .insert((recv, "$submitted".to_string()), (false, submitted));

                    let Some(Val::Ref(task)) = args.get(1).and_then(|a| self.eval(frame, a))
                    else {
                        return Err("submitted task is not a reference".into());
                    };
                    let t = ThreadId(self.next_tid);
                    self.next_tid += 1;
                    if !g.threads.iter().any(|x| x.id == t) {
                        return Err(format!("submitted task {} has no thread state", t.0));
                    }
                    let Some(cls) = self.obj_class.get(&task).cloned() else {
                        return Err("submitted task has no known class".into());
                    };
                    let run = MethodKey {
                        class: cls,
                        name: "run".to_string(),
                        desc: "()V".to_string(),
                    };
                    let Some(rbody) = self.prog.body(&run) else {
                        return Err(format!("no body for submitted task {run}"));
                    };
                    let entry_block = rbody.entry;
                    match self.initial_frame(&run, Some(Val::Ref(task))) {
                        Some(f) => self.frames[t.0 as usize] = vec![f],
                        None => return Err(format!("no frame for {run}")),
                    }
                    if let Some(st) = g.threads.iter_mut().find(|x| x.id == t) {
                        st.at = ProgramPoint { method: run, block: entry_block, index: 0 };
                        st.status = ThreadStatus::Runnable;
                    }
                    // Submitting is a fork: everything the submitter has done
                    // happens-before the task's first action. Without this the
                    // task shares no history with anyone and every value it
                    // touches looks racy -- including ones the submitter had
                    // already initialised.
                    self.hb.fork(tid.0, t.0);
                    self.executor_tasks.entry(recv.0).or_default().push(t);

                    // `submit` hands back a Future; `execute` returns nothing.
                    if target.name == "submit" {
                        let fid = self.next_obj;
                        self.next_obj += 1;
                        g.heap
                            .insert((ObjId(fid), "$thread".to_string()), (false, t.0 as i64));
                        return Ok(Some(Val::Ref(fid)));
                    }
                    return Ok(None);
                }
                // Shutting down only refuses new work; it orders nothing.
                "shutdown" | "shutdownNow" => return Ok(None),
                "isShutdown" | "isTerminated" => {
                    let all_done = self
                        .executor_tasks
                        .get(&recv.0)
                        .map(|ts| {
                            ts.iter().all(|t| {
                                g.threads
                                    .iter()
                                    .find(|x| x.id == *t)
                                    .map(|x| x.status == ThreadStatus::Terminated)
                                    .unwrap_or(true)
                            })
                        })
                        .unwrap_or(true);
                    return Ok(Some(Val::Int(all_done as i64)));
                }
                "awaitTermination" => {
                    // The timeout is real: it may expire with tasks still
                    // running, in which case the call reports false and the
                    // program continues *without* the ordering a completed
                    // await would have given it. Modelling it as untimed
                    // assumed the ordering always holds, which is the
                    // assumption the surrounding code is making when it ignores
                    // the returned boolean -- but not one we may make for it.
                    if let Some(ts) = self.executor_tasks.get(&recv.0) {
                        let any_running = ts.iter().any(|t| {
                            g.threads
                                .iter()
                                .find(|x| x.id == *t)
                                .map(|x| x.status != ThreadStatus::Terminated)
                                .unwrap_or(false)
                        });
                        if any_running {
                            let Some(c) = self.choose(2) else { return Ok(None) };
                            if c == 0 {
                                return Ok(Some(Val::Int(0)));
                            }
                        }
                    }
                    // Join every task in turn. Parking does not advance, so the
                    // call is re-entered until none is left running, which is
                    // how one `Joining { on }` slot covers a set of tasks.
                    //
                    // Modelled as the untimed wait it usually is in practice.
                    // A timeout that *expires* would let the program continue
                    // with tasks still running; treating that as impossible is
                    // the same assumption the surrounding code is making when
                    // it ignores the returned boolean.
                    let pending = self.executor_tasks.get(&recv.0).and_then(|ts| {
                        ts.iter()
                            .find(|t| {
                                g.threads
                                    .iter()
                                    .find(|x| x.id == **t)
                                    .map(|x| x.status != ThreadStatus::Terminated)
                                    .unwrap_or(false)
                            })
                            .copied()
                    });
                    if let Some(t) = pending {
                        g.threads[ti].status = ThreadStatus::Joining { on: t };
                        return Ok(None);
                    }
                    return Ok(Some(Val::Int(1)));
                }
                other => return Err(format!("unmodelled ExecutorService.{other}")),
            }
        }

        if target.class == "java/util/concurrent/Future" {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                _ => return Err("unresolved Future receiver".into()),
            };
            let ti = tid.0 as usize;
            let t = match g.heap.get(&(recv, "$thread".to_string())) {
                Some(&(_, v)) => ThreadId(v as u32),
                None => return Err("Future not bound to a task".into()),
            };
            match target.name.as_str() {
                "get" => {
                    // The join edge: get() returns only once the task is done,
                    // and everything the task did is visible afterwards.
                    let done = g
                        .threads
                        .iter()
                        .find(|x| x.id == t)
                        .map(|x| x.status == ThreadStatus::Terminated)
                        .unwrap_or(true);
                    if !done {
                        g.threads[ti].status = ThreadStatus::Joining { on: t };
                        return Ok(None);
                    }
                    // A Runnable task computes no value, so `get()` is null.
                    self.hb.acquire(tid.0, SyncKey::Thread(t.0));
                    return Ok(Some(Val::Ref(0)));
                }
                "isDone" => {
                    let done = g
                        .threads
                        .iter()
                        .find(|x| x.id == t)
                        .map(|x| x.status == ThreadStatus::Terminated)
                        .unwrap_or(true);
                    return Ok(Some(Val::Int(done as i64)));
                }
                "cancel" => {
                    // Only the already-finished case is exact: cancel() returns
                    // false and changes nothing. Cancelling a *running* task
                    // needs interruption to be delivered at an arbitrary point
                    // inside it, which is not the same as interrupting at a
                    // blocking call, so that stays refused.
                    let done = g
                        .threads
                        .iter()
                        .find(|x| x.id == t)
                        .map(|x| x.status == ThreadStatus::Terminated)
                        .unwrap_or(true);
                    if done {
                        return Ok(Some(Val::Int(0)));
                    }
                    return Err("cancelling a running task is not modelled".into());
                }
                other => return Err(format!("unmodelled Future.{other}")),
            }
        }

        // BlockingQueue: ArrayBlockingQueue and LinkedBlockingQueue.
        //
        // A bounded FIFO whose `put` and `take` park on the queue object, so a
        // consumer waiting on a queue nobody fills leaves no runnable thread
        // and is found by the existing deadlock check. Elements live in the
        // heap under `$e{index}` with monotonic head and tail cursors, so a
        // taken element is not overwritten by a later put and FIFO order is
        // exact rather than approximated by a count.
        //
        // Parking re-executes the call, so both operations re-test their
        // condition on wake-up and need no extra state.
        if matches!(
            target.class.as_str(),
            "java/util/concurrent/ArrayBlockingQueue"
                | "java/util/concurrent/LinkedBlockingQueue"
                | "java/util/concurrent/BlockingQueue"
                | "java/util/concurrent/LinkedBlockingDeque"
        ) {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                _ => return Err("unresolved queue receiver".into()),
            };
            let ti = tid.0 as usize;
            let get = |g: &GlobalState, f: &str| -> i64 {
                g.heap.get(&(recv, f.to_string())).map(|&(_, v)| v).unwrap_or(0)
            };
            let set = |g: &mut GlobalState, f: &str, v: i64| {
                g.heap.insert((recv, f.to_string()), (false, v));
            };
            let wake_all = |g: &mut GlobalState| {
                for t in g.threads.iter_mut() {
                    if t.status == (ThreadStatus::Waiting { monitor: recv }) && t.wait_depth == 0 {
                        t.status = ThreadStatus::Runnable;
                    }
                }
            };
            match target.name.as_str() {
                "<init>" => {
                    // Unbounded when no capacity is given. i64::MAX stands in
                    // for "never full", which is what LinkedBlockingQueue is
                    // in every program that does not exhaust memory.
                    let cap = match args.get(1).and_then(|a| self.eval(frame, a)) {
                        Some(Val::Int(n)) if n > 0 => n,
                        None => i64::MAX,
                        _ => return Err("queue capacity is not a known positive int".into()),
                    };
                    set(g, "$cap", cap);
                    set(g, "$head", 0);
                    set(g, "$tail", 0);
                    return Ok(None);
                }
                "put" | "offer" | "add" => {
                    let (head, tail, cap) = (get(g, "$head"), get(g, "$tail"), get(g, "$cap"));
                    if tail - head >= cap {
                        // `offer` reports failure rather than blocking.
                        if target.name == "offer" && target.desc.ends_with(")Z") {
                            return Ok(Some(Val::Int(0)));
                        }
                        if target.name == "add" {
                            self.raise(g, tid, "java/lang/IllegalStateException")?;
                            return Ok(None);
                        }
                        g.threads[ti].status = ThreadStatus::Waiting { monitor: recv };
                        return Ok(None);
                    }
                    let v = match args.get(1).and_then(|a| self.eval(frame, a)) {
                        Some(Val::Ref(r)) => r as i64,
                        Some(Val::Int(n)) => n,
                        None => return Err("queue element is unknown".into()),
                    };
                    set(g, &format!("$e{tail}"), v);
                    set(g, "$tail", tail + 1);
                    self.hb.release(tid.0, SyncKey::Sync(recv.0));
                    wake_all(g);
                    if target.name == "put" {
                        return Ok(None);
                    }
                    return Ok(Some(Val::Int(1)));
                }
                "take" | "poll" => {
                    let (head, tail) = (get(g, "$head"), get(g, "$tail"));
                    if head == tail {
                        // `poll` reports emptiness with null rather than
                        // blocking. Only the untimed form: a timed poll can
                        // return null after a wait we cannot decide.
                        if target.name == "poll" {
                            // Untimed: reports emptiness immediately.
                            if target.desc.starts_with("()") {
                                return Ok(Some(Val::Ref(0)));
                            }
                            // Timed: either nothing arrived before the deadline,
                            // or an element did and this behaves as `take`.
                            let Some(c) = self.choose(2) else { return Ok(None) };
                            if c == 0 {
                                return Ok(Some(Val::Ref(0)));
                            }
                            g.threads[ti].status = ThreadStatus::Waiting { monitor: recv };
                            g.threads[ti].timed_wait = true;
                            return Ok(None);
                        }
                        g.threads[ti].status = ThreadStatus::Waiting { monitor: recv };
                        return Ok(None);
                    }
                    let v = get(g, &format!("$e{head}"));
                    set(g, "$head", head + 1);
                    self.hb.acquire(tid.0, SyncKey::Sync(recv.0));
                    wake_all(g);
                    return Ok(Some(Val::Ref(v as u32)));
                }
                "size" => return Ok(Some(Val::Int(get(g, "$tail") - get(g, "$head")))),
                "isEmpty" => {
                    return Ok(Some(Val::Int((get(g, "$tail") == get(g, "$head")) as i64)))
                }
                "remainingCapacity" => {
                    return Ok(Some(Val::Int(
                        get(g, "$cap") - (get(g, "$tail") - get(g, "$head")),
                    )))
                }
                other => return Err(format!("unmodelled BlockingQueue.{other}")),
            }
        }

        // ReentrantReadWriteLock.
        //
        // `readLock()` and `writeLock()` return view objects; all the state
        // lives on the parent, keyed `$readers`, `$r{tid}` (per-thread read
        // holds, for reentrancy), `$writer` (owning tid + 1, 0 for none) and
        // `$wcount`. Views may therefore be allocated fresh per call, which is
        // what `rw.readLock().lock()` ... `rw.readLock().unlock()` needs.
        //
        // The grant rules are the whole model:
        //   read  -- no writer, or I am the writer (downgrade is allowed)
        //   write -- no readers at all, and no other writer
        //
        // "No readers at all" is what makes upgrading deadlock, without any
        // special case for it: a thread holding the read lock is itself a
        // reader, so it waits for a lock only it could release. The Javadoc is
        // explicit that upgrading is not supported, and this is why.
        //
        // Modelling the read lock as exclusive would be the tempting
        // simplification and is unsound in the expensive direction: it
        // serialises two readers and hides a real race, a wrong TRUE.
        // ReadWriteLockConcurrentReaders exists to catch exactly that.
        if target.class.starts_with("java/util/concurrent/locks/ReentrantReadWriteLock") {
            let recv = match args.first().and_then(|a| self.eval(frame, a)) {
                Some(Val::Ref(r)) if r != 0 => ObjId(r),
                _ => return Err("unresolved ReentrantReadWriteLock receiver".into()),
            };
            let ti = tid.0 as usize;
            let is_view = target.class.contains('$');
            // A view delegates to its parent; the parent is its own subject.
            let parent = if is_view {
                match g.heap.get(&(recv, "$rwlock".to_string())) {
                    Some(&(_, v)) if v != 0 => ObjId(v as u32),
                    _ => return Err("read/write lock view has no parent".into()),
                }
            } else {
                recv
            };
            let get = |g: &GlobalState, f: &str| -> i64 {
                g.heap.get(&(parent, f.to_string())).map(|&(_, v)| v).unwrap_or(0)
            };
            let set = |g: &mut GlobalState, f: &str, v: i64| {
                g.heap.insert((parent, f.to_string()), (false, v));
            };
            let wake_all = |g: &mut GlobalState| {
                for t in g.threads.iter_mut() {
                    if t.status == (ThreadStatus::Waiting { monitor: parent }) && t.wait_depth == 0
                    {
                        t.status = ThreadStatus::Runnable;
                    }
                }
            };
            let mine = tid.0 as i64 + 1;
            let my_reads = format!("$r{ti}");

            if !is_view {
                match target.name.as_str() {
                    "<init>" => return Ok(None),
                    "readLock" | "writeLock" => {
                        let id = self.next_obj;
                        self.next_obj += 1;
                        let cls = if target.name == "readLock" {
                            "java/util/concurrent/locks/ReentrantReadWriteLock$ReadLock"
                        } else {
                            "java/util/concurrent/locks/ReentrantReadWriteLock$WriteLock"
                        };
                        self.obj_class.insert(id, cls.to_string());
                        g.heap
                            .insert((ObjId(id), "$rwlock".to_string()), (false, parent.0 as i64));
                        return Ok(Some(Val::Ref(id)));
                    }
                    other => {
                        return Err(format!("unmodelled ReentrantReadWriteLock.{other}"))
                    }
                }
            }

            let writing = target.class.ends_with("$WriteLock");
            match target.name.as_str() {
                "lock" | "lockInterruptibly" => {
                    if writing {
                        let writer = get(g, "$writer");
                        if get(g, "$readers") > 0 || (writer != 0 && writer != mine) {
                            g.threads[ti].status = ThreadStatus::Waiting { monitor: parent };
                            return Ok(None);
                        }
                        // A writer is ordered after the last writer *and* after
                        // every reader that has finished.
                        self.hb.acquire(tid.0, SyncKey::Sync(parent.0));
                        self.hb
                            .acquire(tid.0, SyncKey::Volatile(parent.0, "$read".into()));
                        set(g, "$writer", mine);
                        set(g, "$wcount", get(g, "$wcount") + 1);
                        return Ok(None);
                    }
                    let writer = get(g, "$writer");
                    if writer != 0 && writer != mine {
                        g.threads[ti].status = ThreadStatus::Waiting { monitor: parent };
                        return Ok(None);
                    }
                    // A reader is ordered after the last writer only. Two
                    // readers hold the lock at once and are genuinely
                    // concurrent, so ordering them here would hide a write
                    // performed inside a read section.
                    self.hb.acquire(tid.0, SyncKey::Sync(parent.0));
                    set(g, "$readers", get(g, "$readers") + 1);
                    let n = get(g, &my_reads) + 1;
                    set(g, &my_reads, n);
                    return Ok(None);
                }
                "unlock" => {
                    if writing {
                        if get(g, "$writer") != mine {
                            return Err("write unlock without holding the write lock".into());
                        }
                        let n = get(g, "$wcount") - 1;
                        set(g, "$wcount", n);
                        if n == 0 {
                            set(g, "$writer", 0);
                            self.hb.release(tid.0, SyncKey::Sync(parent.0));
                        }
                        wake_all(g);
                        return Ok(None);
                    }
                    if get(g, &my_reads) <= 0 {
                        return Err("read unlock without holding the read lock".into());
                    }
                    set(g, &my_reads, get(g, &my_reads) - 1);
                    // Published on the reader channel, which only writers
                    // absorb -- never other readers.
                    self.hb
                        .release(tid.0, SyncKey::Volatile(parent.0, "$read".into()));
                    let r = get(g, "$readers") - 1;
                    set(g, "$readers", r);
                    if r == 0 {
                        wake_all(g);
                    }
                    return Ok(None);
                }
                "tryLock" if target.desc == "()Z" => {
                    if writing {
                        let writer = get(g, "$writer");
                        if get(g, "$readers") > 0 || (writer != 0 && writer != mine) {
                            return Ok(Some(Val::Int(0)));
                        }
                        set(g, "$writer", mine);
                        set(g, "$wcount", get(g, "$wcount") + 1);
                        return Ok(Some(Val::Int(1)));
                    }
                    let writer = get(g, "$writer");
                    if writer != 0 && writer != mine {
                        return Ok(Some(Val::Int(0)));
                    }
                    set(g, "$readers", get(g, "$readers") + 1);
                    set(g, &my_reads, get(g, &my_reads) + 1);
                    return Ok(Some(Val::Int(1)));
                }
                other => return Err(format!("unmodelled read/write lock .{other}")),
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
                    // A terminating thread publishes everything it did, so a
                    // later join() or Future.get() inherits it (JLS 17.4.5).
                    // This is where threads actually finish -- the check at the
                    // top of `advance` only catches an already-empty stack, so
                    // putting the edge there alone meant a joiner learned
                    // nothing and every joined write looked like a race.
                    self.hb.release(tid.0, SyncKey::Thread(tid.0));
                    g.threads[ti].status = ThreadStatus::Terminated;
                    return Ok(Some(Step::Terminated));
                }
                // Returning into the caller: skip past the call statement.
                if let Some(caller) = self.frames[tid.0 as usize].last_mut() {
                    caller.at.index += 1;
                }
                Ok(None)
            }
            Terminator::Throw(op) => {
                // Previously this terminated the thread outright, so a worker
                // that threw never ran its own handlers and every `try`/`catch`
                // inside a thread was invisible.
                let class = match self.eval(frame, &op) {
                    Some(Val::Ref(r)) if r != 0 => self
                        .obj_class
                        .get(&r)
                        .cloned()
                        .unwrap_or_else(|| "java/lang/RuntimeException".to_string()),
                    _ => "java/lang/RuntimeException".to_string(),
                };
                let step = self.raise(g, tid, &class)?;
                Ok(Some(step))
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
        timed_wait: false,
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

/// The JDK exception hierarchy we depend on, which is small, fixed and
/// specified — so it is known rather than guessed. Anything outside it makes
/// `handler_catches` decline rather than assume.
fn jdk_exception_super(class: &str) -> Option<&'static str> {
    Some(match class {
        "java/lang/InterruptedException" => "java/lang/Exception",
        "java/lang/IllegalStateException"
        | "java/lang/IllegalArgumentException"
        | "java/lang/NullPointerException"
        | "java/lang/ArithmeticException"
        | "java/lang/ClassCastException"
        | "java/lang/IllegalMonitorStateException"
        | "java/lang/NegativeArraySizeException"
        | "java/lang/UnsupportedOperationException"
        | "java/lang/IndexOutOfBoundsException" => "java/lang/RuntimeException",
        "java/lang/ArrayIndexOutOfBoundsException"
        | "java/lang/StringIndexOutOfBoundsException" => "java/lang/IndexOutOfBoundsException",
        "java/lang/NumberFormatException" => "java/lang/IllegalArgumentException",
        "java/util/NoSuchElementException" => "java/lang/RuntimeException",
        "java/util/concurrent/BrokenBarrierException"
        | "java/util/concurrent/TimeoutException"
        | "java/util/concurrent/ExecutionException" => "java/lang/Exception",
        "java/lang/RuntimeException" => "java/lang/Exception",
        "java/lang/Exception" | "java/lang/Error" => "java/lang/Throwable",
        "java/lang/AssertionError" => "java/lang/Error",
        "java/lang/Throwable" => "java/lang/Object",
        _ => return None,
    })
}
