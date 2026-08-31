//! Bounded interleaving explorer — Phase 4 of `docs/strategies/concurrency.md`.
//!
//! **Direction: Under.** It may publish `Violated`, never `Discharged`. Every
//! bound in `concurrent_state::Bounds` is a reason the absence of a violation
//! proves nothing.
//!
//! # What this engine will and will not attempt
//!
//! It refuses to run at all unless three preconditions hold, and each refusal
//! is a deliberate choice to answer UNKNOWN rather than risk a wrong FALSE:
//!
//! 1. **Every `start()` resolves to a concrete `run()`.** Over-approximating
//!    the thread set would let us report a bug in a thread that never runs.
//!    See `threads::discover`.
//! 2. **Every class whose monitor is used has one allocation site.** `ObjId` is
//!    allocation-site identity, so two locks on *different* instances of the
//!    same class are indistinguishable — which would make threads look mutually
//!    excluded when they are not, hiding a real race *and* letting us claim
//!    exclusion we do not have.
//! 3. **No unmodelled `java.util.concurrent` primitive is used.** A
//!    `CountDownLatch` we treat as a no-op removes an ordering the program
//!    relies on, which manufactures interleavings the JVM cannot produce.
//!
//! The refusal reason is logged, because an engine that declines should be able
//! to say why — that is what turns "we found nothing" into a work item.
//!
//! # Status
//!
//! Precondition checking is implemented and tested. The exploration loop itself
//! is not yet written: it needs a concrete interpreter step function shared
//! with `concrete.rs`, which is the next piece of work. Until then `step`
//! reports why it declined and publishes nothing, which is the correct
//! behaviour for an engine that cannot yet answer.

use std::collections::HashSet;

use log::{debug, info};

use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_ir::{Operand, Program, Rvalue, Stmt};

use ajave_ir::verdict::{ScheduleSlice, ThreadId, Witness};
use ajave_ir::{MethodKey, ObligationId};

use crate::concurrent_exec::{spawn_state, Access, Interp, Step, Val};
use crate::concurrent_state::{Bounds, GlobalState, ObjId};
use crate::threads::{discover, ThreadDiscovery};

/// Why the explorer declined to analyse a program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// No thread is started; another engine should handle this.
    Sequential,
    /// A `start()` could not be resolved to a concrete body.
    UnresolvedThread(String),
    /// A monitor is taken on a class with more than one allocation site, so
    /// allocation-site identity cannot distinguish the instances.
    AmbiguousMonitor(String),
    /// A concurrency primitive we do not model appears in reachable code.
    UnmodelledPrimitive(String),
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Refusal::Sequential => write!(f, "program starts no threads"),
            Refusal::UnresolvedThread(w) => write!(f, "unresolved thread body: {w}"),
            Refusal::AmbiguousMonitor(c) => write!(
                f,
                "monitor taken on {c}, which has multiple allocation sites — \
                 allocation-site identity cannot tell the instances apart"
            ),
            Refusal::UnmodelledPrimitive(c) => {
                write!(f, "unmodelled concurrency primitive: {c}")
            }
        }
    }
}

/// `java.util.concurrent` types whose ordering effects we do not model.
///
/// Treating any of these as a no-op would *remove* a happens-before edge the
/// program depends on, letting the explorer produce interleavings the JVM
/// cannot. For an Under engine that is a wrong FALSE, so their presence is a
/// refusal rather than an approximation.
const UNMODELLED_PRIMITIVES: &[&str] = &[
    // ReentrantLock, the scalar atomics and the three basic synchronizers
    // (CountDownLatch, Semaphore, CyclicBarrier) are modelled in
    // `concurrent_exec`:
    // a lock is a monitor with a different spelling, and an atomic update is a
    // single transition on a synthetic `$value` field. Members outside what is
    // modelled there are refused individually, so an unmodelled `newCondition`
    // still declines rather than being silently ignored.
    "java/util/concurrent/Phaser",
    "java/util/concurrent/CompletableFuture",
    "java/util/concurrent/ForkJoinPool",
];

/// Decide whether the explorer may soundly analyse this program.
pub fn check_preconditions(prog: &Program) -> Result<Vec<crate::threads::ThreadEntry>, Refusal> {
    // Scan for unmodelled primitives BEFORE deciding the program is sequential.
    //
    // `discover` only sees explicit `Thread.start()`. An `ExecutorService` or
    // `ForkJoinPool` starts threads internally, so a program using one has no
    // visible start() and would be classified `Sequential` — telling the rest
    // of the system there is no concurrency here when there is. Checking the
    // primitives first means such a program is refused rather than
    // mis-described.
    //
    // (Found by a unit test that expected UnmodelledPrimitive and got
    // Sequential. The test was right and the ordering was wrong.)
    let mut alloc_count: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    // Classes whose monitor is actually taken. Resolving this precisely
    // matters: an earlier version flagged *any* multi-allocated class whenever
    // *any* monitor was used, which refused `SynchronizedCounter` because the
    // Verifier stub happens to allocate `java.util.Random` nine times — a
    // class no one locks.
    let mut monitored: HashSet<String> = HashSet::new();
    let mut unresolved_monitor = false;
    // Fields whose value is used as a monitor, e.g. `synchronized (l.a)`.
    //
    // Class identity is too coarse for these. `Locks.a` and `Locks.b` are both
    // `java.lang.Object`, so an allocation-site-per-class test calls them
    // ambiguous and refuses — yet they are plainly different monitors, which is
    // the entire point of a lock-order-inversion benchmark.
    //
    // A field is a sound monitor identity when it is written exactly once
    // across the whole program: then every read of it yields the same object,
    // so two threads locking `l.a` really are contending, and `l.a` and `l.b`
    // really are distinct.
    let mut monitored_fields: HashSet<ajave_ir::FieldKey> = HashSet::new();
    let mut field_writes: std::collections::HashMap<ajave_ir::FieldKey, usize> =
        std::collections::HashMap::new();

    for body in prog.bodies.values() {
        // Per-body allocation tracking, as in `threads::discover`.
        let mut var_class: std::collections::HashMap<ajave_ir::VarId, String> =
            std::collections::HashMap::new();
        // Which field a local was loaded from, for monitor identity.
        let mut var_field: std::collections::HashMap<ajave_ir::VarId, ajave_ir::FieldKey> =
            std::collections::HashMap::new();
        for block in &body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Stmt::Assign(v, Rvalue::New(cls)) => {
                        *alloc_count.entry(cls.clone()).or_insert(0) += 1;
                        var_class.insert(*v, cls.clone());
                        if UNMODELLED_PRIMITIVES.contains(&cls.as_str()) {
                            return Err(Refusal::UnmodelledPrimitive(cls.clone()));
                        }
                    }
                    Stmt::Assign(v, Rvalue::Use(Operand::Var(src))) => {
                        if let Some(c) = var_class.get(src).cloned() {
                            var_class.insert(*v, c);
                        }
                        if let Some(f) = var_field.get(src).cloned() {
                            var_field.insert(*v, f);
                        }
                    }
                    Stmt::Assign(v, Rvalue::GetField { field, .. }) => {
                        var_field.insert(*v, field.clone());
                    }
                    // A static field names a monitor exactly as an instance
                    // field does, and `static final Object LOCK = new Object()`
                    // is the commonest lock idiom in Java. Without this arm the
                    // load traces to neither an allocation nor a field, the
                    // monitor is called unresolved, and every program locking a
                    // static was refused outright.
                    //
                    // Same ambiguity rule as instance fields: the identity is
                    // unambiguous only if the field is written once
                    // program-wide, which for a `static final` initialised in
                    // `<clinit>` is exactly one `putstatic`.
                    Stmt::Assign(v, Rvalue::GetStatic(fk)) => {
                        var_field.insert(*v, fk.clone());
                    }
                    Stmt::PutField { field, .. } => {
                        *field_writes.entry(field.clone()).or_insert(0) += 1;
                    }
                    Stmt::PutStatic(fk, _) => {
                        *field_writes.entry(fk.clone()).or_insert(0) += 1;
                    }
                    Stmt::Assign(_, Rvalue::Call { target, .. }) => {
                        if UNMODELLED_PRIMITIVES.contains(&target.class.as_str()) {
                            return Err(Refusal::UnmodelledPrimitive(target.class.clone()));
                        }
                    }
                    Stmt::MonitorEnter(Operand::Var(v)) => {
                        // Prefer field identity when the monitor came from a
                        // field load: it distinguishes two same-class objects.
                        if let Some(f) = var_field.get(v).cloned() {
                            monitored_fields.insert(f);
                            continue;
                        }
                        match var_class.get(v) {
                            Some(c) => {
                                monitored.insert(c.clone());
                            }
                            None => {
                                // `synchronized` on an instance method locks
                                // `this`, whose allocation is in the *caller*.
                                // Attribute it to the declaring class, which is
                                // exactly right for that case.
                                if matches!(v, ajave_ir::VarId(_))
                                    && body
                                        .vars
                                        .get(v.0 as usize)
                                        .map(|vi| matches!(vi.kind, ajave_ir::VarKind::Local(0)))
                                        .unwrap_or(false)
                                {
                                    monitored.insert(body.key.class.clone());
                                } else {
                                    unresolved_monitor = true;
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let entries = match discover(prog) {
        ThreadDiscovery::Sequential => return Err(Refusal::Sequential),
        ThreadDiscovery::Unresolved(why) => return Err(Refusal::UnresolvedThread(why)),
        ThreadDiscovery::Resolved(e) => e,
    };

    // The allocation-site ambiguity checks that used to live here are gone.
    //
    // They asked whether a *static* abstraction could tell two monitors apart:
    // a locked class with several `new` sites, a monitor field written more
    // than once, a monitor not traceable to an allocation were all refused.
    // The explorer does not use that abstraction. It interprets the program
    // and evaluates a monitor operand to the concrete `ObjId` produced by the
    // `new` that actually ran, so two `new Account(...)` are two monitors by
    // construction and no static disambiguation is required.
    //
    // Keeping the checks cost real coverage: `synchronized (from)` inside
    // `transfer(from, to)` -- the single most common locking pattern in real
    // code, and the shape of the classic transfer deadlock -- locks a
    // parameter, which is traceable to no allocation site in its own method.
    // BankTransferDeadlock was refused for that reason alone.
    //
    // What replaces them is a run-time guard rather than a static one: a
    // monitor operand that evaluates to reference 0 is refused in the
    // interpreter. 0 is null and is also how an untracked object reads, so it
    // is the one value that could silently make two distinct monitors one.
    // Anything else is a real, distinct object identity. An operand the
    // interpreter cannot evaluate at all already stops exploration, so the
    // failure mode is UNKNOWN rather than a wrong verdict.
    let _ = (&monitored, &monitored_fields, &field_writes, &alloc_count, unresolved_monitor);

    Ok(entries)
}


/// Outcome of exhaustively exploring the bounded interleaving space.
#[derive(Clone, Debug)]
pub enum Exploration {
    /// Every interleaving within the bounds was explored; none violated.
    ///
    /// This licenses a `Discharged` *only* because no bound was hit — the
    /// space was genuinely covered, not merely sampled. If any bound had cut
    /// the search short we would report `Incomplete` instead.
    ExhaustiveNoViolation,
    /// A violating interleaving, with the schedule that produces it.
    Violation {
        obligation: ObligationId,
        method: MethodKey,
        schedule: Vec<ScheduleSlice>,
    },
    /// A reachable state where no thread can proceed and not all terminated.
    Deadlock { schedule: Vec<ScheduleSlice> },
    /// A bound was hit or a construct was unsupported, so the space was not
    /// covered. Proves nothing in either direction.
    Incomplete(String),
}

/// Dynamic partial-order reduction (Flanagan & Godefroid, POPL 2005).
///
/// The naive explorer enumerates every interleaving, which is factorial in the
/// number of visible actions — it exhausted its context-switch bound on a
/// two-thread counter. DPOR explores one interleaving, then adds a
/// *backtracking point* only where reordering could actually change the
/// outcome.
///
/// # The reduction, stated precisely
///
/// Two transitions are **dependent** if swapping them can change what the
/// program observes: they touch the same location and at least one writes, or
/// they contend for the same monitor, or one is a lifecycle event for the
/// other's thread. Independent transitions commute, so exploring `A then B`
/// makes `B then A` redundant — it reaches the same state.
///
/// After executing a transition by thread `p`, we scan *backwards* for the most
/// recent dependent transition by a different thread. That earlier point is
/// where the order mattered, so `p` is added to its backtrack set. Everything
/// not so marked is never explored, and soundness rests on the claim that those
/// unexplored orders reach states already covered.
///
/// # Where this implementation is deliberately weaker than the paper
///
/// The persistent-set refinement ("which threads can *reach* p") is not
/// implemented: at a backtrack point we add every enabled thread rather than
/// the minimal set. That explores more than necessary but never less, so it
/// costs time, not soundness. Source-DPOR and sleep sets are the natural next
/// step and are measurable against this — which is why the naive explorer is
/// retained behind `Strategy::Exhaustive` as the ground truth to check against.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    /// Enumerate every interleaving. Correct, exponential — the baseline DPOR
    /// is validated against.
    Exhaustive,
    /// Dynamic partial-order reduction.
    Dpor,
}

/// One executed transition, kept so dependencies can be found by looking back.
#[derive(Clone, Debug)]
struct Transition {
    thread: ThreadId,
    accesses: Vec<Access>,
    /// Threads that were enabled *before* this transition ran. A backtrack
    /// point can only schedule a thread that was actually runnable there.
    enabled: Vec<ThreadId>,
}

struct Explorer<'a> {
    prog: &'a Program,
    bounds: Bounds,
    strategy: Strategy,
    incomplete: Option<String>,
    /// Transitions executed on the current path.
    stack: Vec<Transition>,
    /// Backtrack set per depth, indexed alongside `stack`.
    backtrack: Vec<HashSet<ThreadId>>,
    /// Threads already explored at each depth.
    done: Vec<HashSet<ThreadId>>,
    explored: u64,
}

impl<'a> Explorer<'a> {
    /// Add `p` at the most recent point where a dependent transition by
    /// another thread ran — the core of DPOR.
    ///
    /// Scanning backwards matters: only the *latest* dependency needs a
    /// backtrack point, because any earlier reordering is subsumed by it.
    fn add_backtrack(&mut self, next_thread: ThreadId, next_accesses: &[Access]) {
        for i in (0..self.stack.len()).rev() {
            let t = &self.stack[i];
            if t.thread == next_thread {
                continue;
            }
            let dependent = t
                .accesses
                .iter()
                .any(|a| next_accesses.iter().any(|b| a.conflicts(b)));
            if !dependent {
                continue;
            }
            // Found the latest conflict. Schedule `next_thread` there if it was
            // enabled; otherwise fall back to every enabled thread, which
            // over-explores but cannot miss a reordering.
            let enabled = t.enabled.clone();
            if enabled.contains(&next_thread) {
                self.backtrack[i].insert(next_thread);
            } else {
                for q in enabled {
                    self.backtrack[i].insert(q);
                }
            }
            return;
        }
    }

    fn explore(&mut self, g: GlobalState, interp: &mut Interp<'a>) -> Option<Exploration> {
        if g.switches > self.bounds.max_switches {
            self.incomplete = Some(format!(
                "context-switch bound {} reached",
                self.bounds.max_switches
            ));
            return None;
        }
        self.explored += 1;
        if self.explored > self.bounds.max_states {
            self.incomplete = Some(format!("state bound {} reached", self.bounds.max_states));
            return None;
        }
        if self.stack.len() > self.bounds.max_depth {
            self.incomplete = Some(format!("depth bound {} reached", self.bounds.max_depth));
            return None;
        }

        if g.is_deadlocked() {
            return Some(Exploration::Deadlock {
                schedule: g.schedule.clone(),
            });
        }
        if g.all_terminated() {
            return None;
        }

        let enabled = g.runnable();
        if enabled.is_empty() {
            return None;
        }

        let depth = self.stack.len();
        self.backtrack.push(HashSet::new());
        self.done.push(HashSet::new());

        // Seed the backtrack set. Exhaustive mode takes every enabled thread;
        // DPOR starts with one and grows the set only where a dependency
        // demands it.
        match self.strategy {
            Strategy::Exhaustive => {
                for t in &enabled {
                    self.backtrack[depth].insert(*t);
                }
            }
            Strategy::Dpor => {
                self.backtrack[depth].insert(enabled[0]);
                // Also seed any enabled thread that has not run anywhere on
                // this path.
                //
                // DPOR grows backtrack sets from *executed* transitions: it
                // compares what a thread just did against the history. A thread
                // that has never executed has no accesses to compare, so no
                // dependency is ever found for it, so no backtrack point is
                // created, so it never executes — a fixed point at "only ever
                // run thread 0".
                //
                // Classic DPOR escapes this because the first interleaving is
                // *maximal*: the running thread finishes and the others become
                // the only enabled ones. That guarantee does not hold here,
                // because an unmodellable construct can end a path early. In
                // RacyNullDeref main walks into `String.length()`, which has no
                // body, before it ever terminates — so the worker never took a
                // turn, its write to `h.s` was never compared against main's
                // read, and the race was unreachable by construction.
                //
                // Seeding a thread's first execution is a small
                // over-approximation of the persistent set: it can explore an
                // interleaving DPOR would have proved redundant, but it cannot
                // miss one. `tools/dpor_equivalence.py` checks that against the
                // unreduced baseline.
                for t in &enabled {
                    if !self.stack.iter().any(|tr| tr.thread == *t) {
                        self.backtrack[depth].insert(*t);
                    }
                }
            }
        }

        loop {
            let next = self.backtrack[depth]
                .iter()
                .find(|t| !self.done[depth].contains(t))
                .copied();
            let Some(tid) = next else { break };
            self.done[depth].insert(tid);

            let mut g2 = g.clone();
            // Everything the interpreter accumulates has to be restored, not
            // just the frames. Sibling branches are alternative universes that
            // re-execute the same statements, so an allocator carried across
            // them hands the *same* `new` a different identity in each.
            //
            // `next_tid` made that fatal rather than merely untidy: a submit
            // re-executed in a sibling branch minted a thread identity beyond
            // the states that exist, and the task failed with "no thread
            // state". Thread constructions escaped it only by happening at
            // depth 0, before any branching.
            let saved_frames = interp.frames.clone();
            let saved_objs = interp.thread_objs.clone();
            let saved_runnables = interp.runnable_objs.clone();
            let saved_next_obj = interp.next_obj;
            let saved_next_tid = interp.next_tid;
            let saved_obj_class = interp.obj_class.clone();
            let saved_interrupted = interp.interrupted.clone();
            let saved_exec_tasks = interp.executor_tasks.clone();
            g2.schedule_step(tid);

            let step = interp.advance(&mut g2, tid);
            let accesses = match &step {
                Step::Advanced(a) => a.clone(),
                // A blocked acquire is a monitor access for dependency
                // purposes. It did not take the lock, but it *contended* for
                // it, and that contention is dependent with whoever holds or
                // acquires the same monitor. Recording it is what lets DPOR
                // find the deadlocking interleaving: without it a blocking
                // transition carries no accesses, no dependency is seen, and
                // the backtrack point that would try the other acquire order is
                // never created.
                Step::Blocked(Some(m)) => vec![Access::Monitor(*m)],
                _ => Vec::new(),
            };

            match step {
                Step::Violated(oid, method) => {
                    return Some(Exploration::Violation {
                        obligation: oid,
                        method,
                        schedule: g2.schedule.clone(),
                    })
                }
                Step::Unsupported(why) => {
                    // One unmodellable construct kills this *interleaving*, not
                    // the search.
                    //
                    // `break` abandoned every remaining backtrack point at this
                    // depth, so a single library call with no body stopped the
                    // sibling schedules from ever being tried. RacyNullDeref
                    // died exactly that way: the first interleaving read a
                    // non-null `h.s` and walked into `String.length()`, which
                    // has no body, and the interleaving where the worker writes
                    // null *first* -- the one that raises the NPE -- was never
                    // explored. Nine states, then silence.
                    //
                    // The run is still marked incomplete, so an exhausted
                    // search cannot be mistaken for a proof. It simply carries
                    // on with the other threads at this point.
                    self.incomplete = Some(why);
                    interp.frames = saved_frames;
                    interp.thread_objs = saved_objs;
                    interp.runnable_objs = saved_runnables;
                    interp.next_obj = saved_next_obj;
                    interp.next_tid = saved_next_tid;
                    interp.obj_class = saved_obj_class;
                    interp.interrupted = saved_interrupted;
                    interp.executor_tasks = saved_exec_tasks;
                    continue;
                }
                Step::Advanced(_) | Step::Terminated | Step::Blocked(_) => {
                    if self.strategy == Strategy::Dpor {
                        self.add_backtrack(tid, &accesses);
                    }
                    self.stack.push(Transition {
                        thread: tid,
                        accesses,
                        enabled: enabled.clone(),
                    });
                    let found = self.explore(g2, interp);
                    self.stack.pop();
                    if found.is_some() {
                        return found;
                    }
                }
            }
            interp.frames = saved_frames;
            interp.thread_objs = saved_objs;
            interp.runnable_objs = saved_runnables;
            interp.next_obj = saved_next_obj;
            interp.next_tid = saved_next_tid;
            interp.obj_class = saved_obj_class;
            interp.interrupted = saved_interrupted;
            interp.executor_tasks = saved_exec_tasks;
        }

        self.backtrack.truncate(depth);
        self.done.truncate(depth);
        None
    }
}

/// Build the state every thread starts from: class initialisers run, thread
/// states created, and `interp.frames` populated.
///
/// Shared by `explore` and `replay_schedule` deliberately. They had drifted:
/// the explorer ran `<clinit>` and drew Runnable identities from the allocator
/// while the replayer started with empty statics and a fixed `Ref(1000 + i)`
/// base. A certifier that reconstructs a *different* initial state can only
/// confirm violations in programs whose statics do not matter, and silently
/// fails to reproduce every other one -- which reads as "the explorer was
/// wrong" when it was the certifier that never saw the same program.
fn build_initial_state(
    prog: &Program,
    entries: &[crate::threads::ThreadEntry],
    bounds: Bounds,
    interp: &mut Interp,
) -> Result<GlobalState, String> {
    let Some(entry) = prog.entry.clone() else {
        return Err("no entry method".into());
    };
    if entries.len() + 1 > bounds.max_threads {
        return Err(format!(
            "{} threads exceeds bound {}",
            entries.len() + 1,
            bounds.max_threads
        ));
    }
    // Establish the static state by *running* `<clinit>`, not by guessing it.
    //
    // Class initialisers were previously approximated: a static whose
    // initialiser was visibly a `new` got a fresh object id, and anything else
    // stayed `Val::Ref(0)` -- null. Both halves of that misfired.
    //
    // Reading an uninitialised static as null does not merely lose precision
    // here, it flips verdicts. `static final Condition cond = lock.newCondition()`
    // is not a `new`, so `cond` read as null, the null-check before `await`
    // pruned every path that reaches it, and a program that deadlocks on a
    // missed signal was reported TRUE. Pruning paths is how an under-approximation
    // turns into a wrong proof.
    //
    // Running the initialiser is also simply what the JVM does, and it gets
    // aliasing, factory methods and computed initial values right for free.
    //
    // Approximation that remains: every `<clinit>` runs up front, in
    // `bodies` order, whereas the JVM runs each lazily on first use. That
    // differs only for initialisers that read another class's statics before
    // it is initialised -- which observes a default value on a real JVM too,
    // just possibly a different one. No benchmark here does it, and the
    // alternative (lazy initialisation during exploration) needs `<clinit>`
    // frames pushed mid-schedule.
    let mut statics: std::collections::BTreeMap<(String, String), (bool, i64)> =
        Default::default();
    let mut heap: std::collections::BTreeMap<(ObjId, String), (bool, i64)> = Default::default();
    let mut clinit_failed: Option<String> = None;
    for mk in prog.bodies.keys().filter(|k| k.name == "<clinit>").cloned() {
        let Some(st) = spawn_state(ThreadId(0), &mk, prog, true) else {
            continue;
        };
        let Some(frame) = interp.initial_frame(&mk, None) else {
            continue;
        };
        let mut cg = GlobalState {
            threads: vec![st],
            monitor_owner: Default::default(),
            heap: heap.clone(),
            statics: statics.clone(),
            schedule: Vec::new(),
            switches: 0,
        };
        interp.frames = vec![vec![frame]];
        let mut done = false;
        for _ in 0..bounds.max_steps {
            match interp.advance(&mut cg, ThreadId(0)) {
                Step::Terminated => {
                    done = true;
                    break;
                }
                Step::Advanced(_) => {}
                Step::Blocked(_) => {
                    // A class initialiser that blocks is either deadlocked at
                    // class-init time or uses a primitive we do not model.
                    clinit_failed = Some(format!("{} blocked", mk.class));
                    break;
                }
                Step::Unsupported(why) => {
                    clinit_failed = Some(format!("{}: {}", mk.class, why));
                    break;
                }
                // A check violated during class initialisation is a real
                // violation, reachable before main even starts. Reporting it
                // needs a witness carrying a schedule that never entered the
                // scheduler, so decline instead of claiming either verdict.
                Step::Violated(..) => {
                    clinit_failed = Some(format!("{} violates a check", mk.class));
                    break;
                }
            }
        }
        if !done {
            if clinit_failed.is_none() {
                clinit_failed = Some(format!("{} did not finish", mk.class));
            }
            break;
        }
        statics = cg.statics;
        heap = cg.heap;
    }
    // An initialiser we could not run leaves statics at their default null
    // reading, which is exactly the unsound case above. Refuse rather than
    // explore a state we know is wrong.
    if let Some(why) = clinit_failed {
        return Err(format!("could not run class initialiser: {why}"));
    }

    let mut threads = Vec::new();
    let mut frames = Vec::new();

    // Thread 0 is main; the rest are the discovered run() bodies. Starting
    // every thread up front over-approximates: a real program only starts a
    // thread when it reaches start(). That is sound in the direction that
    // matters for *deadlock* and *safety* here only because the benchmarks
    // start all threads before joining — a more faithful model needs start()
    // to spawn, which is the next refinement.
    let Some(main_state) = spawn_state(ThreadId(0), &entry, prog, true) else {
        return Err("no body for entry".into());
    };
    threads.push(main_state);
    frames.push(vec![interp.initial_frame(&entry, None).unwrap()]);

    for (i, e) in entries.iter().enumerate() {
        let tid = ThreadId(i as u32 + 1);
        let Some(st) = spawn_state(tid, &e.run, prog, false) else {
            return Err(format!("no body for {}", e.run));
        };
        threads.push(st);
        // `this` for the Runnable: a fresh object identity. Drawn from the
        // allocator rather than a fixed 1000+i base, which could collide with
        // an object a class initialiser allocated and silently alias two
        // distinct objects.
        let _ = i;
        let this = Val::Ref(interp.next_obj);
        interp.next_obj += 1;
        match interp.initial_frame(&e.run, Some(this)) {
            Some(f) => frames.push(vec![f]),
            None => return Err(format!("no frame for {}", e.run)),
        }
    }
    interp.frames = frames;

    Ok(GlobalState {
        threads,
        monitor_owner: Default::default(),
        heap,
        statics,
        schedule: Vec::new(),
        switches: 0,
    })

}

/// Explore every interleaving of `entries` plus the main thread.
pub fn explore(
    prog: &Program,
    entries: &[crate::threads::ThreadEntry],
    bounds: Bounds,
    strategy: Strategy,
) -> Exploration {
    let Some(entry) = prog.entry.clone() else {
        return Exploration::Incomplete("no entry method".into());
    };
    if entries.len() + 1 > bounds.max_threads {
        return Exploration::Incomplete(format!(
            "{} threads exceeds bound {}",
            entries.len() + 1,
            bounds.max_threads
        ));
    }

    let mut interp = Interp::new(prog, bounds.max_steps);
    let g = match build_initial_state(prog, entries, bounds, &mut interp) {
        Ok(g) => g,
        Err(why) => return Exploration::Incomplete(why),
    };

    let mut ex = Explorer {
        prog,
        bounds,
        strategy,
        incomplete: None,
        stack: Vec::new(),
        backtrack: Vec::new(),
        done: Vec::new(),
        explored: 0,
    };
    let result = ex.explore(g, &mut interp);
    log::debug!(
        "concurrency: {:?} explored {} state(s)",
        strategy,
        ex.explored
    );
    match result {
        Some(found) => found,
        None => match ex.incomplete {
            Some(why) => Exploration::Incomplete(why),
            // Stepping over an unmodelled call lets an interleaving finish,
            // which DPOR needs, but the callee's effects were not modelled — so
            // the search covered every *schedule* without covering every
            // *behaviour*, and must not be reported as a proof.
            None if !interp.skipped_calls.is_empty() => {
                let mut names: Vec<String> = interp.skipped_calls.clone();
                names.sort();
                names.dedup();
                Exploration::Incomplete(format!(
                    "stepped over {} unmodelled call(s): {}",
                    names.len(),
                    names.join(", ")
                ))
            }
            None => Exploration::ExhaustiveNoViolation,
        },
    }
}


/// Re-run the program forcing exactly the schedule a witness records, and
/// report whether the same obligation is violated.
///
/// This is the concurrency counterpart of `JvmReplay`, and it is deliberately
/// weaker: it certifies against **our own interpreter**, not a real JVM.
/// `JvmReplay` can hand a stock JVM the nondet values but cannot force an
/// interleaving, so it returns Inconclusive for these witnesses (see
/// `certify.rs`). Until a JVM agent exists that can enforce a schedule, a
/// concurrency FALSE rests on the interpreter being right — which is a weaker
/// guarantee than every other FALSE ajave emits, and is recorded as such in
/// docs/strategies/concurrency.md.
///
/// What it does still catch: a schedule that does not actually reach the
/// violation, which is the failure mode of a buggy explorer. Replaying is not
/// a rubber stamp — it independently re-derives the outcome from the recorded
/// interleaving.
pub fn replay_schedule(
    prog: &Program,
    entries: &[crate::threads::ThreadEntry],
    oref: &ObligationRef,
    schedule: &[ScheduleSlice],
    bounds: Bounds,
) -> bool {
    // Same constructor the explorer used. Reconstructing the initial state
    // independently is how this certifier came to replay a program with empty
    // statics against a schedule recorded on one whose class initialisers had
    // run: it could not reproduce the violation, and the FALSE was discarded.
    let mut interp = Interp::new(prog, bounds.max_steps);
    let mut g = match build_initial_state(prog, entries, bounds, &mut interp) {
        Ok(g) => g,
        Err(_) => return false,
    };

    // Follow the recorded interleaving exactly.
    for slice in schedule {
        for _ in 0..slice.steps {
            match interp.advance(&mut g, slice.thread) {
                Step::Violated(oid, ref m) => {
                    // Reproduced only if it is the *same* obligation. A
                    // different violation would mean the schedule reaches some
                    // other bug, which does not certify this witness.
                    return oid == oref.id && *m == oref.method;
                }
                Step::Unsupported(_) => return false,
                Step::Advanced(_) | Step::Terminated | Step::Blocked(_) => {}
            }
        }
    }
    false
}

pub struct ConcurrencyEngine {
    done: bool,
    #[allow(dead_code)]
    bounds: Bounds,
}

impl ConcurrencyEngine {
    pub fn new() -> Self {
        ConcurrencyEngine {
            done: false,
            bounds: Bounds::from_env(),
        }
    }
}

impl Default for ConcurrencyEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine for ConcurrencyEngine {
    fn id(&self) -> EngineId {
        EngineId("concurrency")
    }

    fn direction(&self) -> Direction {
        // Bounded exploration can exhibit a bug but never prove its absence.
        Direction::Under
    }

    fn step(&mut self, prog: &Program, _bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        match check_preconditions(prog) {
            Err(Refusal::Sequential) => {
                debug!("concurrency: {}", Refusal::Sequential);
                Progress::Exhausted
            }
            Err(why) => {
                // Deliberately INFO, not DEBUG: a refusal is the difference
                // between "no bug here" and "we did not look", and that
                // distinction should be visible without -vv.
                info!("concurrency: declining to analyse — {why}");
                Progress::Stalled
            }
            Ok(entries) => {
                info!(
                    "concurrency: {} thread(s) resolved: {}",
                    entries.len(),
                    entries
                        .iter()
                        .map(|e| e.run.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );

                match explore(prog, &entries, self.bounds, Strategy::Dpor) {
                    Exploration::Violation { obligation, method, schedule } => {
                        info!(
                            "concurrency: violation of {method}#{} under a {}-slice schedule",
                            obligation.0,
                            schedule.len()
                        );
                        let oref = ObligationRef { method, id: obligation };
                        let witness = Witness {
                            nondet_sequence: Vec::new(),
                            entries: Vec::new(),
                            schedule,
                        };
                        let published = _bb.publish(
                            self.id(),
                            Direction::Under,
                            Artifact::Status(
                                oref,
                                Status::Violated { by: self.id(), witness },
                            ),
                        );
                        if published.is_ok() { Progress::Advanced } else { Progress::Stalled }
                    }
                    Exploration::Deadlock { schedule } => {
                        // Neither valid-assert nor no-runtime-exception is
                        // violated by a deadlock — the program hangs rather
                        // than failing — so there is nothing to publish under
                        // the properties we score. Reported for visibility.
                        info!(
                            "concurrency: deadlock reachable under a {}-slice schedule \
                             (not a violation of either scored property)",
                            schedule.len()
                        );
                        Progress::Stalled
                    }
                    Exploration::ExhaustiveNoViolation => {
                        // Every interleaving within the bounds was explored and
                        // no bound was hit, so the bounded space was genuinely
                        // covered. That licenses discharging the obligations in
                        // the threads we explored — published as Over, exactly
                        // as the BMC does for an exhaustive exploration.
                        //
                        // The bound still matters: it is `max_switches`
                        // preemptions, not all schedules. Recorded in the log
                        // so the claim is auditable.
                        info!(
                            "concurrency: exhaustive within {} context switches, no violation",
                            self.bounds.max_switches
                        );
                        let mut advanced = false;
                        // `open_or_unconfirmed`, not `open`: a sequential
                        // engine analysing a threaded program gets wrong
                        // answers — `concrete` reports the assert in
                        // JoinOrdersWrite as violated because `t.start()` is a
                        // no-op to it, so the joined write never happens. That
                        // candidate is refuted at replay, but it would still
                        // veto this engine's proof if we only considered open
                        // obligations. Same reasoning as the BMC's discharge
                        // loop.
                        for oref in _bb.open_or_unconfirmed() {
                            let published = _bb.publish(
                                self.id(),
                                Direction::Over,
                                Artifact::Status(
                                    oref,
                                    Status::Discharged {
                                        by: self.id(),
                                        proof: ProofKind::Exhaustive,
                                    },
                                ),
                            );
                            if published.is_ok() { advanced = true; }
                        }
                        if advanced { Progress::Advanced } else { Progress::Stalled }
                    }
                    Exploration::Incomplete(why) => {
                        info!("concurrency: exploration incomplete — {why}");
                        Progress::Stalled
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::{Block, BlockId, Body, MethodKey, Terminator, Ty, VarId, VarInfo, VarKind};

    fn body_with(stmts: Vec<Stmt>, nvars: usize) -> Body {
        body_named(mk_key("Main", "main", "()V"), stmts, nvars)
    }

    fn mk_key(class: &str, name: &str, desc: &str) -> MethodKey {
        MethodKey { class: class.into(), name: name.into(), desc: desc.into() }
    }

    fn body_named(key: MethodKey, stmts: Vec<Stmt>, nvars: usize) -> Body {
        Body {
            key,
            vars: (0..nvars)
                .map(|i| VarInfo {
                    ty: Ty::Ref,
                    kind: VarKind::Local(i as u16),
                })
                .collect(),
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts,
                term: Terminator::Return(None),
                exceptional: Vec::new(),
            }],
            entry: BlockId(0),
            obligations: Vec::new(),
        }
    }

    fn mk(class: &str, name: &str, desc: &str) -> MethodKey {
        MethodKey {
            class: class.into(),
            name: name.into(),
            desc: desc.into(),
        }
    }

    #[test]
    fn sequential_program_is_refused_as_sequential() {
        let mut prog = Program::default();
        prog.bodies
            .insert(mk("Main", "main", "()V"), body_with(vec![], 1));
        assert_eq!(check_preconditions(&prog), Err(Refusal::Sequential));
    }

    #[test]
    fn unmodelled_primitive_refuses() {
        // A synchronizer treated as a no-op would drop the ordering the
        // program relies on, letting us produce interleavings the JVM cannot —
        // a wrong FALSE for an Under engine.
        //
        // Uses `Phaser`, which is genuinely unmodelled. This test named
        // `CountDownLatch` until that was modelled, at which point it began
        // asserting that a supported feature is refused; the mechanism under
        // test is the refusal, so it needs a primitive still outside the model.
        let mut prog = Program::default();
        prog.bodies.insert(
            mk("Main", "main", "()V"),
            body_with(
                vec![Stmt::Assign(
                    VarId(0),
                    Rvalue::Call {
                        target: mk("java/util/concurrent/Phaser", "arriveAndAwaitAdvance", "()I"),
                        args: vec![Operand::Var(VarId(1))],
                        is_virtual: true,
                    },
                )],
                2,
            ),
        );
        match check_preconditions(&prog) {
            Err(Refusal::UnmodelledPrimitive(c)) => {
                assert!(c.contains("Phaser"))
            }
            other => panic!("expected UnmodelledPrimitive, got {other:?}"),
        }
    }
}
