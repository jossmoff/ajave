//! State model for bounded interleaving exploration.
//!
//! Phase 4 of `docs/strategies/concurrency.md`. This is the representation
//! only — the explorer that drives it comes next.
//!
//! # Where the state explosion is bounded, and why there
//!
//! The reachable state space of a concurrent program is the product of every
//! thread's local state with the shared heap, over every interleaving. That is
//! unbounded in three independent directions, and each needs its own cap:
//!
//! * **Context switches.** Bounded by `max_switches`. This is the classic
//!   context-bounded model checking result (Qadeer & Rehof): most concurrency
//!   bugs manifest with very few preemptions, so a small bound finds most bugs
//!   at a fraction of the cost. It is a *completeness* bound, not a soundness
//!   one — we may miss a bug needing more switches, never invent one.
//! * **Steps per thread.** Bounded by `max_steps`, so a spinning thread cannot
//!   consume the whole budget.
//! * **Live threads.** Bounded by `max_threads`.
//!
//! Every bound is a reason to answer UNKNOWN rather than TRUE. An explorer
//! using this must be `Direction::Under`.

use std::collections::BTreeMap;

use ajave_core::artifact::ProgramPoint;
use ajave_ir::verdict::{ScheduleSlice, ThreadId};
use ajave_ir::{MethodKey, VarId};

/// Where a thread is in its lifecycle.
///
/// `Blocked` and `Waiting` are distinct because they resume for different
/// reasons: a blocked thread becomes runnable when the monitor it wants is
/// released, a waiting one only when notified. Collapsing them would let the
/// explorer resume a `wait()` that nobody notified, inventing schedules the
/// JVM cannot produce — and for an Under engine that means inventing bugs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThreadStatus {
    Runnable,
    /// Waiting to acquire the monitor of the given object.
    Blocked { monitor: ObjId },
    /// Inside `Object.wait()` on the given monitor, pending a notify.
    Waiting { monitor: ObjId },
    /// Created but `start()` has not been called. Not runnable, and not
    /// deadlocked either — the program simply has not started it yet.
    NotStarted,
    /// Blocked in `join()` until the named thread terminates.
    ///
    /// This edge is not optional. `join()` establishes happens-before between
    /// the joined thread's last action and the joiner's next one (JLS 17.4.5);
    /// treating it as a no-op lets the explorer run past a join before the
    /// thread has done anything, which invents interleavings the JVM cannot
    /// produce. That is a wrong FALSE for an Under engine — and it is exactly
    /// what happened before this was modelled.
    Joining { on: ThreadId },
    Terminated,
}

/// Identifies an object in the shared heap.
///
/// Allocation-site identity, not a concrete address: two objects from the same
/// `new` are the same `ObjId`. That is the same flat abstraction the interval
/// domain's field cells use, and it has the same consequence — a lock on one
/// instance looks like a lock on all of them.
///
/// For monitors this is **unsound in the dangerous direction**: it can make two
/// threads look mutually excluded when they hold locks on *different* objects,
/// hiding a real race. Any explorer must therefore refuse to reason about
/// mutual exclusion unless the class has a single allocation site — the same
/// `singleton_classes` test `FieldPrec` already computes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObjId(pub u32);

/// One thread's private execution state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThreadState {
    pub id: ThreadId,
    pub at: ProgramPoint,
    pub status: ThreadStatus,
    /// Locals, as concrete values. The explorer is concrete rather than
    /// symbolic: symbolic values would multiply with interleavings, and the
    /// point of Phase 4 is a ground-truth baseline, not a fast one.
    pub locals: BTreeMap<VarId, i64>,
    /// Call stack of return points; empty means the next return terminates
    /// the thread.
    pub stack: Vec<ProgramPoint>,
    /// Monitors held, innermost last. A JVM monitor is reentrant, so the same
    /// `ObjId` may appear more than once and only the outermost release
    /// actually frees it.
    pub monitors: Vec<ObjId>,
}

impl ThreadState {
    pub fn holds(&self, m: ObjId) -> bool {
        self.monitors.contains(&m)
    }

    /// Reentrant acquire: pushing a monitor already held is legal and only the
    /// matching release frees it.
    pub fn enter(&mut self, m: ObjId) {
        self.monitors.push(m);
    }

    /// Release the innermost acquisition of `m`. Returns whether the monitor
    /// is now fully released and available to other threads.
    pub fn exit(&mut self, m: ObjId) -> bool {
        if let Some(i) = self.monitors.iter().rposition(|&x| x == m) {
            self.monitors.remove(i);
        }
        !self.holds(m)
    }
}

/// Shared state: the heap, monitor ownership, and every thread.
#[derive(Clone, Debug)]
pub struct GlobalState {
    pub threads: Vec<ThreadState>,
    /// Which thread owns each monitor, if any.
    pub monitor_owner: BTreeMap<ObjId, ThreadId>,
    /// Instance fields, keyed by `(object, field)`.
    ///
    /// Values carry their reference-ness: storing a plain `i64` loses the
    /// distinction between an int and an object identity, so reading a field
    /// that holds a reference and dereferencing it fails. `(is_ref, value)`.
    pub heap: BTreeMap<(ObjId, String), (bool, i64)>,
    /// Static fields, keyed by `(class, field)`.
    pub statics: BTreeMap<(String, String), (bool, i64)>,
    /// The interleaving taken to reach this state, for the witness.
    pub schedule: Vec<ScheduleSlice>,
    /// Context switches used so far, against `Bounds::max_switches`.
    pub switches: u32,
}

/// Exploration bounds. Every one of these is a reason to answer UNKNOWN.
#[derive(Clone, Copy, Debug)]
pub struct Bounds {
    pub max_switches: u32,
    pub max_steps: u64,
    pub max_threads: usize,
}

impl Default for Bounds {
    fn default() -> Self {
        // Deliberately small. Context-bounded model checking finds most
        // concurrency bugs within two or three preemptions, and a tight bound
        // keeps the baseline explorer honest about being a baseline.
        //
        // These are fitted-by-nothing starting values: see issue #50 on
        // deriving budgets from program shape rather than fixing them.
        // Raised from 3 once DPOR landed. A bound that cannot cover a
        // two-thread counter is too small to prove anything: SynchronizedCounter
        // has more preemption points than the unsynchronised version (the
        // monitor operations are themselves visible actions), and exhausted 3.
        //
        // This is affordable *because* of the reduction — the naive explorer
        // could not have gone here. Still a completeness bound, never a
        // soundness one, and still fitted rather than derived (#50).
        Bounds {
            max_switches: 10,
            max_steps: 100_000,
            max_threads: 4,
        }
    }
}

impl GlobalState {
    /// Threads that could execute next.
    ///
    /// A `Blocked` thread becomes runnable exactly when its monitor is
    /// unowned; a `Waiting` one does not appear here at all, since only a
    /// notify can move it.
    pub fn runnable(&self) -> Vec<ThreadId> {
        self.threads
            .iter()
            .filter(|t| match t.status {
                ThreadStatus::Runnable => true,
                ThreadStatus::Blocked { monitor } => !self.monitor_owner.contains_key(&monitor),
                ThreadStatus::Joining { on } => self
                    .threads
                    .iter()
                    .find(|x| x.id == on)
                    .map(|x| x.status == ThreadStatus::Terminated)
                    .unwrap_or(true),
                ThreadStatus::Waiting { .. }
                | ThreadStatus::NotStarted
                | ThreadStatus::Terminated => false,
            })
            .map(|t| t.id)
            .collect()
    }

    /// Every thread is finished.
    pub fn all_terminated(&self) -> bool {
        self.threads.iter().all(|t| {
            matches!(
                t.status,
                ThreadStatus::Terminated | ThreadStatus::NotStarted
            )
        })
    }

    /// A thread that has not been started yet is not stuck — the program may
    /// still start it — so it does not count as live for deadlock purposes.
    fn has_unstarted(&self) -> bool {
        self.threads
            .iter()
            .any(|t| t.status == ThreadStatus::NotStarted)
    }

    /// No thread can proceed, but not all have finished.
    ///
    /// This is the deadlock condition: threads exist, none is runnable, and
    /// none has terminated. Note it covers both lock-order inversion (all
    /// `Blocked`) and a missed notify (all `Waiting`), which is why the two
    /// statuses are tracked separately.
    pub fn is_deadlocked(&self) -> bool {
        !self.all_terminated() && self.runnable().is_empty() && !self.has_unstarted()
    }

    /// Record that `thread` is about to run, extending the current slice or
    /// starting a new one. Returns whether this counted as a **preemption**.
    ///
    /// The bound is on preemptions, not on switches. A switch away from a
    /// thread that has terminated or blocked is forced — the scheduler had no
    /// choice — and counting it would exhaust the budget on programs that
    /// simply run threads one after another. Qadeer & Rehof's result is about
    /// preemptions specifically: the number of times the scheduler interrupts
    /// a thread that *could* have continued.
    ///
    /// Counting switches instead made a two-thread counter unanalysable at
    /// bound 3, because start/join alone consume several forced switches.
    pub fn schedule_step(&mut self, thread: ThreadId) -> bool {
        match self.schedule.last_mut() {
            Some(last) if last.thread == thread => {
                last.steps += 1;
                false
            }
            _ => {
                // Was the outgoing thread still able to run? If so this is a
                // genuine preemption; if it had blocked or finished, the
                // switch was forced.
                let preempted = match self.schedule.last() {
                    Some(prev) => self
                        .threads
                        .iter()
                        .find(|t| t.id == prev.thread)
                        .map(|t| matches!(t.status, ThreadStatus::Runnable))
                        .unwrap_or(false),
                    // The first slice has nothing to preempt.
                    None => false,
                };
                self.schedule.push(ScheduleSlice { thread, steps: 1 });
                if preempted {
                    self.switches += 1;
                }
                preempted
            }
        }
    }
}

/// Why exploration stopped, which decides what verdict we may claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExploreOutcome {
    /// Every reachable interleaving within the bounds was explored and none
    /// violated the property. This still does **not** license TRUE: the bounds
    /// mean unexplored interleavings exist.
    ExhaustedWithinBounds,
    /// A bound was hit, so not even the bounded space was covered.
    BoundHit(&'static str),
    /// A violating interleaving was found.
    Violation {
        method: MethodKey,
        schedule: Vec<ScheduleSlice>,
    },
    /// A state where no thread can proceed and not all have terminated.
    Deadlock { schedule: Vec<ScheduleSlice> },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn point() -> ProgramPoint {
        ProgramPoint {
            method: MethodKey {
                class: "Main".into(),
                name: "main".into(),
                desc: "()V".into(),
            },
            block: ajave_ir::BlockId(0),
            index: 0,
        }
    }

    fn thread(id: u32, status: ThreadStatus) -> ThreadState {
        ThreadState {
            id: ThreadId(id),
            at: point(),
            status,
            locals: BTreeMap::new(),
            stack: Vec::new(),
            monitors: Vec::new(),
        }
    }

    fn state(threads: Vec<ThreadState>) -> GlobalState {
        GlobalState {
            threads,
            monitor_owner: BTreeMap::new(),
            heap: BTreeMap::new(),
            statics: BTreeMap::new(),
            schedule: Vec::new(),
            switches: 0,
        }
    }

    #[test]
    fn monitors_are_reentrant() {
        let mut t = thread(0, ThreadStatus::Runnable);
        t.enter(ObjId(1));
        t.enter(ObjId(1));
        // The inner release must not free the monitor.
        assert!(!t.exit(ObjId(1)), "inner release freed a reentrant monitor");
        assert!(t.holds(ObjId(1)));
        assert!(t.exit(ObjId(1)), "outer release did not free the monitor");
    }

    #[test]
    fn blocked_thread_becomes_runnable_when_monitor_freed() {
        let mut g = state(vec![thread(0, ThreadStatus::Blocked { monitor: ObjId(7) })]);
        g.monitor_owner.insert(ObjId(7), ThreadId(1));
        assert!(g.runnable().is_empty());
        g.monitor_owner.remove(&ObjId(7));
        assert_eq!(g.runnable(), vec![ThreadId(0)]);
    }

    #[test]
    fn waiting_thread_does_not_self_wake() {
        // A waiting thread must stay unrunnable even with the monitor free —
        // only a notify moves it. Treating Waiting like Blocked would let the
        // explorer resume a wait() nobody notified, inventing a schedule the
        // JVM cannot produce.
        let g = state(vec![thread(0, ThreadStatus::Waiting { monitor: ObjId(7) })]);
        assert!(g.runnable().is_empty());
        assert!(g.is_deadlocked(), "un-notified wait is a deadlock");
    }

    #[test]
    fn all_blocked_is_deadlock_but_all_terminated_is_not() {
        let g = state(vec![
            thread(0, ThreadStatus::Blocked { monitor: ObjId(1) }),
            thread(1, ThreadStatus::Blocked { monitor: ObjId(2) }),
        ]);
        let mut g = g;
        g.monitor_owner.insert(ObjId(1), ThreadId(1));
        g.monitor_owner.insert(ObjId(2), ThreadId(0));
        assert!(g.is_deadlocked(), "lock-order inversion not detected");

        let done = state(vec![
            thread(0, ThreadStatus::Terminated),
            thread(1, ThreadStatus::Terminated),
        ]);
        assert!(!done.is_deadlocked(), "clean termination reported as deadlock");
    }

    #[test]
    fn schedule_records_switches_not_steps() {
        let mut g = state(vec![thread(0, ThreadStatus::Runnable)]);
        assert!(!g.schedule_step(ThreadId(0)), "first slice is not a switch");
        assert!(!g.schedule_step(ThreadId(0)), "same thread is not a switch");
        assert!(g.schedule_step(ThreadId(1)), "different thread is a switch");
        assert_eq!(g.switches, 1);
        assert_eq!(
            g.schedule,
            vec![
                ScheduleSlice { thread: ThreadId(0), steps: 2 },
                ScheduleSlice { thread: ThreadId(1), steps: 1 },
            ]
        );
    }
}
