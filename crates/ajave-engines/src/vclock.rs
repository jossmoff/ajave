//! Vector clocks and the happens-before relation.
//!
//! # Why this is a relation and not an ordering on the schedule
//!
//! Under sequential consistency an execution *is* a total order, so "did A
//! happen before B" could be answered by looking at their positions in the
//! interleaving. That answer is useless for the question we actually need to
//! ask, which is whether two accesses are ordered *by synchronisation* — and it
//! is wrong the moment executions stop being sequentially consistent.
//!
//! So happens-before is built here as its own relation, from edges emitted by
//! the synchronisation primitives themselves (release/acquire), and never from
//! the order in which the explorer happened to schedule threads. Two
//! consequences, both deliberate:
//!
//! * A **data race** is expressible: two conflicting accesses whose clocks are
//!   incomparable. In the schedule order every pair is comparable, so the
//!   notion does not even exist there.
//! * The relation stays correct if we later explore executions that are not
//!   sequentially consistent. A weak-memory explorer branches a read over the
//!   writes it may observe; the happens-before edges among synchronising
//!   operations are unchanged by that. Deriving the relation from the schedule
//!   would have to be thrown away at that point.
//!
//! # The rules (JLS 17.4.5)
//!
//! Each thread `t` carries a clock `C_t`. A *release* of some synchronisation
//! object `m` (monitor exit, volatile write, `countDown`, thread termination)
//! publishes `C_t` into `L_m`; a matching *acquire* (monitor enter, volatile
//! read, `await` returning, `join` returning) joins `L_m` into `C_t`. Each
//! thread increments its own component on release so that later actions are
//! distinguishable from earlier ones.

use std::collections::HashMap;

/// A vector clock, indexed by thread id.
///
/// Sparse rather than a fixed-width array: thread count is bounded but small,
/// and a map keeps the type independent of `Bounds::max_threads`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VClock {
    ticks: HashMap<u32, u64>,
}

impl VClock {
    pub fn new() -> VClock {
        VClock::default()
    }

    pub fn get(&self, t: u32) -> u64 {
        self.ticks.get(&t).copied().unwrap_or(0)
    }

    /// Advance this thread's own component.
    pub fn tick(&mut self, t: u32) {
        *self.ticks.entry(t).or_insert(0) += 1;
    }

    /// Pointwise maximum: this is the acquire step.
    pub fn join(&mut self, other: &VClock) {
        for (&t, &v) in &other.ticks {
            let e = self.ticks.entry(t).or_insert(0);
            if v > *e {
                *e = v;
            }
        }
    }

    /// `self <= other` pointwise, i.e. everything this clock has seen, that one
    /// has seen too. This is the happens-before test.
    pub fn happens_before(&self, other: &VClock) -> bool {
        self.ticks.iter().all(|(&t, &v)| v <= other.get(t))
    }
}

/// What a release/acquire pair synchronises on.
///
/// Volatile fields and monitors are distinct keys even when they belong to the
/// same object: locking an object and writing a volatile field of it are
/// different synchronisation actions and must not be conflated.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SyncKey {
    Monitor(u32),
    /// A volatile static, or a volatile instance field of a specific object.
    Volatile(u32, String),
    /// A synchronizer object: latch, semaphore, barrier, queue, condition.
    Sync(u32),
    /// A thread, for the start and join edges.
    Thread(u32),
}

/// The happens-before state of an execution.
#[derive(Clone, Debug, Default)]
pub struct Hb {
    threads: HashMap<u32, VClock>,
    released: HashMap<SyncKey, VClock>,
}

impl Hb {
    /// A thread's own component starts at 1, not 0, so that "what this thread
    /// has done so far" is always a non-empty fact that a release can publish.
    pub fn clock(&self, t: u32) -> VClock {
        self.threads.get(&t).cloned().unwrap_or_else(|| {
            let mut c = VClock::new();
            c.tick(t);
            c
        })
    }

    /// Publish this thread's knowledge to `key`, *then* advance the thread.
    ///
    /// The order is the whole point. Publishing after the tick would hand the
    /// acquirer a clock that already covers the releaser's next action, so
    /// everything the releaser does afterwards would appear ordered before
    /// whatever the acquirer does -- and no two threads would ever look
    /// concurrent. That is a race detector that reports nothing.
    pub fn release(&mut self, t: u32, key: SyncKey) {
        log::trace!("hb: t{t} release {key:?}");
        let mut c = self.clock(t);
        self.released.entry(key).or_default().join(&c);
        c.tick(t);
        self.threads.insert(t, c);
    }

    /// Absorb whatever was last released to `key`.
    pub fn acquire(&mut self, t: u32, key: SyncKey) {
        log::trace!("hb: t{t} acquire {key:?}");
        let acquired = self.released.get(&key).cloned().unwrap_or_default();
        let mut c = self.clock(t);
        c.join(&acquired);
        self.threads.insert(t, c);
    }

    /// A fork edge: everything the parent has done happens-before the child's
    /// first action.
    pub fn fork(&mut self, parent: u32, child: u32) {
        self.release(parent, SyncKey::Thread(child));
        self.acquire(child, SyncKey::Thread(child));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsynchronised_threads_are_concurrent() {
        // Two threads that never synchronise have incomparable clocks in both
        // directions. This is the shape of a data race, and it is the case the
        // schedule order cannot express -- there, one of them is simply first.
        let mut hb = Hb::default();
        hb.release(0, SyncKey::Monitor(1));
        hb.release(1, SyncKey::Monitor(2));
        let (a, b) = (hb.clock(0), hb.clock(1));
        assert!(!a.happens_before(&b));
        assert!(!b.happens_before(&a));
    }

    #[test]
    fn release_then_acquire_orders_them() {
        let mut hb = Hb::default();
        let before = hb.clock(0);
        hb.release(0, SyncKey::Monitor(1));
        hb.acquire(1, SyncKey::Monitor(1));
        assert!(before.happens_before(&hb.clock(1)));
    }

    #[test]
    fn acquiring_a_different_monitor_orders_nothing() {
        // The edge is per synchronisation object. Conflating two monitors would
        // order threads that a real JVM leaves concurrent, hiding races.
        let mut hb = Hb::default();
        let before = hb.clock(0);
        hb.release(0, SyncKey::Monitor(1));
        hb.acquire(1, SyncKey::Monitor(99));
        assert!(!before.happens_before(&hb.clock(1)));
    }

    #[test]
    fn a_monitor_and_a_volatile_on_one_object_are_distinct() {
        let mut hb = Hb::default();
        let before = hb.clock(0);
        hb.release(0, SyncKey::Monitor(7));
        hb.acquire(1, SyncKey::Volatile(7, "f".into()));
        assert!(!before.happens_before(&hb.clock(1)));
    }

    #[test]
    fn fork_orders_parent_before_child() {
        let mut hb = Hb::default();
        let at_fork = hb.clock(0);
        hb.fork(0, 5);
        assert!(at_fork.happens_before(&hb.clock(5)));
        // ...but not the other way.
        assert!(!hb.clock(5).happens_before(&at_fork));
    }

    #[test]
    fn a_releaser_s_later_actions_are_not_visible_to_the_acquirer() {
        // The bug this pins: ticking before publishing handed the acquirer a
        // clock covering the releaser's *next* action, so a fork made the
        // parent's subsequent writes look ordered before the child's and the
        // detector found no races at all.
        let mut hb = Hb::default();
        hb.fork(0, 5);
        let parent_after_fork = hb.clock(0);
        let child = hb.clock(5);
        assert!(!parent_after_fork.happens_before(&child));
        assert!(!child.happens_before(&parent_after_fork));
    }

    #[test]
    fn happens_before_is_transitive_through_a_chain() {
        let mut hb = Hb::default();
        let a = hb.clock(0);
        hb.release(0, SyncKey::Monitor(1));
        hb.acquire(1, SyncKey::Monitor(1));
        hb.release(1, SyncKey::Monitor(2));
        hb.acquire(2, SyncKey::Monitor(2));
        assert!(a.happens_before(&hb.clock(2)));
    }
}
