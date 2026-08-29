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

use crate::concurrent_state::Bounds;
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
    "java/util/concurrent/locks/ReentrantLock",
    "java/util/concurrent/locks/ReentrantReadWriteLock",
    "java/util/concurrent/CountDownLatch",
    "java/util/concurrent/CyclicBarrier",
    "java/util/concurrent/Semaphore",
    "java/util/concurrent/Phaser",
    "java/util/concurrent/ExecutorService",
    "java/util/concurrent/CompletableFuture",
    "java/util/concurrent/ForkJoinPool",
    "java/util/concurrent/atomic/AtomicInteger",
    "java/util/concurrent/atomic/AtomicLong",
    "java/util/concurrent/atomic/AtomicBoolean",
    "java/util/concurrent/atomic/AtomicReference",
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
    let mut monitored: HashSet<String> = HashSet::new();

    for body in prog.bodies.values() {
        for block in &body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Stmt::Assign(_, Rvalue::New(cls)) => {
                        *alloc_count.entry(cls.clone()).or_insert(0) += 1;
                        if UNMODELLED_PRIMITIVES.contains(&cls.as_str()) {
                            return Err(Refusal::UnmodelledPrimitive(cls.clone()));
                        }
                    }
                    Stmt::Assign(_, Rvalue::Call { target, .. }) => {
                        if UNMODELLED_PRIMITIVES.contains(&target.class.as_str()) {
                            return Err(Refusal::UnmodelledPrimitive(target.class.clone()));
                        }
                    }
                    // Record which classes have their monitor taken. The
                    // operand is a local; resolving it to a class needs the
                    // same allocation tracking `threads::discover` does, so
                    // for now any monitor use makes every multi-allocated
                    // class suspect. Conservative in the safe direction: it
                    // can only cause a refusal, never a claim.
                    Stmt::MonitorEnter(Operand::Var(_)) => {
                        monitored.insert(String::from("*"));
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

    if monitored.contains("*") {
        if let Some((cls, n)) = alloc_count.iter().find(|(_, &n)| n > 1) {
            return Err(Refusal::AmbiguousMonitor(format!("{cls} ({n} sites)")));
        }
    }

    Ok(entries)
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
            bounds: Bounds::default(),
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
                // The exploration loop is not implemented yet. Publishing
                // nothing is correct: this engine may only ever publish
                // Violated, and it has not explored anything.
                debug!("concurrency: exploration not yet implemented; publishing nothing");
                Progress::Stalled
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
        // A CountDownLatch treated as a no-op would drop the ordering the
        // program relies on, letting us produce interleavings the JVM cannot —
        // a wrong FALSE for an Under engine.
        let mut prog = Program::default();
        prog.bodies.insert(
            mk("Main", "main", "()V"),
            body_with(
                vec![Stmt::Assign(
                    VarId(0),
                    Rvalue::Call {
                        target: mk("java/util/concurrent/CountDownLatch", "await", "()V"),
                        args: vec![Operand::Var(VarId(1))],
                        is_virtual: true,
                    },
                )],
                2,
            ),
        );
        match check_preconditions(&prog) {
            Err(Refusal::UnmodelledPrimitive(c)) => {
                assert!(c.contains("CountDownLatch"))
            }
            other => panic!("expected UnmodelledPrimitive, got {other:?}"),
        }
    }
}
