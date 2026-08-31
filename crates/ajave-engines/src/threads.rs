//! Static discovery of thread entry points.
//!
//! Before anything can explore interleavings it has to know *which* bodies run
//! concurrently. That is a points-to question in general — which `Runnable` did
//! this `Thread` get? — and ajave has no points-to analysis. But the shape that
//! actually appears in Java programs is narrow enough to resolve exactly:
//!
//! ```java
//! Thread t = new Thread(new Worker());   // argument is a fresh allocation
//! t.start();
//! ```
//!
//! so we resolve that shape precisely and report *failure* for anything else,
//! rather than guessing.
//!
//! # Why precision matters here, and in which direction
//!
//! A concurrency explorer is an **Under** engine: it may publish `Violated`,
//! never `Discharged`. That makes over-approximating the thread set unsound in
//! the dangerous direction — exploring a thread that never actually starts
//! would let us report a violation in code that never runs, which is a wrong
//! FALSE (−32).
//!
//! The usual "be conservative, over-approximate" instinct is therefore exactly
//! backwards for this analysis. Under-approximating is the safe failure mode:
//! we miss bugs (costing precision) rather than inventing them.
//!
//! So `discover` returns `Unresolved` whenever it cannot pin the body down, and
//! callers must treat that as "cannot analyse this program" rather than
//! "no threads".

use std::collections::HashMap;

use ajave_ir::{Const, MethodKey, Operand, Program, Rvalue, Stmt, VarId};

/// A thread whose body we resolved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThreadEntry {
    /// The `run()` body that executes on this thread.
    pub run: MethodKey,
    /// The method containing the `start()` call that creates it.
    pub started_from: MethodKey,
}

/// What `discover` found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThreadDiscovery {
    /// No thread is ever started; the program is sequential.
    Sequential,
    /// Every `start()` was resolved to a concrete `run()` body.
    Resolved(Vec<ThreadEntry>),
    /// At least one `start()` could not be resolved. Carries a human-readable
    /// reason, which is worth surfacing: an engine that declines to analyse a
    /// program should be able to say why.
    Unresolved(String),
}

/// Find every thread body the program can start.
///
/// Handles the two idiomatic constructions:
///
/// * `new Thread(new Worker())` — the body is `Worker.run()`.
/// * `new MyThread()` where `MyThread extends Thread` — the body is
///   `MyThread.run()`.
///
/// Anything else (a `Runnable` from a field, a factory, an array, a lambda that
/// did not lift to a concrete class) yields `Unresolved`.
/// Classes whose `execute`/`submit` starts a task on a pooled thread.
pub fn is_executor(class: &str) -> bool {
    matches!(
        class,
        "java/util/concurrent/ExecutorService"
            | "java/util/concurrent/Executor"
            | "java/util/concurrent/ScheduledExecutorService"
            | "java/util/concurrent/ThreadPoolExecutor"
            | "java/util/concurrent/AbstractExecutorService"
    )
}

/// Is `class` `java/lang/Thread` or a subclass?
///
/// `class W extends Thread` makes javac emit `invokevirtual Main$W.start()` --
/// the declared type -- so testing for `java/lang/Thread` by equality sees no
/// thread start at all and the program is classified sequential.
pub fn is_thread_class(prog: &Program, class: &str) -> bool {
    if class == "java/lang/Thread" {
        return true;
    }
    let mut cur = class.to_string();
    for _ in 0..64 {
        match prog.supers.get(&cur) {
            Some(sup) if sup == "java/lang/Thread" => return true,
            Some(sup) => cur = sup.clone(),
            None => return false,
        }
    }
    false
}

pub fn discover(prog: &Program) -> ThreadDiscovery {
    // (declaring method, position within it, entry). Threads are identified at
    // run time in construction order, so entries must preserve multiplicity;
    // `prog.bodies` is a HashMap, so the pair is also what makes the order
    // deterministic across runs.
    let mut pending: Vec<(String, usize, ThreadEntry)> = Vec::new();
    let mut ordinal: usize = 0;
    let mut saw_start = false;

    for (caller, body) in &prog.bodies {
        // Track *allocation identity*, not variable identity.
        //
        // javac routes a `new` through several temporaries before it reaches
        // the named local, so `v0`, `v2`, `v3` and `v5` all denote the same
        // Thread. Keying the Runnable on the variable that happened to be the
        // receiver of `<init>` therefore loses it by the time `start()` is
        // called on a different alias — which is exactly how the first version
        // of this failed on every benchmark.
        //
        // Each `new` gets an id; copies carry the id; the Runnable is recorded
        // against the id.
        let mut var_alloc: HashMap<VarId, u32> = HashMap::new();
        let mut alloc_class: HashMap<u32, String> = HashMap::new();
        let mut alloc_runnable: HashMap<u32, String> = HashMap::new();
        let mut next_alloc: u32 = 0;

        for block in &body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Stmt::Assign(v, Rvalue::New(class)) => {
                        next_alloc += 1;
                        var_alloc.insert(*v, next_alloc);
                        alloc_class.insert(next_alloc, class.clone());
                    }
                    // Copy propagation: `v = w` denotes the same allocation.
                    Stmt::Assign(v, Rvalue::Use(Operand::Var(src))) => {
                        if let Some(a) = var_alloc.get(src).copied() {
                            var_alloc.insert(*v, a);
                        }
                    }
                    Stmt::Assign(_, Rvalue::Call { target, args, .. }) => {
                        if target.class == "java/lang/Thread" && target.name == "<init>" {
                            // Receiver is arg 0; the Runnable, if any, is arg 1.
                            let recv = match args.first() {
                                Some(Operand::Var(v)) => *v,
                                _ => continue,
                            };
                            let Some(recv_alloc) = var_alloc.get(&recv).copied() else {
                                return ThreadDiscovery::Unresolved(format!(
                                    "{caller}: Thread.<init> on a receiver not traced to \
                                     an allocation"
                                ));
                            };
                            match args.get(1) {
                                Some(Operand::Var(r)) => {
                                    let cls = var_alloc
                                        .get(r)
                                        .and_then(|a| alloc_class.get(a))
                                        .cloned();
                                    match cls {
                                        Some(c) => {
                                            alloc_runnable.insert(recv_alloc, c);
                                        }
                                        None => {
                                            return ThreadDiscovery::Unresolved(format!(
                                                "{caller}: Thread constructed from a Runnable \
                                                 this analysis cannot resolve to an allocation"
                                            ))
                                        }
                                    }
                                }
                                Some(Operand::Const(Const::Null)) => {
                                    // `new Thread(null)` still consumes a
                                    // thread identity at run time but has no
                                    // body to give an entry, so the entry list
                                    // and the identities would no longer
                                    // correspond. Refuse rather than silently
                                    // analyse the wrong number of threads.
                                    return ThreadDiscovery::Unresolved(format!(
                                        "{caller}: new Thread(null) has no body to model"
                                    ));
                                }
                                None => {
                                    // `new Thread()`: a Thread subclass, so the
                                    // body is the receiver's own `run()`.
                                    if let Some(c) = alloc_class.get(&recv_alloc).cloned() {
                                        alloc_runnable.insert(recv_alloc, c);
                                    }
                                }
                                _ => {}
                            }
                            // One entry per construction. Two `new Thread(new W())`
                            // are two threads even though both run `W.run`, so
                            // the entry cannot be keyed on the run method.
                            if let Some(cls) = alloc_runnable.get(&recv_alloc).cloned() {
                                let run = MethodKey {
                                    class: cls,
                                    name: "run".to_string(),
                                    desc: "()V".to_string(),
                                };
                                if prog.body(&run).is_none() {
                                    return ThreadDiscovery::Unresolved(format!(
                                        "{caller}: resolved thread body {run} has no lifted body"
                                    ));
                                }
                                pending.push((caller.to_string(), ordinal, ThreadEntry {
                                    run,
                                    started_from: caller.clone(),
                                }));
                                ordinal += 1;
                            }
                        } else if is_executor(&target.class)
                            && (target.name == "execute" || target.name == "submit")
                        {
                            // A task submitted to a pool is a thread whose
                            // start() is hidden inside the library. Without
                            // this the program has no visible start() at all
                            // and is classified sequential -- told there is no
                            // concurrency in a program that is entirely about
                            // concurrency.
                            saw_start = true;
                            if !target.desc.starts_with("(Ljava/lang/Runnable;)") {
                                // `submit(Callable)` returns a value the task
                                // computes, which needs the Future to carry a
                                // result rather than just an ordering.
                                return ThreadDiscovery::Unresolved(format!(
                                    "{caller}: only submit/execute of a Runnable is modelled"
                                ));
                            }
                            let Some(Operand::Var(r)) = args.get(1) else {
                                return ThreadDiscovery::Unresolved(format!(
                                    "{caller}: task argument is not a local"
                                ));
                            };
                            let Some(cls) =
                                var_alloc.get(r).and_then(|a| alloc_class.get(a)).cloned()
                            else {
                                return ThreadDiscovery::Unresolved(format!(
                                    "{caller}: submitted task could not be traced to an allocation"
                                ));
                            };
                            let run = MethodKey {
                                class: cls,
                                name: "run".to_string(),
                                desc: "()V".to_string(),
                            };
                            if prog.body(&run).is_none() {
                                return ThreadDiscovery::Unresolved(format!(
                                    "{caller}: submitted task body {run} has no lifted body"
                                ));
                            }
                            pending.push((
                                caller.to_string(),
                                ordinal,
                                ThreadEntry { run, started_from: caller.clone() },
                            ));
                            ordinal += 1;
                        } else if is_thread_class(prog, &target.class) && target.name == "start" {
                            saw_start = true;
                            let recv = match args.first() {
                                Some(Operand::Var(v)) => *v,
                                _ => {
                                    return ThreadDiscovery::Unresolved(format!(
                                        "{caller}: start() on a receiver that is not a local"
                                    ))
                                }
                            };
                            let Some(class) = var_alloc
                                .get(&recv)
                                .and_then(|a| alloc_runnable.get(a))
                                .cloned()
                            else {
                                return ThreadDiscovery::Unresolved(format!(
                                    "{caller}: start() on a Thread whose body could not be \
                                     traced to an allocation in this method"
                                ));
                            };
                            let run = MethodKey {
                                class: class.clone(),
                                name: "run".to_string(),
                                desc: "()V".to_string(),
                            };
                            if prog.body(&run).is_none() {
                                return ThreadDiscovery::Unresolved(format!(
                                    "{caller}: resolved thread body {run} has no lifted body"
                                ));
                            }
                            // The entry was recorded at construction; this
                            // branch only checks that the body is resolvable
                            // from here, and that a start() we cannot trace
                            // refuses rather than being ignored.
                            let _ = run;
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    if !saw_start {
        return ThreadDiscovery::Sequential;
    }
    // Sorted for determinism only. Which body each thread actually runs is
    // decided at `start()` from the Runnable object itself, so this order no
    // longer carries meaning -- it used to, and pairing a sorted list against
    // construction-ordered identities gave one thread another's body.
    //
    // Deliberately no `dedup()`: it collapsed two threads running the same
    // run() into one, so a program starting two identical workers was analysed
    // as starting one. `TwoWorkersSameClass` was reported FALSE on that basis.
    pending.sort_by(|a, b| (&a.0, a.1).cmp(&(&b.0, b.1)));
    ThreadDiscovery::Resolved(pending.into_iter().map(|(_, _, e)| e).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::{Block, BlockId, Body, Terminator, Ty, VarInfo, VarKind};

    fn mk(class: &str, name: &str) -> MethodKey {
        MethodKey {
            class: class.into(),
            name: name.into(),
            desc: "()V".into(),
        }
    }

    /// A body with the given statements in one block.
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

    #[test]
    fn no_threads_is_sequential() {
        let mut prog = Program::default();
        prog.bodies.insert(mk("Main", "main"), body_with(vec![], 1));
        assert_eq!(discover(&prog), ThreadDiscovery::Sequential);
    }

    #[test]
    fn unresolvable_start_is_not_reported_as_sequential() {
        // `start()` on a receiver we never saw allocated. Reporting Sequential
        // here would be the dangerous failure: an explorer would conclude
        // there are no threads and analyse the program as single-threaded.
        let mut prog = Program::default();
        prog.bodies.insert(
            mk("Main", "main"),
            body_with(
                vec![Stmt::Assign(
                    VarId(0),
                    Rvalue::Call {
                        target: MethodKey {
                            class: "java/lang/Thread".into(),
                            name: "start".into(),
                            desc: "()V".into(),
                        },
                        args: vec![Operand::Var(VarId(1))],
                        is_virtual: true,
                    },
                )],
                2,
            ),
        );
        match discover(&prog) {
            ThreadDiscovery::Unresolved(_) => {}
            other => panic!("expected Unresolved, got {other:?}"),
        }
    }
}
