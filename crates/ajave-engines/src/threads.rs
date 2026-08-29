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
pub fn discover(prog: &Program) -> ThreadDiscovery {
    let mut entries = Vec::new();
    let mut saw_start = false;

    for (caller, body) in &prog.bodies {
        // Which local holds which freshly-allocated class, within this body.
        // Deliberately intra-procedural and flow-insensitive over a single
        // body: enough for the idiomatic shape, and it fails closed elsewhere.
        let mut alloc_class: HashMap<VarId, String> = HashMap::new();
        // Thread object -> class whose `run()` it will execute.
        let mut thread_runnable: HashMap<VarId, String> = HashMap::new();

        for block in &body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Stmt::Assign(v, Rvalue::New(class)) => {
                        alloc_class.insert(*v, class.clone());
                    }
                    // Copy propagation: `v = w` carries the allocation through
                    // the temporaries javac introduces around `new`.
                    Stmt::Assign(v, Rvalue::Use(Operand::Var(src))) => {
                        if let Some(c) = alloc_class.get(src).cloned() {
                            alloc_class.insert(*v, c);
                        }
                        if let Some(c) = thread_runnable.get(src).cloned() {
                            thread_runnable.insert(*v, c);
                        }
                    }
                    Stmt::Assign(_, Rvalue::Call { target, args, .. }) => {
                        if target.class == "java/lang/Thread" && target.name == "<init>" {
                            // Receiver is arg 0; the Runnable, if any, is arg 1.
                            let recv = match args.first() {
                                Some(Operand::Var(v)) => *v,
                                _ => continue,
                            };
                            match args.get(1) {
                                Some(Operand::Var(r)) => {
                                    if let Some(c) = alloc_class.get(r).cloned() {
                                        thread_runnable.insert(recv, c);
                                    } else {
                                        return ThreadDiscovery::Unresolved(format!(
                                            "{caller}: Thread constructed from a Runnable \
                                             this analysis cannot resolve to an allocation"
                                        ));
                                    }
                                }
                                Some(Operand::Const(Const::Null)) => {
                                    // `new Thread(null)` — run() does nothing.
                                }
                                None => {
                                    // `new Thread()`: the body is the receiver's
                                    // own `run()`, i.e. a Thread subclass.
                                    if let Some(c) = alloc_class.get(&recv).cloned() {
                                        thread_runnable.insert(recv, c);
                                    }
                                }
                                _ => {}
                            }
                        } else if target.class == "java/lang/Thread" && target.name == "start" {
                            saw_start = true;
                            let recv = match args.first() {
                                Some(Operand::Var(v)) => *v,
                                _ => {
                                    return ThreadDiscovery::Unresolved(format!(
                                        "{caller}: start() on a receiver that is not a local"
                                    ))
                                }
                            };
                            let Some(class) = thread_runnable.get(&recv).cloned() else {
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
                            entries.push(ThreadEntry {
                                run,
                                started_from: caller.clone(),
                            });
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
    entries.sort_by(|a, b| a.run.to_string().cmp(&b.run.to_string()));
    entries.dedup();
    ThreadDiscovery::Resolved(entries)
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
