//! Concolic execution: run the program for real, then ask the solver for the
//! input that would have taken the other branch.
//!
//! # Why this exists
//!
//! Forward symbolic execution enters a call with whatever it knows *at that
//! point*. When the fact that pins the input lies downstream of the call, it
//! knows nothing, and a recursive callee forks until its budget is gone. The
//! `jayhorn-recursive` `Unsat*` tasks are exactly this shape:
//!
//! ```java
//! int x = Verifier.nondetInt();
//! int result = fibonacci(x);      // explored with x unconstrained: exponential
//! if (x != 5 || result == 3) return; else assert false;
//! ```
//!
//! Measured 2026-09-06: moving `if (x != 5) return;` *above* the call turns
//! UNKNOWN into FALSE, with no other change. Raising the fork budget eightfold
//! does nothing. So the blocker is evaluation order, not budget or solver.
//!
//! Concolic execution inverts the roles. The concrete run decides control flow
//! -- `fibonacci(5)` is a handful of additions, not an exponential tree -- and
//! the solver only ever sees the branch conditions along one path, which are
//! small. Flipping the last unflipped branch and solving gives the next input.
//! This is the DART/CUTE loop (Godefroid et al. 2005, Sen et al. 2005).
//!
//! # What it may conclude
//!
//! `Direction::Under`, and it earns that in the strongest way available: a
//! violation is reported only when a *real execution* reached the check and
//! the check failed. The witness is the input that execution ran on, so it
//! reproduces by construction. The solver is used only to *propose* inputs;
//! it never decides that something is violated.
//!
//! That is what makes an incomplete symbolic shadow harmless. `sym_rvalue`
//! declines anything it cannot model faithfully -- integer division, which is
//! Euclidean in SMT and truncating in Java, and every bitwise operator, which
//! LIA does not have. Declining loses flips and therefore paths; it cannot
//! produce a wrong answer, because the concrete run is the arbiter.

use std::collections::BTreeSet;
use std::io::Write;
use std::process::{Command, Stdio};

use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_ir::verdict::Witness;
use ajave_ir::*;
use log::{debug, info};

use crate::concrete::{run_concolic, Outcome, PathCond};

/// How many inputs to try. Each costs one concrete run and one solver call.
///
/// A fitted constant, and recorded as such: it was chosen as "enough to walk a
/// handful of guards deep", not by raising it until a benchmark passed. The
/// loop stops early whenever the queue empties, which is the common case on
/// small entry methods.
const MAX_ITERATIONS: usize = 60;

/// Cap on how many branches from one path get flipped, so a single long run
/// cannot monopolise the iteration budget.
const MAX_FLIPS_PER_PATH: usize = 24;

/// Wall-clock budget for the whole search.
///
/// The iteration cap alone is not a cost bound: each run executes the program
/// concretely, and a loop over a nondeterministic bound can be arbitrarily
/// long. Measured on `jbmc-regression/aastore_aaload1`, which fills an array
/// of nondeterministic size: concolic spent **13.3 seconds** and discharged
/// nothing, while `chc` proved the task in 39ms. The engine is speculative, so
/// it gets a speculative budget and stops when it runs out.
const TIME_BUDGET: std::time::Duration = std::time::Duration::from_millis(2000);

pub struct Concolic {
    solver_binary: String,
    done: bool,
}

impl Default for Concolic {
    fn default() -> Self {
        Self::new()
    }
}

impl Concolic {
    pub fn new() -> Self {
        Concolic {
            solver_binary: std::env::var("ROAST_SMT_SOLVER").unwrap_or_else(|_| "z3".to_string()),
            done: false,
        }
    }

    /// Run one satisfiability query and return the solver's raw reply.
    fn ask(&self, smt: &str) -> Option<String> {
        let mut child = Command::new(&self.solver_binary)
            .args(["-in", "-smt2", "-T:5"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .ok()?;
        child.stdin.as_mut()?.write_all(smt.as_bytes()).ok()?;
        let out = child.wait_with_output().ok()?;
        Some(String::from_utf8_lossy(&out.stdout).into_owned())
    }

    /// Ask for an assignment that follows `path[..i]` and then flips `path[i]`.
    ///
    /// Inputs are constrained to the `int` range: an unbounded model would
    /// propose a value no Java `int` can hold, and the concrete run would then
    /// execute something the JVM never could.
    fn solve_flip(
        &self,
        path: &[PathCond],
        i: usize,
        inputs: &BTreeSet<usize>,
    ) -> Option<Vec<i64>> {
        let mut smt = String::from("(set-logic QF_LIA)\n");
        for idx in inputs {
            smt.push_str(&format!("(declare-const n{} Int)\n", idx));
            smt.push_str(&format!(
                "(assert (and (<= (- 2147483648) n{0}) (<= n{0} 2147483647)))\n",
                idx
            ));
        }
        for (j, c) in path.iter().enumerate().take(i + 1) {
            // Every condition before the flip keeps the polarity the concrete
            // run took; the flipped one is negated.
            let want = if j == i { !c.taken } else { c.taken };
            smt.push_str(&format!(
                "(assert {})\n",
                if want {
                    c.text.clone()
                } else {
                    format!("(not {})", c.text)
                }
            ));
        }
        smt.push_str("(check-sat)\n(get-model)\n");

        let out = self.ask(&smt)?;
        if !out.starts_with("sat") {
            return None;
        }
        // Read `(define-fun nK () Int V)` back out of the model.
        let max = inputs.iter().copied().max().unwrap_or(0);
        let mut choices = vec![0i64; max + 1];
        for idx in inputs {
            if let Some(v) = model_value(&out, &format!("n{}", idx)) {
                choices[*idx] = v;
            }
        }
        Some(choices)
    }
}

/// Pull `nK`'s value out of an SMT-LIB model. Negative values print as
/// `(- 5)`, which a naive parse reads as zero.
fn model_value(model: &str, name: &str) -> Option<i64> {
    let at = model.find(&format!("define-fun {} ", name))?;
    let rest = &model[at..];
    let close = rest.find(')')?;
    let tail = rest[close + 1..].trim_start();
    let tail = tail.strip_prefix("Int").unwrap_or(tail).trim_start();
    if let Some(neg) = tail.strip_prefix("(-") {
        let digits: String = neg
            .trim_start()
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        return digits.parse::<i64>().ok().map(|v| -v);
    }
    let digits: String = tail
        .chars()
        .take_while(|c| c.is_ascii_digit() || *c == '-')
        .collect();
    digits.parse::<i64>().ok()
}

impl Engine for Concolic {
    fn id(&self) -> EngineId {
        EngineId("concolic")
    }

    fn direction(&self) -> Direction {
        Direction::Under
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let (Some(entry), Some(body)) = (
            prog.entry.as_ref(),
            prog.entry.as_ref().and_then(|e| prog.body(e)),
        ) else {
            return Progress::Exhausted;
        };

        let step_budget = 200_000u64;
        // Breadth-first over inputs, starting from the all-zero probe so the
        // first run is the one `concrete` already does.
        let mut queue: Vec<Vec<i64>> = vec![Vec::new()];
        let mut seen: BTreeSet<Vec<i64>> = BTreeSet::new();
        let mut advanced = false;
        let mut runs = 0usize;
        let started = std::time::Instant::now();

        info!("concolic: exploring from {entry:?}");

        while let Some(choices) = queue.pop() {
            if runs >= MAX_ITERATIONS {
                debug!("concolic: stopping at the {MAX_ITERATIONS}-run cap");
                break;
            }
            if started.elapsed() > TIME_BUDGET {
                debug!(
                    "concolic: stopping after {:?}, past the {TIME_BUDGET:?} budget",
                    started.elapsed()
                );
                break;
            }
            if !seen.insert(choices.clone()) {
                continue;
            }
            runs += 1;

            let (outcome, path, inputs) = run_concolic(prog, body, &choices, step_budget);

            if let Outcome::Violated {
                method,
                oid,
                witness,
                entries,
            } = outcome
            {
                // A real execution reached this check and it failed, so the
                // inputs it ran on are a witness, not a candidate.
                let oref = ObligationRef { method, id: oid };
                info!("concolic: violation at {oref:?} after {runs} run(s), choices={choices:?}");
                let published = bb.publish(
                    self.id(),
                    self.direction(),
                    Artifact::Status(
                        oref,
                        Status::Violated {
                            by: self.id(),
                            witness: Witness {
                                nondet_sequence: witness,
                                entries,
                                schedule: Vec::new(),
                                choices: Vec::new(),
                            },
                        },
                    ),
                );
                if published.is_ok() {
                    advanced = true;
                }
                continue;
            }

            if inputs.is_empty() {
                continue; // nothing symbolic: no other input can change anything
            }

            // Flip the deepest branches first: those are the ones the previous
            // runs have not already explored around.
            let flips = path.len().min(MAX_FLIPS_PER_PATH);
            for i in (path.len().saturating_sub(flips)..path.len()).rev() {
                if let Some(next) = self.solve_flip(&path, i, &inputs) {
                    queue.push(next);
                }
            }
        }

        debug!("concolic: {runs} run(s), advanced={advanced}");
        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}
