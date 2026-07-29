//! Tier 2, made real: bounded concrete execution over a small candidate set
//! for every `nondet` value, with exceptional control flow actually routed
//! through the handlers the frontend already computed.
//!
//! This is deliberately not full BMC -- there's no solver, no unrolling
//! variable, no SMT encoding. It is exactly the "self-certifying falsifier"
//! described early on: enumerate a handful of representative values
//! (0, ±1, extremes) rather than solving for one, execute the program for
//! real against each combination, and report a bug the moment a `Check`
//! fails somewhere the exception can't be caught. Because the values are
//! concrete, the witness is just "here is what we ran" -- no independent
//! trust in the engine is required to believe it, only the interpreter's own
//! determinism (and eventually `certify::JvmReplay`, which confirms even
//! that isn't required).
//!
//! The one piece of real semantic care here is exception routing: a
//! `DivByZero` or similar check failing inside a `try` block must transfer to
//! the matching handler, not be reported as a runtime-exception-property
//! violation -- getting this wrong is exactly how `ArithmeticException1`
//! (division caught, `assert false` in the handler) would be misjudged.

use std::collections::HashMap;

use log::{debug, info};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::verdict::Witness;
use roast_ir::*;
use roast_models as models;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Value {
    I32(i32),
    I64(i64),
    /// We don't track referential identity or heap contents; `bool` records
    /// only whether this reference is null. `New` produces `false`
    /// (non-null); unmodelled reference-producing calls default to
    /// non-null too -- an Under-approximating engine is allowed to miss the
    /// null-valued branch of a nondet reference, it just costs completeness.
    Ref(bool),
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
            Value::Ref(is_null) => !is_null,
            Value::Unknown => false,
        }
    }
}

const INT_CANDIDATES: [i32; 7] = [0, 1, -1, 2, -2, i32::MAX, i32::MIN];
// Not yet wired into `search`'s odometer, which only enumerates
// `INT_CANDIDATES` -- `Long` nondet values are currently always defaulted to
// 0 rather than varied. Kept visible (with the allow, rather than deleted)
// as a marker of a real gap: see "Known incompleteness" in
// docs/strategies/concrete.md.
#[allow(dead_code)]
const LONG_CANDIDATES: [i64; 5] = [0, 1, -1, i64::MAX, i64::MIN];

/// Outcome of running one concrete path to completion.
enum Outcome {
    /// Ran to a `Return` with nothing amiss.
    Clean,
    /// `Verifier.assume` failed: this path is uninteresting, not unsafe.
    Halted,
    /// A `Check` failed with nothing able to catch it.
    Violated {
        oid: ObligationId,
        witness: Vec<i64>,
    },
    /// Ran out of budget or hit something we can't interpret.
    Inconclusive,
}

/// The evaluator for everything except `Nondet`, which `run_with_choices`
/// intercepts before it ever reaches here (see the comment on that arm
/// below). Just a `store` -- no need for `prog`/`body` since arithmetic and
/// comparisons never look anything up beyond the variables already bound,
/// and no `steps_left` since evaluating a single rvalue is O(1), not
/// something that can itself run out of budget.
struct Run {
    store: HashMap<VarId, Value>,
}

impl Run {
    fn eval(&self, op: &Operand) -> Value {
        match op {
            Operand::Var(v) => self.store.get(v).copied().unwrap_or(Value::Unknown),
            Operand::Const(Const::Int(n)) => Value::I32(*n),
            Operand::Const(Const::Long(n)) => Value::I64(*n),
            Operand::Const(Const::Null) => Value::Ref(true),
            Operand::Const(_) => Value::Ref(false),
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
            Rvalue::New(cls) => {
                let _ = cls;
                Value::Ref(false)
            }
            Rvalue::NewArray { .. } => Value::Ref(false),
            Rvalue::GetStatic(_) | Rvalue::GetField { .. } | Rvalue::ArrayLoad { .. } => {
                Value::Unknown
            }
            Rvalue::ArrayLength(_) => Value::Unknown,
            Rvalue::InstanceOf { .. } => Value::I32(1),
            // A body containing a live, unmodelled call diverges at lift
            // time, so this arm is unreachable in practice on any body this
            // engine actually runs against -- but Value::Unknown is the
            // sound answer if it ever were reached, so it's handled rather
            // than left to panic.
            Rvalue::Call { .. } => Value::Unknown,
            Rvalue::Cast(ty, o) => match (ty, self.eval(o)) {
                (Ty::Int, Value::I64(v)) => Value::I32(v as i32),
                (Ty::Long, Value::I32(v)) => Value::I64(v as i64),
                (_, v) => v,
            },
            Rvalue::Cmp(a, b) => {
                let (x, y) = (self.eval(a).as_i64(), self.eval(b).as_i64());
                Value::I32(x.cmp(&y) as i32)
            }
            // Never reached: `run_with_choices` intercepts `Nondet` in the
            // `Assign` match before `eval_rvalue` is called, since picking a
            // candidate needs access to the choice vector and trace that live
            // outside this struct. Kept as an explicit arm rather than
            // omitted so a future refactor that routes `Nondet` through here
            // gets a compile error to fill in, not a silent gap.
            Rvalue::Nondet(_) => unreachable!("Nondet is handled in run_with_choices"),
        }
    }

    fn eval_bin(&self, op: BinOp, a: Value, b: Value) -> Value {
        use BinOp::*;
        let wide = matches!(a, Value::I64(_)) || matches!(b, Value::I64(_));
        match op {
            Eq | Ne | Lt | Le | Gt | Ge => {
                if let (Value::Ref(na), Value::Ref(nb)) = (a, b) {
                    let eq = na == nb; // both-null or both-non-null-as-unknown
                    return Value::I32(match op {
                        Eq => eq as i32,
                        Ne => !eq as i32,
                        _ => 0, // ordering on refs never occurs in our IR
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

/// Run the body once against a fully-predetermined sequence of nondet
/// choices. Choices beyond what's provided fall back to `0` / non-null,
/// which is why the outer search widens the candidate list on the values it
/// controls rather than needing true backtracking here.
fn run_with_choices(prog: &Program, body: &Body, choices: &[i64], step_budget: u64) -> Outcome {
    let mut store: HashMap<VarId, Value> = HashMap::new();
    let mut choice_idx = 0usize;
    let mut trace = Vec::new();
    let mut steps = step_budget;

    let mut block = body.entry;
    let mut idx = 0usize;

    loop {
        if steps == 0 {
            return Outcome::Inconclusive;
        }
        steps -= 1;

        let b = body.block(block);
        if idx >= b.stmts.len() {
            match &b.term {
                Terminator::Goto(t) => {
                    block = *t;
                    idx = 0;
                }
                Terminator::Branch { cond, then_, else_ } => {
                    let taken = store
                        .get(match cond {
                            Operand::Var(v) => v,
                            _ => unreachable!("branch cond is always a temp"),
                        })
                        .copied()
                        .unwrap_or(Value::Unknown)
                        .nonzero();
                    block = if taken { *then_ } else { *else_ };
                    idx = 0;
                }
                Terminator::Switch {
                    value,
                    cases,
                    default,
                } => {
                    let v = match value {
                        Operand::Var(vid) => store.get(vid).copied().unwrap_or(Value::Unknown),
                        other => Value::I32(match other {
                            Operand::Const(Const::Int(n)) => *n,
                            _ => 0,
                        }),
                    }
                    .as_i64() as i32;
                    block = cases
                        .iter()
                        .find(|(k, _)| *k == v)
                        .map(|(_, t)| *t)
                        .unwrap_or(*default);
                    idx = 0;
                }
                Terminator::Return(_) => return Outcome::Clean,
                Terminator::Halt => return Outcome::Halted,
                Terminator::Throw(v) => {
                    // A user-thrown (non-obligation) exception we don't
                    // recognise as AssertionError. Try to route it; if
                    // nothing catches it, this path taught us nothing about
                    // the properties we check, so it's inconclusive rather
                    // than a violation.
                    let _ = v;
                    return Outcome::Inconclusive;
                }
                Terminator::Diverge(_) => return Outcome::Inconclusive,
            }
            continue;
        }

        match &b.stmts[idx] {
            Stmt::Assign(v, rv) => {
                let val = match rv {
                    Rvalue::Nondet(ty) => {
                        let picked = choices.get(choice_idx).copied();
                        choice_idx += 1;
                        match (ty, picked) {
                            (Ty::Ref, _) => Value::Ref(false),
                            (Ty::Long, Some(c)) => {
                                trace.push(c);
                                Value::I64(c)
                            }
                            (Ty::Long, None) => {
                                trace.push(0);
                                Value::I64(0)
                            }
                            (_, Some(c)) => {
                                trace.push(c);
                                Value::I32(c as i32)
                            }
                            (_, None) => {
                                trace.push(0);
                                Value::I32(0)
                            }
                        }
                    }
                    other => {
                        let mut r = Run { store };
                        let val = r.eval_rvalue(other);
                        store = r.store;
                        val
                    }
                };
                store.insert(*v, val);
            }
            Stmt::Assume(op) => {
                let v = store
                    .get(match op {
                        Operand::Var(v) => v,
                        _ => unreachable!("assume operand is always a temp"),
                    })
                    .copied()
                    .unwrap_or(Value::Unknown);
                if !v.nonzero() {
                    return Outcome::Halted;
                }
            }
            Stmt::PutStatic(..) | Stmt::PutField { .. } | Stmt::ArrayStore { .. } => {
                // No heap model: writes are dropped. Sound for an
                // under-approximating engine (we simply won't find bugs that
                // depend on a written-then-read value), never unsound.
            }
            Stmt::Check(oid) => {
                let ob = body.obligation(*oid);
                let ok = match &ob.cond {
                    Operand::Const(Const::Int(v)) => *v != 0,
                    other => {
                        let v = match other {
                            Operand::Var(vid) => store.get(vid).copied().unwrap_or(Value::Unknown),
                            _ => Value::Unknown,
                        };
                        v.nonzero()
                    }
                };
                if !ok {
                    // Assertion obligations are never routed: reaching the
                    // failing assert location is the property violation
                    // itself, independent of any handler.
                    if let Some(class) = models::exception_class(ob.kind) {
                        if let Some(target) = route(prog, b, class) {
                            block = target;
                            idx = 0;
                            // Handler blocks are entered with the exception
                            // object at stack height 1; we don't need its
                            // identity, only that it's a non-null reference.
                            if let Some(slot) = body
                                .vars
                                .iter()
                                .enumerate()
                                .find(|(_, vi)| vi.kind == VarKind::Stack(0))
                                .map(|(i, _)| VarId(i as u32))
                            {
                                store.insert(slot, Value::Ref(false));
                            }
                            continue;
                        }
                    }
                    return Outcome::Violated {
                        oid: *oid,
                        witness: trace,
                    };
                }
            }
            Stmt::Nop => {}
        }
        idx += 1;
    }
}

/// Widen the candidate assignment at position `slot` in a fixed-length choice
/// vector, enumerating combinations depth-first up to `budget` total runs.
/// This is brute force, deliberately: no solver, no path merging, just enough
/// search to catch the shapes of bug this benchmark set actually contains.
fn search(prog: &Program, body: &Body, budget: u64) -> Vec<(ObligationId, Witness)> {
    let mut found = Vec::new();
    let mut runs_left = budget;

    // Discover how many nondet slots exist by running once with no choices
    // available (all default to 0) up to a generous step budget, counting
    // how many were consumed. Programs with a variable number of nondet
    // calls on different paths are handled by just re-running per candidate
    // vector and letting `run_with_choices` fall back to 0 past the end.
    let probe_steps = 200_000u64;
    let mut probe_choices: Vec<i64> = Vec::new();
    let slots = count_nondet_slots(prog, body, probe_steps, &mut probe_choices);

    if slots == 0 {
        // Fully deterministic: one run tells the whole story, and there's no
        // budget left to account for since we're returning immediately.
        if let Outcome::Violated { oid, witness } = run_with_choices(prog, body, &[], probe_steps) {
            found.push((
                oid,
                Witness {
                    nondet_sequence: witness,
                },
            ));
        }
        return found;
    }

    // Cartesian product over a capped number of slots, each drawn from a
    // small candidate pool. Capped at a handful of slots to keep this
    // "minimal": beyond that the combinatorics need real search, which is
    // exactly where a solver-backed BMC tier belongs instead.
    let capped = slots.min(4);
    let pool: Vec<i64> = INT_CANDIDATES.iter().map(|x| *x as i64).collect();
    let mut idxs = vec![0usize; capped];

    'outer: loop {
        if runs_left == 0 {
            break;
        }
        runs_left -= 1;

        let choices: Vec<i64> = idxs.iter().map(|i| pool[*i]).collect();
        if let Outcome::Violated { oid, witness } =
            run_with_choices(prog, body, &choices, probe_steps)
        {
            found.push((
                oid,
                Witness {
                    nondet_sequence: witness,
                },
            ));
        }

        // Odometer increment.
        let mut k = capped;
        loop {
            if k == 0 {
                break 'outer;
            }
            k -= 1;
            idxs[k] += 1;
            if idxs[k] < pool.len() {
                break;
            }
            idxs[k] = 0;
        }
    }

    found
}

/// Run once with an empty choice vector (every nondet defaults to 0) purely
/// to count how many nondet call sites are on the taken path, so `search`
/// knows how many odometer slots to enumerate.
fn count_nondet_slots(prog: &Program, body: &Body, steps: u64, out: &mut Vec<i64>) -> usize {
    match run_with_choices(prog, body, &[], steps) {
        Outcome::Violated { witness, .. } => {
            *out = witness.clone();
            witness.len()
        }
        _ => {
            // No violation on the all-zero path; we still need a slot count.
            // Re-run counting via a sentinel-free trace by reusing the
            // Halted/Clean path's implicit trace length isn't available
            // (Outcome doesn't carry it), so fall back to a fixed small
            // guess. This is the one place this engine trades precision for
            // simplicity: under-counting slots only means fewer combinations
            // get tried, which costs completeness, not soundness.
            3
        }
    }
}

pub struct Concrete {
    done: bool,
    budget_runs: u64,
}

impl Concrete {
    pub fn new(budget_runs: u64) -> Self {
        Concrete {
            done: false,
            budget_runs,
        }
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

        info!("concrete: starting bounded search (budget={} runs) on {entry:?}", self.budget_runs);
        let violations = search(prog, body, self.budget_runs);
        debug!("concrete: search complete, found {} violation(s)", violations.len());

        let mut advanced = false;
        for (oid, witness) in violations {
            let oref = ObligationRef {
                method: entry.clone(),
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
