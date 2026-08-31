//! Search-based floating-point falsification.
//!
//! # Why an SMT solver cannot do this
//!
//! The `float-nonlinear-calculation` corpus is dominated by transcendentals —
//! 173 uses of `Math.sin`, 100 of `cos`, 91 of `log`, 82 of `pow`, 62 of
//! `sqrt`, 61 of `atan`. **SMT-LIB's FloatingPoint theory has no transcendental
//! functions.** There is no `fp.sin`. So no amount of FPA encoding can decide
//! these obligations.
//!
//! Solving over the reals instead (what the NRA engine does with cvc5) finds
//! answers that are correct over ℝ but not over IEEE-754, so the witness fails
//! JVM replay and the point is withdrawn. And `Math.sin` is specified only to
//! within 1 ulp and need not be correctly rounded, so there is no unique
//! symbolic answer to find: **the JVM is the ground truth**.
//!
//! These benchmarks come from `concolic-walk` and `jpf-symbc`, which exist
//! precisely to be solved by search rather than by symbolic reasoning.
//!
//! # The approach
//!
//! Run the program concretely on candidate inputs and search for inputs that
//! reach a violation, guided by how close each run came. This is the
//! Alternating Variable Method (Korel), the search used by FloPSy and CORAL for
//! floating-point path conditions:
//!
//! 1. Seed from a handful of values programs actually branch on.
//! 2. Take one variable at a time. Probe both directions; on an improvement,
//!    accelerate in that direction with a geometrically growing step.
//! 3. When no variable improves, restart from a new random seed.
//!
//! Fitness is the smallest relative distance to equality seen at any float
//! comparison during the run (`Run::min_cmp_distance`). The guards here are
//! overwhelmingly `if (expr == 0.0) { assert false; }`, so driving that
//! distance to zero is exactly the objective.
//!
//! # Soundness
//!
//! This is an under-approximating engine and may only publish violations. It
//! publishes **only** when a concrete run actually reached the obligation and
//! failed it — the interpreter executing the real program *is* the semantics,
//! so a witness cannot be spurious by construction. Failing to find one costs
//! precision, never correctness. It never discharges anything.
//!
//! There are no hardcoded trigger values: seeds are ordinary boundary constants
//! (0, ±1, small integers) and everything else is derived by search from the
//! program's own behaviour. Nothing here recognises a benchmark.

use ajave_core::artifact::{Artifact, Direction, EngineId, ObligationRef};
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_ir::verdict::{NondetEntry, Witness};
use ajave_ir::{Body, MethodKey, ObligationId, Program, Ty};
use log::{debug, info};

use crate::concrete::{run_with_fitness, Outcome};

/// Concrete steps per candidate run. These programs are small; a candidate that
/// needs more than this is not the shape this engine targets.
const STEP_BUDGET: u64 = 100_000;

/// Total candidate evaluations. Each is a full concrete run, so this is the
/// engine's real cost. Deliberately modest: this runs after the cheaper engines
/// have already failed.
const MAX_EVALS: usize = 300_000;

/// Values programs actually branch on. Not benchmark-derived — these are the
/// boundaries any numeric code tends to have.
const SEEDS: [f64; 9] = [0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 10.0, -10.0];

pub struct FloatSearch;

impl Default for FloatSearch {
    fn default() -> Self {
        Self::new()
    }
}

impl FloatSearch {
    pub fn new() -> FloatSearch {
        FloatSearch
    }
}

/// What each nondet slot this body draws is: 64-bit double, 32-bit float, or
/// not a float at all.
///
/// The width matters and getting it wrong is a soundness hazard, not a
/// precision one. The replay harness decodes a `nondetFloat` as
/// `Float.intBitsToFloat((int) next())` — the *low 32 bits* — so writing a
/// 64-bit double pattern into the sequence means the engine and the JVM run the
/// program on different values. That produced a confirmed-but-bogus violation
/// on `argv-tasks/ReverseInterpolator_true`: the search used -3.88e9 while the
/// JVM replayed 18.145, and the resulting wrong FALSE cost -32.
///
/// Only float slots are searched; integer slots stay at whatever the seed gave
/// them, because the SMT engine already handles integer path conditions well.
#[derive(Clone, Copy, PartialEq)]
enum Slot {
    Double,
    Float,
    NotFloat,
}

fn nondet_slots(body: &Body) -> Vec<Slot> {
    let mut slots = Vec::new();
    for block in &body.blocks {
        for st in &block.stmts {
            if let ajave_ir::Stmt::Assign(_, ajave_ir::Rvalue::Nondet(ty, _)) = st {
                slots.push(match ty {
                    Ty::Double => Slot::Double,
                    Ty::Float => Slot::Float,
                    _ => Slot::NotFloat,
                });
            }
        }
    }
    slots
}

fn encode(vals: &[f64], slots: &[Slot]) -> Vec<i64> {
    vals.iter()
        .zip(slots)
        .map(|(v, s)| match s {
            Slot::Double => v.to_bits() as i64,
            // 32 bits, because that is what the JVM will read back.
            Slot::Float => (*v as f32).to_bits() as i32 as i64,
            Slot::NotFloat => *v as i64,
        })
        .collect()
}

/// The next representable double from `v` toward `dir`'s infinity.
///
/// Exact float equality is reached one representable value at a time; an
/// arithmetic step of any fixed size may step straight over the solution.
fn next_after(v: f64, dir: f64) -> f64 {
    if v.is_nan() {
        return v;
    }
    if v == 0.0 {
        return if dir > 0.0 { f64::from_bits(1) } else { -f64::from_bits(1) };
    }
    let bits = v.to_bits() as i64;
    let up = (v > 0.0) == (dir > 0.0);
    let next = if up { bits + 1 } else { bits - 1 };
    f64::from_bits(next as u64)
}

struct Candidate {
    vals: Vec<f64>,
    fitness: f64,
    /// Signed gap at the closest comparison; see `Run::min_cmp_signed`.
    signed: f64,
    hit: Option<(MethodKey, ObligationId, Vec<i64>, Vec<NondetEntry>)>,
}

fn evaluate(prog: &Program, body: &Body, vals: &[f64], slots: &[Slot]) -> Candidate {
    let choices = encode(vals, slots);
    let (out, fitness, signed) = run_with_fitness(prog, body, &choices, STEP_BUDGET);
    let hit = match out {
        Outcome::Violated { method, oid, witness, entries } => {
            Some((method, oid, witness, entries))
        }
        _ => None,
    };
    Candidate { vals: vals.to_vec(), fitness, signed, hit }
}

/// Find a value of variable `i` that drives the compared expression to exactly
/// zero, by bracketing a sign change and bisecting the representable doubles.
fn bisect(
    prog: &Program,
    body: &Body,
    slots: &[Slot],
    cur: &[f64],
    i: usize,
    best: &Candidate,
    evals: &mut usize,
) -> Option<Candidate> {
    // Walk outward until the sign of the gap flips: that brackets a root.
    let sign0 = best.signed.signum();
    let mut hi = cur[i];
    let mut found = false;
    let mut step = cur[i].abs().max(1.0) * 1e-9;
    for _ in 0..80 {
        if *evals >= MAX_EVALS || !step.is_finite() {
            break;
        }
        for dir in [1.0f64, -1.0] {
            let mut trial = cur.to_vec();
            trial[i] = cur[i] + dir * step;
            if !trial[i].is_finite() {
                continue;
            }
            let c = evaluate(prog, body, &trial, slots);
            *evals += 1;
            if c.hit.is_some() {
                return Some(c);
            }
            if c.signed.is_finite() && c.signed.signum() != sign0 {
                hi = trial[i];
                found = true;
                break;
            }
        }
        if found {
            break;
        }
        step *= 4.0;
    }
    if !found {
        return None;
    }

    // Bisect on the bit patterns. Adjacent doubles have nothing between them,
    // so this terminates and covers every candidate in the bracket.
    let mut lo_bits = ordered_bits(cur[i]);
    let mut hi_bits = ordered_bits(hi);
    if lo_bits > hi_bits {
        std::mem::swap(&mut lo_bits, &mut hi_bits);
    }
    while hi_bits - lo_bits > 1 && *evals < MAX_EVALS {
        let mid = lo_bits + (hi_bits - lo_bits) / 2;
        let mut trial = cur.to_vec();
        trial[i] = from_ordered_bits(mid);
        if !trial[i].is_finite() {
            break;
        }
        let c = evaluate(prog, body, &trial, slots);
        *evals += 1;
        if c.hit.is_some() {
            return Some(c);
        }
        if !c.signed.is_finite() {
            break;
        }
        if c.signed.signum() == sign0 {
            lo_bits = mid;
        } else {
            hi_bits = mid;
        }
    }

    // Evaluate the bracket's endpoints. Bisection converges *to* the root but
    // only ever evaluates midpoints, so the root itself — which is where the
    // expression is exactly zero and the violating branch is taken — can sit at
    // an endpoint that is never tested.
    for bits in [lo_bits, hi_bits] {
        if *evals >= MAX_EVALS {
            break;
        }
        let mut trial = cur.to_vec();
        trial[i] = from_ordered_bits(bits);
        if !trial[i].is_finite() {
            continue;
        }
        let c = evaluate(prog, body, &trial, slots);
        *evals += 1;
        if c.hit.is_some() {
            return Some(c);
        }
    }
    None
}

/// Map a double to a monotone integer ordering, so bisection over bit patterns
/// follows numeric order across the sign boundary.
fn ordered_bits(v: f64) -> i64 {
    let b = v.to_bits() as i64;
    if b < 0 {
        i64::MIN - b
    } else {
        b
    }
}

fn from_ordered_bits(o: i64) -> f64 {
    let b = if o < 0 { i64::MIN - o } else { o };
    f64::from_bits(b as u64)
}

/// Alternating Variable Method with an accelerating pattern search.
///
/// Each variable is probed in both directions; an improvement is followed with
/// a geometrically growing step until it stops paying, which is what lets the
/// search cross many orders of magnitude without knowing the scale in advance.
fn search(prog: &Program, body: &Body, slots: &[Slot], evals: &mut usize, best_out: &mut f64) -> Option<Candidate> {
    let n = slots.len();
    let float_idx: Vec<usize> = (0..n).filter(|i| slots[*i] != Slot::NotFloat).collect();
    if float_idx.is_empty() {
        return None;
    }

    // A cheap deterministic generator. Reproducibility matters more than
    // statistical quality here, and `rand` is not a dependency of this crate.
    let mut rng: u64 = 0x9E3779B97F4A7C15;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };

    let mut restart = 0usize;
    loop {
        // Seed: first restart uses the boundary constants, later ones spread
        // across magnitudes so the search is not confined near zero.
        let mut cur: Vec<f64> = (0..n)
            .map(|i| {
                if restart < SEEDS.len() {
                    // Boundary-value seeding: try each constant across *all*
                    // variables before moving on. Assigning `SEEDS[i]` per
                    // index instead pins each variable to one value forever,
                    // and a single unlucky choice flattens the objective — with
                    // `1.5 - d1*(1.0-d2)`, fixing d2 at 1.0 makes d1 irrelevant
                    // and the search has no gradient to follow from anywhere.
                    let _ = i;
                    SEEDS[restart]
                } else {
                    let r = next();
                    let mag = ((r >> 32) % 40) as f64 - 20.0;
                    let sign = if r & 1 == 0 { 1.0 } else { -1.0 };
                    sign * ((r % 1000) as f64 + 1.0) * 10f64.powf(mag / 4.0)
                }
            })
            .collect();

        let mut best = evaluate(prog, body, &cur, slots);
        *evals += 1;
        if best.hit.is_some() {
            return Some(best);
        }
        // No float comparison was reached, so there is no gradient to descend
        // and every further candidate is a blind guess. Most of this corpus is
        // in that state, and searching it anyway doubled the category's runtime
        // for nothing. Give up on this seed immediately.
        if !best.fitness.is_finite() {
            restart += 1;
            if restart >= SEEDS.len() {
                return None;
            }
            continue;
        }

        let mut improved_any = true;
        while improved_any && *evals < MAX_EVALS {
            improved_any = false;
            for &i in &float_idx {
                let mut moved = false;
                // Multi-scale probing. The step must span everything from the
                // magnitude of the value down to a single ULP: the search
                // routinely reaches a distance of ~1e-300 and then has to close
                // an exact-equality gap, which a schedule that only grows can
                // never do. Coarse first so big moves are cheap, then finer.
                let base = cur[i].abs().max(1.0);
                let scales: Vec<f64> = (-18..=3).rev().map(|k| base * 10f64.powi(k)).collect();
                'scales: for coarse in scales {
                    for dir in [1.0f64, -1.0] {
                        let mut step = coarse;
                        loop {
                            if *evals >= MAX_EVALS || !step.is_finite() {
                                break;
                            }
                            let mut trial = cur.clone();
                            trial[i] = cur[i] + dir * step;
                            if !trial[i].is_finite() || trial[i] == cur[i] {
                                break;
                            }
                            let c = evaluate(prog, body, &trial, slots);
                            *evals += 1;
                            if c.hit.is_some() {
                                return Some(c);
                            }
                            if c.fitness < best.fitness {
                                cur = c.vals.clone();
                                best = c;
                                improved_any = true;
                                moved = true;
                                step *= 2.0; // accelerate while it keeps paying
                            } else {
                                break;
                            }
                        }
                        if moved {
                            break 'scales;
                        }
                    }
                }
                // Exact equality is reached by bracketing a sign change and
                // bisecting the bit patterns between the two ends.
                //
                // Stepping cannot do it: near the solution one ULP of an input
                // moves the compared expression by far more than the remaining
                // gap, so every step overshoots. The search reliably reaches a
                // gap of ~1e-311 this way and then cannot close it. Bisection
                // on the representable values does close it, in at most 64
                // steps, because adjacent doubles have nothing between them.
                if !moved && best.signed.is_finite() && best.fitness < 0.9 {
                    if let Some(c) = bisect(prog, body, slots, &cur, i, &best, evals) {
                        return Some(c);
                    }
                }
            }
        }

        if best.fitness < *best_out {
            *best_out = best.fitness;
        }
        restart += 1;
        if *evals >= MAX_EVALS {
            return None;
        }
    }
}

impl Engine for FloatSearch {
    fn id(&self) -> EngineId {
        EngineId("float-search")
    }

    /// Under: violations only, never a discharge. A concrete run that fails an
    /// obligation is a real execution, so the witness is valid by construction.
    fn direction(&self) -> Direction {
        Direction::Under
    }

    fn init(&mut self, _prog: &Program, _bb: &mut Blackboard) {}

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };

        let open: Vec<ObligationRef> = bb.open().to_vec();
        if open.is_empty() {
            return Progress::Exhausted;
        }

        let slots = nondet_slots(body);
        if !slots.iter().any(|s| *s != Slot::NotFloat) {
            debug!("float-search: no float nondets, skipping");
            return Progress::Exhausted;
        }

        // Only run where the fitness signal can mean something.
        //
        // Fitness is the branch distance at float *comparisons*, which is what
        // guards an assertion — `if (expr == 0.0) { assert false; }`. An
        // exception obligation (NullDeref, ArrayBounds) is not guarded that
        // way, so there is no gradient to descend and every candidate is a
        // blind guess.
        //
        // Running anyway is not free: this engine spends up to MAX_EVALS
        // concrete executions per task. On the no-runtime-exception property,
        // where every open obligation is an exception kind, that burned the
        // budget for nothing and cost 26 tasks in
        // float-nonlinear-calculation alone — timeouts went from 32 to 71 and
        // the score fell 1018 -> 949.
        //
        // Keyed on obligation kind rather than on the property, so the engine
        // does not need to know which property is being checked.
        let has_assertion = open.iter().any(|o| {
            prog.body(&o.method)
                .map(|b| b.obligation(o.id).kind.is_assertion())
                .unwrap_or(false)
        });
        if !has_assertion {
            debug!("float-search: no open assertion obligations, skipping");
            return Progress::Exhausted;
        }

        let mut evals = 0usize;
        let mut best_fitness = f64::INFINITY;
        let found = search(prog, body, &slots, &mut evals, &mut best_fitness);
        let Some(c) = found else {
            info!("float-search: no violation after {evals} candidate runs (best fitness {best_fitness:e})");
            return Progress::Exhausted;
        };

        let Some((method, oid, seq, entries)) = c.hit else {
            return Progress::Exhausted;
        };
        let oref = ObligationRef { method: method.clone(), id: oid };
        if !open.iter().any(|o| *o == oref) {
            debug!("float-search: {oref} is not open, not publishing");
            return Progress::Exhausted;
        }

        info!("float-search: violation for {oref} after {evals} candidate runs");
        let witness = Witness { nondet_sequence: seq, entries, schedule: Vec::new() };
        let _ = bb.publish(
            self.id(),
            Direction::Under,
            Artifact::Status(
                oref,
                ajave_core::artifact::Status::Violated { by: self.id(), witness },
            ),
        );
        Progress::Advanced
    }
}
