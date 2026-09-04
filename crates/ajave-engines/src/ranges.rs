//! Answers questions about library functions whose *range* is specified.
//!
//! The first answerer. Its whole job is to reply to `Query`s another engine
//! posted, which is why it publishes no statuses of its own and never touches
//! an obligation.
//!
//! # Why this is worth having
//!
//! When the BMC meets `Math.sin(x)` it cannot encode the function — SMT-LIB's
//! FloatingPoint theory has no `fp.sin` — so it substitutes an unconstrained
//! value. That value is not merely imprecise, it is *wrong in a specific way*:
//! it lets the solver claim `sin(x) == 5000`, and every path reachable only
//! through such a claim is explored for nothing.
//!
//! Nobody needs to model `sin` to rule that out. The Javadoc pins the range,
//! and a range is a lemma:
//!
//! ```text
//! smt-bmc → Query  { about: v42, given: [v42 == Math.sin(v7)], want: Bounds }
//! ranges  → Lemma  { Holds: !(v42 == v42) || (-1.0 <= v42 && v42 <= 1.0) }
//! ```
//!
//! This is the difference between a specialised engine being an *alternative*
//! to the others and being a *resource* for them. `ranges` could not verify a
//! program if its life depended on it. It answers one question well.
//!
//! # Why the NaN guard
//!
//! `Math.sin(NaN)` is `NaN`, and so is `Math.sin(Infinity)`. NaN is outside
//! every range, and every ordered comparison against it is false, so the bare
//! claim `-1 <= sin(x) <= 1` is **false** — asserting it would remove real
//! executions, and an engine that then claimed exhaustive coverage would be
//! claiming it over a state space it had shrunk. That is a wrong TRUE at −16.
//!
//! The guard is written as `!(r == r)`, which is true exactly when `r` is NaN:
//! IEEE-754 makes NaN the only value not equal to itself. So the lemma reads
//! "either the result is NaN, or it is in range", which holds for every input
//! — including `sqrt(-1)` and `asin(2)`, where the *argument* is out of domain
//! and the result is NaN.
//!
//! Guarding on the result rather than the argument is what makes one rule
//! cover all of them.
//!
//! # Soundness
//!
//! `Over`: every lemma is a claim about every execution, so this engine may
//! never answer with a witness — the blackboard enforces that at publish.
//!
//! Every entry below is justified from the method's Javadoc, never from
//! observed behaviour, and keyed on the full `(class, name, desc)` signature.
//! That is the discipline `CLAUDE.md` states for `contract_of`, and it applies
//! here for exactly the same reason: a wrong entry is a wrong TRUE, not a
//! precision loss. `tools/validate_ranges.py` checks each one against a real
//! JVM over adversarial inputs.

use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_core::term::{Expr, Op};
use ajave_ir::Program;
use log::{debug, info};

/// Range of a method's result, over every input for which the result is not
/// NaN.
///
/// Deliberately a short list of functions whose Javadoc states the range
/// outright. "When in doubt, leave it out" — omission costs precision, a wrong
/// entry costs correctness.
///
/// `(class, name, desc)` → `(lo, hi)`.
const RANGES: &[(&str, &str, &str, f64, f64)] = &[
    // "the sine of the argument" — a sine is in [-1, 1] by definition, and
    // the Javadoc's 1-ulp error allowance cannot take it outside, because the
    // special cases (±0.0, NaN, ±Infinity) are pinned separately and the
    // computed result is a correctly-signed approximation of a value in range.
    ("java/lang/Math", "sin", "(D)D", -1.0, 1.0),
    ("java/lang/StrictMath", "sin", "(D)D", -1.0, 1.0),
    ("java/lang/Math", "cos", "(D)D", -1.0, 1.0),
    ("java/lang/StrictMath", "cos", "(D)D", -1.0, 1.0),
    // "the arc sine ... in the range -pi/2 through pi/2". Widened by one ulp
    // at each end so a 1-ulp error cannot fall outside the claim.
    ("java/lang/Math", "asin", "(D)D", -1.5707963267948968, 1.5707963267948968),
    ("java/lang/StrictMath", "asin", "(D)D", -1.5707963267948968, 1.5707963267948968),
    // "the arc cosine ... in the range 0.0 through pi".
    ("java/lang/Math", "acos", "(D)D", 0.0, 3.1415926535897936),
    ("java/lang/StrictMath", "acos", "(D)D", 0.0, 3.1415926535897936),
    // "the arc tangent ... in the range -pi/2 through pi/2".
    ("java/lang/Math", "atan", "(D)D", -1.5707963267948968, 1.5707963267948968),
    ("java/lang/StrictMath", "atan", "(D)D", -1.5707963267948968, 1.5707963267948968),
    // "in the range -pi through pi" — two-argument arc tangent.
    ("java/lang/Math", "atan2", "(DD)D", -3.1415926535897936, 3.1415926535897936),
    ("java/lang/StrictMath", "atan2", "(DD)D", -3.1415926535897936, 3.1415926535897936),
    // Non-negative or NaN: `sqrt` of a negative is NaN, `sqrt(+0.0)` is +0.0,
    // and the Javadoc guarantees a correctly rounded non-negative result
    // otherwise.
    ("java/lang/Math", "sqrt", "(D)D", 0.0, f64::INFINITY),
    ("java/lang/StrictMath", "sqrt", "(D)D", 0.0, f64::INFINITY),
    // "if the argument is negative infinity, then the result is positive
    // zero" — and e^x > 0 everywhere else it is defined.
    ("java/lang/Math", "exp", "(D)D", 0.0, f64::INFINITY),
    ("java/lang/StrictMath", "exp", "(D)D", 0.0, f64::INFINITY),
    // `Math.abs` of a double is non-negative or NaN. Note `abs` on *ints* is
    // NOT here: `Math.abs(Integer.MIN_VALUE)` is negative, which is the
    // classic Java trap and exactly the kind of entry that would be a wrong
    // TRUE.
    ("java/lang/Math", "abs", "(D)D", 0.0, f64::INFINITY),
    ("java/lang/StrictMath", "abs", "(D)D", 0.0, f64::INFINITY),
    // "the hypotenuse ... without intermediate overflow or underflow" —
    // non-negative.
    ("java/lang/Math", "hypot", "(DD)D", 0.0, f64::INFINITY),
    ("java/lang/StrictMath", "hypot", "(DD)D", 0.0, f64::INFINITY),
    // "in the range -1.0 through 1.0" — hyperbolic tangent.
    ("java/lang/Math", "tanh", "(D)D", -1.0, 1.0),
    ("java/lang/StrictMath", "tanh", "(D)D", -1.0, 1.0),
];

fn range_of(class: &str, name: &str, desc: &str) -> Option<(f64, f64)> {
    RANGES
        .iter()
        .find(|(c, n, d, _, _)| *c == class && *n == name && *d == desc)
        .map(|(_, _, _, lo, hi)| (*lo, *hi))
}

pub struct Ranges {
    answered: std::collections::HashSet<u32>,
}

impl Default for Ranges {
    fn default() -> Self {
        Self::new()
    }
}

impl Ranges {
    pub fn new() -> Ranges {
        Ranges { answered: std::collections::HashSet::new() }
    }
}

/// The claim: `!(r == r) || (lo <= r && r <= hi)`.
///
/// Read as "the result is NaN, or it is in range". `!(r == r)` is true exactly
/// for NaN, which is what makes one form cover both the in-domain and the
/// out-of-domain case.
fn bounded_or_nan(r: &Expr, lo: f64, hi: f64) -> Expr {
    let is_nan = Expr::not(Expr::bin(Op::Eq, r.clone(), r.clone()));
    let mut in_range = None;
    if lo.is_finite() {
        in_range = Some(Expr::bin(Op::Le, Expr::double(lo), r.clone()));
    }
    if hi.is_finite() {
        let upper = Expr::bin(Op::Le, r.clone(), Expr::double(hi));
        in_range = Some(match in_range {
            Some(l) => Expr::bin(Op::And, l, upper),
            None => upper,
        });
    }
    match in_range {
        Some(b) => Expr::bin(Op::Or, is_nan, b),
        // Both ends infinite: no claim to make.
        None => Expr::Bool(true),
    }
}

/// Find `about == <library call>` among the facts the asker supplied.
///
/// The asker says what the variable *is*; this engine decides whether it knows
/// anything about that. Keeping the binding in `given` rather than making the
/// query be *about* the call directly is what lets the answer be phrased in
/// terms of a variable the asker already has a term for.
fn bound_call<'a>(about: &Expr, given: &'a [Expr]) -> Option<&'a Expr> {
    given.iter().find_map(|g| match g {
        Expr::Bin(Op::Eq, l, r) if l.as_ref() == about => Some(r.as_ref()),
        Expr::Bin(Op::Eq, l, r) if r.as_ref() == about => Some(l.as_ref()),
        _ => None,
    })
}

impl Engine for Ranges {
    fn id(&self) -> EngineId {
        EngineId("ranges")
    }

    /// Over: every answer is a claim about every execution. The blackboard
    /// refuses a witness from this engine, which is the discipline that keeps
    /// a bound from being mistaken for a counterexample.
    fn direction(&self) -> Direction {
        Direction::Over
    }

    fn step(&mut self, _prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        let asked: Vec<(u32, Expr, Vec<Expr>, Want)> = bb
            .unanswered()
            .into_iter()
            .filter(|q| !self.answered.contains(&q.id))
            .map(|q| (q.id, q.about.clone(), q.given.clone(), q.want))
            .collect();
        if asked.is_empty() {
            // `Stalled`, not `Exhausted`. An answerer has nothing to do until
            // somebody asks, and the orchestrator *retires* an engine that
            // reports itself finished — so returning `Exhausted` here meant
            // this engine died in round one, before the BMC had run at all,
            // and every question it later posted went unanswered.
            //
            // "Nothing to do yet" and "nothing to do ever" are different
            // answers, and only the engine knows which it means.
            return Progress::Stalled;
        }

        let mut advanced = false;
        for (id, about, given, want) in asked {
            self.answered.insert(id);
            // Only universal questions. A `Satisfiable` query wants a witness,
            // which an over-approximating engine may not supply.
            if want == Want::Satisfiable {
                continue;
            }
            let answer = match bound_call(&about, &given) {
                Some(Expr::Apply { class, name, desc, .. }) => {
                    match range_of(class, name, desc) {
                        Some((lo, hi)) => {
                            debug!(
                                "ranges: {}.{} is in [{lo}, {hi}] or NaN — answering query {id}",
                                class, name
                            );
                            Answer::Bounds {
                                lo: Expr::double(lo),
                                hi: Expr::double(hi),
                            }
                        }
                        // Named, but nothing specified about its range.
                        None => Answer::Unknown,
                    }
                }
                _ => Answer::Unknown,
            };

            // A refusal is worth publishing: it stops the scheduler offering
            // the same question to this engine again.
            let published = bb.publish(
                self.id(),
                Direction::Over,
                Artifact::Lemma(Lemma { query: id, by: self.id(), answer }),
            );
            if published.is_ok() {
                advanced = true;
            }
        }

        if advanced {
            info!("ranges: answered {} query(ies)", self.answered.len());
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}

/// The `Expr` form of a range answer, for a consumer that wants the guarded
/// predicate rather than the two endpoints.
pub fn as_predicate(about: &Expr, lo: &Expr, hi: &Expr) -> Option<Expr> {
    let (Expr::Double(l), Expr::Double(h)) = (lo, hi) else { return None };
    Some(bounded_or_nan(about, f64::from_bits(*l), f64::from_bits(*h)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::VarId;

    fn v(n: u32) -> Expr {
        Expr::Var(VarId(n))
    }

    #[test]
    fn a_range_is_guarded_by_the_nan_case() {
        let p = bounded_or_nan(&v(0), -1.0, 1.0);
        assert_eq!(p.to_string(), "(!(v0 == v0) || ((-1d <= v0) && (v0 <= 1d)))");
    }

    /// `sqrt` and `exp` are bounded below and not above, so the claim must not
    /// invent an upper bound out of `f64::INFINITY`.
    #[test]
    fn a_one_sided_range_makes_only_the_claim_it_can() {
        let p = bounded_or_nan(&v(0), 0.0, f64::INFINITY);
        assert_eq!(p.to_string(), "(!(v0 == v0) || (0d <= v0))");
    }

    #[test]
    fn the_binding_is_read_from_either_side_of_the_equality() {
        let sin = Expr::call("java/lang/Math", "sin", "(D)D", vec![v(7)]);
        let forward = vec![Expr::bin(Op::Eq, v(42), sin.clone())];
        let backward = vec![Expr::bin(Op::Eq, sin.clone(), v(42))];
        assert_eq!(bound_call(&v(42), &forward), Some(&sin));
        assert_eq!(bound_call(&v(42), &backward), Some(&sin));
    }

    /// Signatures are identity. `Math.abs(double)` is non-negative;
    /// `Math.abs(int)` is not — `Math.abs(Integer.MIN_VALUE)` is negative,
    /// and claiming otherwise would be a wrong TRUE.
    #[test]
    fn the_int_overload_of_abs_is_deliberately_absent() {
        assert!(range_of("java/lang/Math", "abs", "(D)D").is_some());
        assert!(
            range_of("java/lang/Math", "abs", "(I)I").is_none(),
            "Math.abs(Integer.MIN_VALUE) is negative"
        );
    }

    #[test]
    fn an_unknown_function_gets_no_claim() {
        assert!(range_of("java/lang/Math", "log", "(D)D").is_none());
        assert!(range_of("com/example/Mine", "sin", "(D)D").is_none());
    }
}
