//! The language engines use to say things to each other.
//!
//! Until now there wasn't one. `Invariant::formula` was a `String` carrying a
//! comment that said exactly what was wrong with it:
//!
//! ```text
//! /// Placeholder for a real term IR. A string is fine while the consumers are
//! /// stubs, and deliberately painful enough that it will get replaced before
//! /// anything depends on it structurally.
//! ```
//!
//! That absence explains three of the four artifact kinds that have never been
//! produced. `Invariant` and `Precision` are both stubbed on it; the interval
//! engine's bounds reach the BMC through a bespoke `HashMap` that bypasses the
//! artifact log entirely, which is why CHC — for which they would be candidate
//! invariants, the most useful thing you can hand a Horn solver — cannot see
//! them; and an engine has no way to *ask* another a question, so when the BMC
//! meets `Math.sin(x)` its only move is to discard everything it knew about `x`
//! and taint the path.
//!
//! # What this is not
//!
//! Not a second program IR. `ajave_ir::Rvalue` describes *what a statement
//! does*; `Expr` describes *a claim about values*, which is why it has
//! conjunction and negation and no side effects. Nor is it an SMT term:
//! `smt::Term` is a solver-owned handle, alive only for one solver's lifetime,
//! and cannot be stored on a blackboard that outlives the solver that made it.
//!
//! # Deliberately small
//!
//! Variables, literals, arithmetic, comparison, boolean structure, and
//! applications of named library methods. Anything an engine cannot express
//! here it must decline to claim, which is the right failure: a claim nobody
//! can read is worse than no claim.
//!
//! Library applications are keyed on the **full `(class, name, desc)`
//! signature**, never `(class, name)` — the same rule `CLAUDE.md` states for
//! `contract_of`, and for the same reason. `Integer.valueOf(int)` is total and
//! `Integer.valueOf(String)` throws; a lemma about one is not a lemma about the
//! other.

use ajave_ir::VarId;

/// Operators an `Expr` may use.
///
/// Arithmetic is on the *mathematical* value, not on a bit pattern. An engine
/// that reasons about bit patterns has to say so by publishing the
/// `Approximations` that go with it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
}

impl Op {
    pub fn symbol(self) -> &'static str {
        match self {
            Op::Add => "+",
            Op::Sub => "-",
            Op::Mul => "*",
            Op::Div => "/",
            Op::Rem => "%",
            Op::Lt => "<",
            Op::Le => "<=",
            Op::Gt => ">",
            Op::Ge => ">=",
            Op::Eq => "==",
            Op::Ne => "!=",
            Op::And => "&&",
            Op::Or => "||",
        }
    }

    /// Does this produce a truth value rather than a number?
    pub fn is_predicate(self) -> bool {
        matches!(
            self,
            Op::Lt | Op::Le | Op::Gt | Op::Ge | Op::Eq | Op::Ne | Op::And | Op::Or
        )
    }
}

/// A claim about program values, in a form any engine can read.
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Expr {
    /// A program variable. Meaningful only relative to the `ProgramPoint` the
    /// carrying artifact names — `VarId` indexes one `Body`, and a collection
    /// keyed by it alone that outlives that body is the bug `CLAUDE.md`
    /// records under "faults between engines".
    Var(VarId),
    Int(i64),
    /// A double, held as its IEEE-754 bit pattern so the type is exact and
    /// `Eq`/`Hash` behave. `f64` has neither: `NaN != NaN` would make two
    /// identical claims compare unequal, and `-0.0 == 0.0` would make two
    /// different ones compare equal.
    Double(u64),
    Bool(bool),
    Bin(Op, Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    /// A named library method applied to arguments. Present so a claim can be
    /// *about* `Math.sin(x)` without anyone having to model it — which is the
    /// whole point of being able to ask.
    Apply {
        class: String,
        name: String,
        desc: String,
        args: Vec<Expr>,
    },
}

impl Expr {
    pub fn bin(op: Op, a: Expr, b: Expr) -> Expr {
        Expr::Bin(op, Box::new(a), Box::new(b))
    }

    pub fn not(a: Expr) -> Expr {
        Expr::Not(Box::new(a))
    }

    pub fn double(v: f64) -> Expr {
        Expr::Double(v.to_bits())
    }

    pub fn call(class: &str, name: &str, desc: &str, args: Vec<Expr>) -> Expr {
        Expr::Apply {
            class: class.to_string(),
            name: name.to_string(),
            desc: desc.to_string(),
            args,
        }
    }

    /// Every variable this mentions, in order of first appearance.
    ///
    /// A consumer needs this to check the claim is about variables it has, and
    /// to refuse it otherwise rather than silently reading a different one.
    pub fn vars(&self) -> Vec<VarId> {
        let mut out = Vec::new();
        self.collect_vars(&mut out);
        out
    }

    fn collect_vars(&self, out: &mut Vec<VarId>) {
        match self {
            Expr::Var(v) => {
                if !out.contains(v) {
                    out.push(*v);
                }
            }
            Expr::Int(_) | Expr::Double(_) | Expr::Bool(_) => {}
            Expr::Bin(_, a, b) => {
                a.collect_vars(out);
                b.collect_vars(out);
            }
            Expr::Not(a) => a.collect_vars(out),
            Expr::Apply { args, .. } => {
                for a in args {
                    a.collect_vars(out);
                }
            }
        }
    }

    /// Does this mention a library call nobody may have a model for?
    ///
    /// The consumer's cue to check whether it can use the claim at all. A
    /// bound on `sin(x)` is useful to an engine that can encode `sin(x)` as an
    /// uninterpreted term and useless to one that cannot.
    pub fn mentions_call(&self) -> bool {
        match self {
            Expr::Apply { .. } => true,
            Expr::Bin(_, a, b) => a.mentions_call() || b.mentions_call(),
            Expr::Not(a) => a.mentions_call(),
            _ => false,
        }
    }

    /// Is this a truth value rather than a number?
    pub fn is_predicate(&self) -> bool {
        match self {
            Expr::Bool(_) | Expr::Not(_) => true,
            Expr::Bin(op, _, _) => op.is_predicate(),
            _ => false,
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(v) => write!(f, "v{}", v.0),
            Expr::Int(n) => write!(f, "{n}"),
            Expr::Double(bits) => {
                let d = f64::from_bits(*bits);
                if d.is_nan() {
                    f.write_str("NaN")
                } else {
                    write!(f, "{d}d")
                }
            }
            Expr::Bool(b) => write!(f, "{b}"),
            Expr::Bin(op, a, b) => write!(f, "({a} {} {b})", op.symbol()),
            Expr::Not(a) => write!(f, "!{a}"),
            Expr::Apply { class, name, args, .. } => {
                let short = class.rsplit('/').next().unwrap_or(class);
                write!(f, "{short}.{name}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{a}")?;
                }
                f.write_str(")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x() -> Expr {
        Expr::Var(VarId(0))
    }

    #[test]
    fn a_claim_reads_back_the_way_it_was_written() {
        let sin_x = Expr::call("java/lang/Math", "sin", "(D)D", vec![x()]);
        let claim = Expr::bin(Op::Le, sin_x, Expr::double(1.0));
        assert_eq!(claim.to_string(), "(Math.sin(v0) <= 1d)");
    }

    /// The reason doubles are stored as bit patterns. With `f64`, two
    /// identical claims about NaN would compare unequal and a query cache
    /// would never hit.
    #[test]
    fn nan_claims_are_equal_to_themselves() {
        let a = Expr::double(f64::NAN);
        let b = Expr::double(f64::NAN);
        assert_eq!(a, b);
        // And the two zeroes stay distinguishable, which `==` on f64 loses.
        assert_ne!(Expr::double(0.0), Expr::double(-0.0));
    }

    #[test]
    fn a_consumer_can_see_what_a_claim_is_about() {
        let e = Expr::bin(
            Op::And,
            Expr::bin(Op::Lt, x(), Expr::Var(VarId(3))),
            Expr::bin(Op::Gt, Expr::Var(VarId(3)), Expr::Int(0)),
        );
        assert_eq!(e.vars(), vec![VarId(0), VarId(3)]);
        assert!(!e.mentions_call());
        assert!(e.is_predicate());
    }

    #[test]
    fn a_claim_about_an_unmodelled_call_announces_itself() {
        let e = Expr::bin(
            Op::Ge,
            Expr::call("java/lang/Math", "sin", "(D)D", vec![x()]),
            Expr::double(-1.0),
        );
        assert!(e.mentions_call(), "a consumer must be able to refuse this");
        assert_eq!(e.vars(), vec![VarId(0)]);
    }

    /// Signatures are part of identity. `CLAUDE.md` states the rule for
    /// `contract_of`; a lemma about one overload is not a lemma about another.
    #[test]
    fn overloads_are_different_claims() {
        let from_int = Expr::call("java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;", vec![]);
        let from_str = Expr::call(
            "java/lang/Integer",
            "valueOf",
            "(Ljava/lang/String;)Ljava/lang/Integer;",
            vec![],
        );
        assert_ne!(from_int, from_str);
    }
}
