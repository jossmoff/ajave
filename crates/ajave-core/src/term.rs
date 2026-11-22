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
    /// An element of the array allocated at `site`.
    ///
    /// Named by **allocation site**, not by a local, because a heap fact
    /// outlives any particular variable: `a[i] > 0` is a claim about the
    /// array, and the local that happened to point at it when the claim was
    /// made may be dead or reassigned by the time a consumer reads it.
    ///
    /// A site is not an object — a `new` in a loop produces many arrays at one
    /// site, and a claim keyed by site must hold for all of them. That is what
    /// makes it sound as an over-approximation, and it is why an engine
    /// publishing one must have reasoned about every array from that site, not
    /// the one in front of it.
    Select {
        site: ajave_ir::AllocSite,
        index: Box<Expr>,
    },
    /// A field of a particular object.
    ///
    /// `obj` is an `Expr` denoting the **receiver reference**, not an
    /// `AllocSite`, because fields are encoded Burstall-style: one array per
    /// field name, indexed by the reference. `o.f` and `p.f` are then the same
    /// cell exactly when `o = p`, so aliasing is the solver's job and no
    /// points-to analysis is needed.
    ///
    /// # Strength, versus `Select`
    ///
    /// A `Field` claim is about **one receiver**. A `Select` claim is about
    /// **every array from a site**, because a `newarray` in a loop produces
    /// many arrays at one site. Those are different strengths and a consumer
    /// must not read one as the other: a fact about `o.f` says nothing about
    /// `p.f`, while a fact about a site's elements must hold for all of them.
    Field {
        field: ajave_ir::FieldKey,
        obj: Box<Expr>,
    },
    /// The ghost **depth** of a reference along a reference field: the number
    /// of `field` links from it to null.
    ///
    /// E1's contract addition, and the cheapest shape property worth having.
    /// Maintained the way the CHC encoder already maintains ghost array
    /// lengths: `new` gives depth 0, and `o.f = p` gives
    /// `depth(o) = depth(p) + 1` when `p` is non-null.
    ///
    /// # What a consumer may conclude
    ///
    /// **Only that depth is well-founded, which is acyclicity along `field`
    /// and nothing more.** A cycle `o.f = o` would need
    /// `depth(o) = depth(o) + 1`, which no integer satisfies, so a state
    /// containing one is infeasible — that is the whole proof, and it is why
    /// this needs no separation logic and no reachability relation.
    ///
    /// It says nothing about *disjointness*. Two acyclic chains may share a
    /// tail and both have well-founded depth, so a consumer that read this as
    /// "these structures do not overlap" would be unsound. That claim is
    /// `Disjoint`, which does not exist yet, and an engine reasoning about
    /// depth alone must still declare `HEAP_NO_SHAPE`.
    ///
    /// Depth is also *partial*: a reference reached from a parameter or an
    /// unmodelled call has no known depth, and an engine must treat an absent
    /// depth as unconstrained rather than as zero. Zero means "points at
    /// null", which is a real and much stronger claim.
    Depth {
        field: ajave_ir::FieldKey,
        obj: Box<Expr>,
    },
    /// The null reference.
    ///
    /// # What a consumer may conclude
    ///
    /// `Bin(Ne, r, Null)` is the claim that `r` is non-null **at the program
    /// point the carrying artifact names**, and nothing about `r` anywhere
    /// else. `NullDeref` is 53% of the corpus's open obligations and its
    /// safety condition is exactly this shape, so without it an invariant
    /// cannot be *sufficient* for the commonest obligation there is.
    ///
    /// A reference is not a number. A consumer must not read `Null` as
    /// `Int(0)` and must not do arithmetic on it: the JVM gives no numeric
    /// meaning to a reference, and two distinct non-null references are
    /// unordered. `Op::Eq` and `Op::Ne` are the only operators defined on it.
    Null,
    /// The length of the array that `obj` refers to.
    ///
    /// Burstall-style like `Field`: one length array indexed by the reference,
    /// so `Length{o}` and `Length{p}` are the same cell exactly when `o = p`
    /// and aliasing stays the solver's job rather than a points-to analysis's.
    /// This is the shape both CHC encoders already maintain as a ghost length.
    ///
    /// # Strength, versus `Select`
    ///
    /// `Length { obj }` is about **one reference**, as `Field` is.
    /// `Select { site }` is about **every array allocated at a site**. A
    /// consumer must not read one as the other: a length claim about `o` says
    /// nothing about another array from the same `new`.
    ///
    /// # Partiality
    ///
    /// A reference from a parameter or an unmodelled call has no known length.
    /// An absent length is **unconstrained**, never zero — zero would be the
    /// much stronger claim that the array is empty.
    ///
    /// # Why this is not `Apply` on `arraylength`
    ///
    /// `Apply` announces "nobody may have a model for this"
    /// (`mentions_call`), and a consumer is entitled to decline it. Array
    /// length is not unmodelled: the IR has `Rvalue::ArrayLength` and both CHC
    /// encoders track it. Routing it through `Apply` would make every length
    /// claim look optional to every consumer.
    Length {
        obj: Box<Expr>,
    },
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

    // Named for the domain operation, not the std trait: these are
    // interval/term algebra, and `Interval::div` reads correctly.
    #[allow(clippy::should_implement_trait)]
    pub fn not(a: Expr) -> Expr {
        Expr::Not(Box::new(a))
    }

    pub fn double(v: f64) -> Expr {
        Expr::Double(v.to_bits())
    }

    /// `obj` is non-null. The commonest claim there is; see `Expr::Null`.
    pub fn non_null(obj: Expr) -> Expr {
        Expr::bin(Op::Ne, obj, Expr::Null)
    }

    pub fn length(obj: Expr) -> Expr {
        Expr::Length { obj: Box::new(obj) }
    }

    /// `0 <= index < Length{obj}` — the safety condition of an `ArrayBounds`
    /// obligation, which is 34% of the corpus's open obligations.
    pub fn in_bounds(index: Expr, obj: Expr) -> Expr {
        Expr::bin(
            Op::And,
            Expr::bin(Op::Le, Expr::Int(0), index.clone()),
            Expr::bin(Op::Lt, index, Expr::length(obj)),
        )
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
            Expr::Int(_) | Expr::Double(_) | Expr::Bool(_) | Expr::Null => {}
            // The reference may be a variable; the length itself is not one.
            Expr::Length { obj } => obj.collect_vars(out),
            Expr::Bin(_, a, b) => {
                a.collect_vars(out);
                b.collect_vars(out);
            }
            Expr::Not(a) => a.collect_vars(out),
            // The receiver may mention variables; the field key never does.
            Expr::Depth { obj, .. } => obj.collect_vars(out),
            // The site is not a variable; the index may mention some.
            Expr::Select { index, .. } => index.collect_vars(out),
            // The receiver is a reference-valued expression and may be a var.
            Expr::Field { obj, .. } => obj.collect_vars(out),
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
            Expr::Select { site, index } => {
                write!(f, "a[bb{}:{}][{index}]", site.block.0, site.index)
            }
            Expr::Field { field, obj } => write!(f, "{obj}.{}", field.name),
            Expr::Depth { field, obj } => write!(f, "depth_{}({obj})", field.name),
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
            Expr::Null => f.write_str("null"),
            Expr::Length { obj } => write!(f, "{obj}.length"),
            Expr::Bin(op, a, b) => write!(f, "({a} {} {b})", op.symbol()),
            Expr::Not(a) => write!(f, "!{a}"),
            Expr::Apply {
                class, name, args, ..
            } => {
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

    /// The claim language keeps these apart on purpose. A reference has no
    /// numeric meaning in the JVM, so a producer must not be able to write
    /// `r + 1` and a consumer must not be able to order two references. The
    /// LIA checker is the one place allowed to know that null is encoded as 0.
    #[test]
    fn null_is_not_the_integer_zero() {
        assert_ne!(Expr::Null, Expr::Int(0));
        assert_ne!(Expr::non_null(x()), Expr::bin(Op::Ne, x(), Expr::Int(0)));
    }

    /// A consumer uses `vars` to check a claim is about variables it has and
    /// to refuse it otherwise. A length claim's receiver is a variable, and a
    /// `vars` that could not see through `Length` would let a consumer read a
    /// claim about a variable it does not have.
    #[test]
    fn a_length_claim_is_about_its_receiver() {
        assert_eq!(Expr::length(x()).vars(), vec![VarId(0)]);
        assert_eq!(
            Expr::in_bounds(Expr::Var(VarId(2)), x()).vars(),
            vec![VarId(2), VarId(0)]
        );
    }

    /// Array length is modelled, unlike `Math.sin`. If it announced itself as
    /// an unmodelled call, every consumer would be entitled to decline every
    /// bounds claim -- which is 34% of the corpus's open obligations.
    #[test]
    fn a_length_claim_is_not_an_unmodelled_call() {
        assert!(!Expr::length(x()).mentions_call());
        assert!(!Expr::in_bounds(Expr::Var(VarId(2)), x()).mentions_call());
    }

    #[test]
    fn the_new_claims_read_back_the_way_they_were_written() {
        assert_eq!(Expr::non_null(x()).to_string(), "(v0 != null)");
        assert_eq!(Expr::length(x()).to_string(), "v0.length");
        assert_eq!(
            Expr::in_bounds(Expr::Var(VarId(2)), x()).to_string(),
            "((0 <= v2) && (v2 < v0.length))"
        );
    }

    /// Signatures are part of identity. `CLAUDE.md` states the rule for
    /// `contract_of`; a lemma about one overload is not a lemma about another.
    #[test]
    fn overloads_are_different_claims() {
        let from_int = Expr::call(
            "java/lang/Integer",
            "valueOf",
            "(I)Ljava/lang/Integer;",
            vec![],
        );
        let from_str = Expr::call(
            "java/lang/Integer",
            "valueOf",
            "(Ljava/lang/String;)Ljava/lang/Integer;",
            vec![],
        );
        assert_ne!(from_int, from_str);
    }
}
