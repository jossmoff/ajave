//! Shared SMT-LIB2 text encoding for operands and rvalues.
//!
//! CHC uses bitvector theory; interpolation/IMC/CEGAR use linear integer
//! arithmetic. The structure of operand and rvalue encoding is identical
//! across both — only the constants and operator names differ. This module
//! captures that shared structure via the `SmtTheory` trait.

use ajave_ir::*;

/// Variable lookup: maps a VarId index to its current SMT expression.
pub trait VarLookup {
    fn lookup(&self, var_index: usize) -> String;
}

impl VarLookup for Vec<String> {
    fn lookup(&self, var_index: usize) -> String {
        self.get(var_index)
            .cloned()
            .unwrap_or_else(|| format!("v{}", var_index))
    }
}

impl VarLookup for std::collections::HashMap<usize, String> {
    fn lookup(&self, var_index: usize) -> String {
        self.get(&var_index)
            .cloned()
            .unwrap_or_else(|| format!("v{}", var_index))
    }
}

/// Theory-specific encoding of constants and operators.
pub trait SmtTheory {
    fn encode_int(&self, value: i32) -> String;
    fn encode_long(&self, value: i64) -> String;
    fn encode_null(&self) -> String;
    fn encode_non_null(&self) -> String;
    fn encode_zero(&self) -> String;
    fn encode_true(&self) -> String;
    fn encode_false(&self) -> String;

    fn encode_binop(&self, op: &BinOp, left: &str, right: &str) -> String;
    fn encode_neg(&self, operand: &str) -> String;
    /// `to` **and** `from`, because a theory cannot tell a widening cast from
    /// a narrowing one without both. Only the destination used to be passed, so
    /// `LiaTheory` returned the operand unchanged for `l2i` -- a 64-bit value
    /// silently kept as a 32-bit one.
    fn encode_cast(&self, to: &Ty, from: &Ty, operand: &str) -> String;
    fn encode_cmp(&self, left: &str, right: &str) -> String;
    /// Can this theory express `op` faithfully?
    ///
    /// A theory that cannot must not invent a value: linear integer arithmetic
    /// has no bitwise operators, and its `div`/`mod` are Euclidean where Java's
    /// truncate toward zero. Returning `false` makes `Encoder` allocate an
    /// unconstrained binder instead, which is sound. CHC used to encode all of
    /// these as the literal `0` -- not a conservative unknown but a specific
    /// wrong value, and a proof resting on it is worth nothing (#77).
    fn models_binop(&self, op: &BinOp) -> bool;

    /// Can this theory express the cast faithfully? Widening always; narrowing
    /// only where the theory has a truncation.
    fn models_cast(&self, to: &Ty, from: &Ty) -> bool;

    /// The sort a value of this width has, e.g. `Int` or `(_ BitVec 32)`.
    fn sort_of(&self, wide: bool) -> String;

    /// Does an arithmetic result need an overflow side condition?
    ///
    /// False for a theory that already wraps, like bitvectors.
    fn needs_overflow_guard(&self) -> bool;

    fn encode_nonzero(&self, operand: &str) -> String;
    fn encode_is_zero(&self, operand: &str) -> String;
}

/// Encode an operand using the given theory and variable lookup.
pub fn encode_operand<T: SmtTheory, V: VarLookup>(theory: &T, op: &Operand, vars: &V) -> String {
    match op {
        Operand::Var(v) => vars.lookup(v.0 as usize),
        Operand::Const(Const::Int(n)) => theory.encode_int(*n),
        Operand::Const(Const::Long(n)) => theory.encode_long(*n),
        Operand::Const(Const::Null) => theory.encode_null(),
        Operand::Const(Const::Str(_)) => theory.encode_non_null(),
        Operand::Const(_) => theory.encode_zero(),
    }
}

// ---------------------------------------------------------------------------
// Encoder
// ---------------------------------------------------------------------------

/// Builds an encoding, owning the three things a consumer used to re-derive.
///
/// # Why this exists
///
/// The theories are pure string functions, which left every consumer to solve
/// the same three problems and solve them differently:
///
/// * **Naming.** `encode_fresh` minted names from a process-global counter that
///   the theory could not declare, so consumers recovered them by *string
///   prefix* -- `expr.starts_with("bv_fresh")` in one, `"chc_fresh"` in another.
///   A theory that allocates a name it cannot bind is an interface that has to
///   be worked around.
/// * **Side conditions.** Overflow has to reach the consumer's `error`, and
///   there was nowhere to put it, so CHC collected it out of band and IMC did
///   not collect it at all.
/// * **Sharing.** Consumers substituted expression *text* for variables, so
///   `x = a + b; y = x * x;` became `(* (+ a b) (+ a b))` and a chain of
///   assignments duplicated whole subtrees. Fibonacci encoded to 24 KB and
///   Ackermann to 48 KB. `bind` gives each computed value a name, which makes
///   the encoding linear in the number of statements.
pub struct Encoder<'t, T: SmtTheory> {
    theory: &'t T,
    prefix: String,
    counter: u32,
    /// Variables introduced here, as (name, sort). The consumer declares or
    /// quantifies these.
    pub binders: Vec<(String, String)>,
    /// Equalities defining bound values; conjoined into the clause body.
    pub definitions: Vec<String>,
    /// Conditions the consumer must route to `error`, e.g. overflow.
    pub side_conditions: Vec<String>,
}

impl<'t, T: SmtTheory> Encoder<'t, T> {
    pub fn new(theory: &'t T, prefix: &str) -> Self {
        Encoder {
            theory,
            prefix: prefix.to_string(),
            counter: 0,
            binders: Vec::new(),
            definitions: Vec::new(),
            side_conditions: Vec::new(),
        }
    }

    /// An unconstrained variable of the given width.
    pub fn fresh(&mut self, wide: bool) -> String {
        let name = format!("{}f{}", self.prefix, self.counter);
        self.counter += 1;
        self.binders.push((name.clone(), self.theory.sort_of(wide)));
        name
    }

    /// Name `expr`, so later uses refer to the name rather than repeat the term.
    pub fn bind(&mut self, expr: &str, wide: bool) -> String {
        let name = self.fresh(wide);
        self.definitions.push(format!("(= {name} {expr})"));
        name
    }

    /// Encode an rvalue, recording any binder or side condition it needs.
    ///
    /// `ty` reports an operand's JVM type, which the IR carries on the variable
    /// rather than on the operation. It answers two different questions: the
    /// *width* an overflow condition is computed at, and whether the operand is
    /// floating-point. It used to answer only the first, as `wide: Fn -> bool`,
    /// and that is why the quarantine below could not be enforced here.
    ///
    /// # The float quarantine
    ///
    /// **A floating-point operand may not flow into any integer-valued term.**
    ///
    /// Neither theory this `Encoder` serves has a float sort. LIA has no reals
    /// in this encoding at all; a bitvector holds a float's *bit pattern*. So
    /// computing on a float with either theory's arithmetic is not
    /// floating-point arithmetic -- it is a different total function, which is
    /// **wrong rather than coarse**, and a proof resting on it is worth
    /// nothing. The three leaks this closes are enumerated in
    /// `docs/proposals/lia-faithfulness.md` §2.2:
    ///
    /// * `Bin`/`Neg` over a float: `(+ bits bits)` is not `dadd`, and it also
    ///   produced a bogus `lia_overflow_cond` over bit patterns.
    /// * `Cmp` of two floats: `(ite (< l r) -1 ...)` on bit patterns is not
    ///   `dcmpg` -- every negative double has its sign bit set, so the integer
    ///   order is not the float order. Monniaux (TOPLAS 2008) is the general
    ///   warning; `benchmarks/ajave/jvm-floats/NaNComparisonIsAlwaysFalse` is
    ///   this tree's own instance.
    /// * `Cast` between a float type and an integer type: `lia_width(Float)` is
    ///   32, so `models_cast`'s width test called `f2i` a widening and
    ///   `encode_cast` returned the operand unchanged. `(int) 3.7` is `3`, and
    ///   the operand was a bit pattern besides.
    ///
    /// Havoc is the sound answer for an over-approximating engine: an
    /// unconstrained value contains the real one, so a proof over it holds of
    /// the program. It is what this encoder already does for `Div`, `Rem` and
    /// the shifts, and what CHC's second LIA encoder (`chc::lia_rvalue`) has
    /// done for floats all along -- this path was the one that still leaked,
    /// and it is the one `imc`, `cegar`, `invariant_check` and `houdini` read.
    pub fn rvalue<V: VarLookup>(
        &mut self,
        rv: &Rvalue,
        vars: &V,
        ty: &dyn Fn(&Operand) -> Option<Ty>,
    ) -> String {
        let wide = |o: &Operand| ty(o).map(|t| t.is_wide()).unwrap_or(false);
        // The quarantine, before any theory is consulted. Deliberately first:
        // a check placed inside the `Bin` arm would have to be repeated in
        // `Neg`, `Cmp` and `Cast`, and the leak was exactly a missing repeat.
        if rvalue_is_float(rv, ty) {
            // The *result* width, which is not always an operand's: `dcmpg`
            // takes two 64-bit operands and pushes an `int`, and a cast's
            // result width is its destination's. LIA ignores this (`sort_of`
            // answers `Int` either way) but the bitvector theory does not, and
            // a 32-bit binder standing for a 64-bit value would be a sort
            // error rather than an imprecision.
            let w = match rv {
                Rvalue::Cmp(..) => false,
                Rvalue::Cast(to, _, _) => lia_width(to) == 64,
                Rvalue::Bin(_, a, b) => wide(a) || wide(b),
                Rvalue::Neg(o) => wide(o),
                _ => false,
            };
            return self.fresh(w);
        }
        match rv {
            Rvalue::Bin(op, a, b) => {
                let w = wide(a) || wide(b);
                if !self.theory.models_binop(op) {
                    return self.fresh(w);
                }
                let l = encode_operand(self.theory, a, vars);
                let r = encode_operand(self.theory, b, vars);
                let e = self.theory.encode_binop(op, &l, &r);
                if self.theory.needs_overflow_guard() && overflowing(op) {
                    self.side_conditions.push(lia_overflow_cond(&e, w));
                }
                e
            }
            Rvalue::Neg(o) => {
                let w = wide(o);
                let v = encode_operand(self.theory, o, vars);
                let e = self.theory.encode_neg(&v);
                // Negating the minimum value overflows.
                if self.theory.needs_overflow_guard() {
                    self.side_conditions.push(lia_overflow_cond(&e, w));
                }
                e
            }
            Rvalue::Cast(to, from, o) => {
                if !self.theory.models_cast(to, from) {
                    return self.fresh(lia_width(to) == 64);
                }
                let v = encode_operand(self.theory, o, vars);
                self.theory.encode_cast(to, from, &v)
            }
            Rvalue::Use(o) => encode_operand(self.theory, o, vars),
            Rvalue::Cmp(_, a, b) => {
                let l = encode_operand(self.theory, a, vars);
                let r = encode_operand(self.theory, b, vars);
                self.theory.encode_cmp(&l, &r)
            }
            // Nondet, havoc, and everything on the heap: unconstrained.
            _ => self.fresh(false),
        }
    }
}

// ---------------------------------------------------------------------------
// Overflow, for the integer theories
// ---------------------------------------------------------------------------

/// Does this rvalue read or produce a floating-point value?
///
/// The predicate behind `Encoder::rvalue`'s quarantine, and shared with
/// `chc::lia_rvalue` so the two encoders cannot answer it differently -- the
/// seam `CLAUDE.md` records under "CHC has two encoders".
///
/// Only the computing forms matter. A `Use` of a float merely copies a value
/// that was havoced where it was produced, and the unmodelled forms
/// (`Nondet`, `Havoc`, every heap read) already havoc.
///
/// `Cmp` is decided by its `CmpKind` **as well as** by its operands' types,
/// and the kind is checked first on purpose: it is the bytecode's own answer
/// (`fcmpl`/`dcmpg` are `FloatL`/`FloatG`, `lcmp` is `Long`), so it stays
/// correct where `ty` cannot resolve a variable and returns `None`. A
/// comparison whose operand types were lost would otherwise be encoded as an
/// integer comparison of bit patterns.
pub fn rvalue_is_float(rv: &Rvalue, ty: &dyn Fn(&Operand) -> Option<Ty>) -> bool {
    let f = |o: &Operand| matches!(ty(o), Some(Ty::Float) | Some(Ty::Double));
    match rv {
        Rvalue::Bin(_, a, b) => f(a) || f(b),
        Rvalue::Neg(o) => f(o),
        Rvalue::Cmp(kind, a, b) => {
            matches!(kind, CmpKind::FloatL | CmpKind::FloatG) || f(a) || f(b)
        }
        // Either direction, and float-to-float too: `f2d` on a bit pattern is
        // not a widening of a number.
        Rvalue::Cast(to, from, _) => {
            matches!(to, Ty::Float | Ty::Double) || matches!(from, Ty::Float | Ty::Double)
        }
        _ => false,
    }
}

/// The JVM type of an operand, for the `ty` argument of `Encoder::rvalue`.
///
/// Shared so every caller answers it the same way. A variable the body does
/// not declare yields `None`, which reads as "unknown" — not as "int".
pub fn operand_ty(body: &ajave_ir::Body, op: &Operand) -> Option<Ty> {
    match op {
        Operand::Const(c) => Some(c.ty()),
        Operand::Var(v) => body.vars.get(v.0 as usize).map(|vi| vi.ty),
    }
}

/// Width of a type in bits, for deciding whether a cast narrows.
pub fn lia_width(ty: &Ty) -> u32 {
    match ty {
        Ty::Long | Ty::Double => 64,
        _ => 32,
    }
}

/// Does this operator's result need an overflow guard?
pub fn overflowing(op: &BinOp) -> bool {
    matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul)
}

/// `(or (> e MAX) (< e MIN))` for the width `e` is computed at.
///
/// Java's arithmetic wraps; linear integer arithmetic does not, so `x + 1 > x`
/// is valid in an unbounded encoding and false on a JVM. Asserting this as a
/// disjunct of a consumer's `error` condition repairs that: proving `error`
/// unreachable then proves *both* that nothing overflowed *and* that the
/// property holds, and on an overflow-free path the two arithmetics agree.
///
/// Shared so the two consumers cannot drift. CHC described this argument in
/// three comments and never implemented it (#77); the IMC encoder had the same
/// gap and no comment at all.
pub fn lia_overflow_cond(expr: &str, wide: bool) -> String {
    let (min, max) = if wide {
        ("(- 9223372036854775808)", "9223372036854775807")
    } else {
        ("(- 2147483648)", "2147483647")
    };
    format!("(or (> {expr} {max}) (< {expr} {min}))")
}

// ---------------------------------------------------------------------------
// Bitvector theory (used by CHC)
// ---------------------------------------------------------------------------

pub struct BitvectorTheory;

impl SmtTheory for BitvectorTheory {
    fn encode_int(&self, value: i32) -> String {
        format!("#x{:08x}", value as u32)
    }
    fn encode_long(&self, value: i64) -> String {
        format!("#x{:016x}", value as u64)
    }
    fn encode_null(&self) -> String {
        "#x00000000".to_string()
    }
    fn encode_non_null(&self) -> String {
        "#x00000001".to_string()
    }
    fn encode_zero(&self) -> String {
        "#x00000000".to_string()
    }
    fn encode_true(&self) -> String {
        "#x00000001".to_string()
    }
    fn encode_false(&self) -> String {
        "#x00000000".to_string()
    }

    fn encode_binop(&self, op: &BinOp, left: &str, right: &str) -> String {
        match op {
            BinOp::Add => format!("(bvadd {} {})", left, right),
            BinOp::Sub => format!("(bvsub {} {})", left, right),
            BinOp::Mul => format!("(bvmul {} {})", left, right),
            BinOp::Div => format!("(bvsdiv {} {})", left, right),
            BinOp::Rem => format!("(bvsrem {} {})", left, right),
            BinOp::And => format!("(bvand {} {})", left, right),
            BinOp::Or => format!("(bvor {} {})", left, right),
            BinOp::Xor => format!("(bvxor {} {})", left, right),
            BinOp::Shl => format!("(bvshl {} {})", left, right),
            BinOp::Shr => format!("(bvashr {} {})", left, right),
            BinOp::UShr => format!("(bvlshr {} {})", left, right),
            BinOp::Eq => format!("(ite (= {} {}) #x00000001 #x00000000)", left, right),
            BinOp::Ne => format!("(ite (not (= {} {})) #x00000001 #x00000000)", left, right),
            BinOp::Lt => format!("(ite (bvslt {} {}) #x00000001 #x00000000)", left, right),
            BinOp::Le => format!("(ite (bvsle {} {}) #x00000001 #x00000000)", left, right),
            BinOp::Gt => format!("(ite (bvsgt {} {}) #x00000001 #x00000000)", left, right),
            BinOp::Ge => format!("(ite (bvsge {} {}) #x00000001 #x00000000)", left, right),
        }
    }

    fn encode_neg(&self, operand: &str) -> String {
        format!("(bvneg {})", operand)
    }

    fn encode_cast(&self, ty: &Ty, _from: &Ty, operand: &str) -> String {
        match ty {
            Ty::Long => format!("((_ sign_extend 32) {})", operand),
            Ty::Int => format!("((_ extract 31 0) {})", operand),
            _ => operand.to_string(),
        }
    }

    fn encode_cmp(&self, left: &str, right: &str) -> String {
        format!(
            "(ite (bvslt {} {}) #xffffffff (ite (= {} {}) #x00000000 #x00000001))",
            left, right, left, right
        )
    }

    fn models_binop(&self, _op: &BinOp) -> bool {
        // Bitvectors have every Java integer operator, with Java's semantics:
        // bvsdiv and bvsrem truncate toward zero, the shifts and bitwise
        // operators are exact, and arithmetic wraps.
        true
    }

    fn models_cast(&self, to: &Ty, from: &Ty) -> bool {
        // Sign-extension and truncation are exact on bitvectors, so every
        // integer cast is faithful. A cast touching a float is not: a
        // bitvector holds a float's *bit pattern*, and `((_ extract 31 0) p)`
        // is not `d2i` of the number that pattern denotes.
        !(matches!(to, Ty::Float | Ty::Double) || matches!(from, Ty::Float | Ty::Double))
    }

    fn sort_of(&self, wide: bool) -> String {
        if wide {
            "(_ BitVec 64)".into()
        } else {
            "(_ BitVec 32)".into()
        }
    }

    fn needs_overflow_guard(&self) -> bool {
        // Bitvectors wrap exactly as Java does, so there is nothing to guard.
        false
    }

    fn encode_nonzero(&self, operand: &str) -> String {
        format!("(not (= {} #x00000000))", operand)
    }

    fn encode_is_zero(&self, operand: &str) -> String {
        format!("(= {} #x00000000)", operand)
    }
}

// ---------------------------------------------------------------------------
// Linear integer arithmetic theory (used by interpolation, IMC, CEGAR)
// ---------------------------------------------------------------------------

pub struct LiaTheory {
    pub prefix: String,
}

impl LiaTheory {
    pub fn new(prefix: &str) -> Self {
        Self {
            prefix: prefix.to_string(),
        }
    }
}

impl SmtTheory for LiaTheory {
    fn encode_int(&self, value: i32) -> String {
        if value < 0 {
            format!("(- {})", -(value as i64))
        } else {
            value.to_string()
        }
    }
    fn encode_long(&self, value: i64) -> String {
        if value < 0 {
            format!("(- {})", -value)
        } else {
            value.to_string()
        }
    }
    fn encode_null(&self) -> String {
        "0".to_string()
    }
    fn encode_non_null(&self) -> String {
        "1".to_string()
    }
    fn encode_zero(&self) -> String {
        "0".to_string()
    }
    fn encode_true(&self) -> String {
        "1".to_string()
    }
    fn encode_false(&self) -> String {
        "0".to_string()
    }

    fn encode_binop(&self, op: &BinOp, left: &str, right: &str) -> String {
        match op {
            BinOp::Add => format!("(+ {} {})", left, right),
            BinOp::Sub => format!("(- {} {})", left, right),
            BinOp::Mul => format!("(* {} {})", left, right),
            BinOp::Eq => format!("(ite (= {} {}) 1 0)", left, right),
            BinOp::Ne => format!("(ite (not (= {} {})) 1 0)", left, right),
            BinOp::Lt => format!("(ite (< {} {}) 1 0)", left, right),
            BinOp::Le => format!("(ite (<= {} {}) 1 0)", left, right),
            BinOp::Gt => format!("(ite (> {} {}) 1 0)", left, right),
            BinOp::Ge => format!("(ite (>= {} {}) 1 0)", left, right),
            // Unreachable: `models_binop` rejects these, so `Encoder` allocates
            // an unconstrained binder before reaching the theory.
            _ => unreachable!("LiaTheory asked to encode {op:?}, which it cannot model"),
        }
    }

    fn encode_neg(&self, operand: &str) -> String {
        format!("(- 0 {})", operand)
    }

    fn encode_cast(&self, _to: &Ty, _from: &Ty, operand: &str) -> String {
        // Only widening reaches here; `models_cast` rejects narrowing.
        operand.to_string()
    }

    fn encode_cmp(&self, left: &str, right: &str) -> String {
        format!(
            "(ite (< {} {}) (- 1) (ite (= {} {}) 0 1))",
            left, right, left, right
        )
    }

    fn models_binop(&self, op: &BinOp) -> bool {
        !matches!(
            op,
            // No bitwise or shift operators in LIA, and `div`/`mod` are
            // Euclidean where Java's `/` and `%` truncate toward zero.
            BinOp::Div
                | BinOp::Rem
                | BinOp::And
                | BinOp::Or
                | BinOp::Xor
                | BinOp::Shl
                | BinOp::Shr
                | BinOp::UShr
        )
    }

    fn models_cast(&self, to: &Ty, from: &Ty) -> bool {
        // No cast touching a float type, in either direction. This is not a
        // width question, and treating it as one is what made `f2i` look
        // faithful: `lia_width(Float)` is 32, so `models_cast(Int, Float)` was
        // `32 >= 32` and `encode_cast` returned the operand unchanged -- a
        // float's bit pattern copied into an integer variable. `(int) 3.7` is
        // `3`, and LIA has no term for either side of that.
        //
        // `Encoder::rvalue`'s quarantine means a float cast no longer reaches
        // here at all. This stays correct anyway, because `models_cast` is a
        // public claim about what the theory can express and the old answer
        // was false.
        if matches!(to, Ty::Float | Ty::Double) || matches!(from, Ty::Float | Ty::Double) {
            return false;
        }
        // Widening is the identity on the value; narrowing truncates, which
        // LIA cannot express.
        lia_width(to) >= lia_width(from)
    }

    fn sort_of(&self, _wide: bool) -> String {
        "Int".into()
    }

    fn needs_overflow_guard(&self) -> bool {
        true
    }

    fn encode_nonzero(&self, operand: &str) -> String {
        format!("(not (= {} 0))", operand)
    }

    fn encode_is_zero(&self, operand: &str) -> String {
        format!("(= {} 0)", operand)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::{BinOp, CmpKind, Const, Operand, Rvalue, Ty, VarId};

    /// v0: int, v1: double, v2: long, v3: float.
    fn ty_of(op: &Operand) -> Option<Ty> {
        match op {
            Operand::Const(c) => Some(c.ty()),
            Operand::Var(VarId(0)) => Some(Ty::Int),
            Operand::Var(VarId(1)) => Some(Ty::Double),
            Operand::Var(VarId(2)) => Some(Ty::Long),
            Operand::Var(VarId(3)) => Some(Ty::Float),
            // Deliberately unresolvable, to exercise the `None` path.
            _ => None,
        }
    }

    fn lia(rv: &Rvalue) -> (String, Vec<String>) {
        let theory = LiaTheory::new("");
        let mut enc = Encoder::new(&theory, "f_");
        let vars: Vec<String> = (0..8).map(|i| format!("v{i}")).collect();
        let e = enc.rvalue(rv, &vars, &ty_of);
        (e, enc.side_conditions.clone())
    }

    fn v(i: u32) -> Operand {
        Operand::Var(VarId(i))
    }

    /// Leak 1. `(+ bits bits)` is not `dadd`. An unconstrained binder contains
    /// the real result; an integer sum of two IEEE-754 bit patterns does not.
    #[test]
    fn float_arithmetic_becomes_an_unconstrained_binder() {
        for rv in [
            Rvalue::Bin(BinOp::Add, v(1), v(1)),
            Rvalue::Bin(BinOp::Mul, v(3), Operand::int(2)),
            Rvalue::Bin(BinOp::Sub, Operand::Const(Const::Double(1.5)), v(0)),
            Rvalue::Neg(v(1)),
        ] {
            let (e, side) = lia(&rv);
            assert!(e.starts_with("f_f"), "{rv:?} must be havoced, got {e}");
            // And the bogus overflow condition over bit patterns is gone with
            // it. It used to reach `error_formulas`, where a disjunct that is
            // satisfiable for unrelated reasons weakens every proof using it.
            assert!(
                side.is_empty(),
                "{rv:?} must not emit an overflow condition over bit patterns: {side:?}"
            );
        }
    }

    /// Integer arithmetic is untouched, including its overflow condition —
    /// otherwise the test above would pass for a stub that havocs everything.
    #[test]
    fn integer_arithmetic_is_still_encoded_and_still_guarded() {
        let (e, side) = lia(&Rvalue::Bin(BinOp::Add, v(0), Operand::int(1)));
        assert_eq!(e, "(+ v0 1)");
        assert_eq!(side.len(), 1, "an int add needs its overflow condition");
        assert!(side[0].contains("2147483647"), "32-bit bound: {}", side[0]);

        let (e, side) = lia(&Rvalue::Bin(BinOp::Add, v(2), v(2)));
        assert_eq!(e, "(+ v2 v2)");
        assert!(
            side[0].contains("9223372036854775807"),
            "a long add is guarded at 64 bits: {}",
            side[0]
        );
    }

    /// Leak 2. `dcmpg` is not an integer comparison of bit patterns: every
    /// negative double has its sign bit set, so the integer order is not the
    /// float order. `lcmp` is, and must still be encoded.
    #[test]
    fn a_float_comparison_is_havoced_and_lcmp_is_not() {
        let (e, _) = lia(&Rvalue::Cmp(CmpKind::FloatG, v(1), v(1)));
        assert!(e.starts_with("f_f"), "dcmpg must be havoced, got {e}");

        let (e, _) = lia(&Rvalue::Cmp(CmpKind::Long, v(2), v(2)));
        assert!(
            e.starts_with("(ite"),
            "lcmp is faithful in LIA and must stay encoded, got {e}"
        );
    }

    /// The `CmpKind` is the bytecode's own answer, so it holds where the
    /// operand types do not resolve. Without this, a float comparison whose
    /// variables the caller could not type would be encoded as an integer one.
    #[test]
    fn a_float_comparison_is_havoced_even_when_operand_types_are_unknown() {
        let (e, _) = lia(&Rvalue::Cmp(CmpKind::FloatL, v(7), v(7)));
        assert_eq!(ty_of(&v(7)), None, "v7 must be unresolvable for this test");
        assert!(e.starts_with("f_f"), "must be havoced, got {e}");
    }

    /// Leak 3. `lia_width(Float)` is 32, so the old width test called `f2i` a
    /// widening and `encode_cast` returned the operand unchanged — a bit
    /// pattern copied into an integer variable. Every direction is declined.
    #[test]
    fn no_cast_touching_a_float_is_modelled() {
        let theory = LiaTheory::new("");
        for (to, from) in [
            (Ty::Int, Ty::Float),
            (Ty::Int, Ty::Double),
            (Ty::Float, Ty::Int),
            (Ty::Double, Ty::Long),
            (Ty::Double, Ty::Float),
            (Ty::Float, Ty::Double),
        ] {
            assert!(
                !theory.models_cast(&to, &from),
                "LIA must decline {from:?} -> {to:?}"
            );
            assert!(
                !BitvectorTheory.models_cast(&to, &from),
                "bitvectors hold a float's bit pattern, so must decline {from:?} -> {to:?}"
            );
            let (e, _) = lia(&Rvalue::Cast(to, from, v(0)));
            assert!(e.starts_with("f_f"), "{from:?} -> {to:?} gave {e}");
        }
        // Integer casts are unaffected: widening is the identity in LIA, and
        // narrowing is still declined for its own reason.
        assert!(theory.models_cast(&Ty::Long, &Ty::Int));
        assert!(!theory.models_cast(&Ty::Int, &Ty::Long));
        assert!(BitvectorTheory.models_cast(&Ty::Int, &Ty::Long));
    }

    /// A quarantined 64-bit value must not become a 32-bit binder. LIA cannot
    /// see the difference (`sort_of` answers `Int` either way) but the
    /// bitvector theory can, and a sort mismatch is an error rather than an
    /// imprecision.
    #[test]
    fn a_quarantined_binder_has_the_width_of_the_result_not_of_the_operands() {
        let mut enc = Encoder::new(&BitvectorTheory, "b_");
        let vars: Vec<String> = (0..8).map(|i| format!("v{i}")).collect();

        enc.rvalue(&Rvalue::Bin(BinOp::Add, v(1), v(1)), &vars, &ty_of);
        assert_eq!(enc.binders.last().unwrap().1, "(_ BitVec 64)");

        // `dcmpg` takes two 64-bit operands and pushes an `int`.
        enc.rvalue(&Rvalue::Cmp(CmpKind::FloatG, v(1), v(1)), &vars, &ty_of);
        assert_eq!(enc.binders.last().unwrap().1, "(_ BitVec 32)");

        // A cast's result width is its destination's, not its source's.
        enc.rvalue(&Rvalue::Cast(Ty::Double, Ty::Int, v(0)), &vars, &ty_of);
        assert_eq!(enc.binders.last().unwrap().1, "(_ BitVec 64)");
        enc.rvalue(&Rvalue::Cast(Ty::Int, Ty::Double, v(1)), &vars, &ty_of);
        assert_eq!(enc.binders.last().unwrap().1, "(_ BitVec 32)");
    }

    /// Why `encode_operand`'s `Const(_) => encode_zero()` arm is left alone.
    ///
    /// A `double` constant still encodes as `0`, which is a wrong value rather
    /// than an unknown — but the quarantine *contains* it: the only rvalue that
    /// reads a float constant and is not havoced is `Use`, which copies it into
    /// a float-typed variable, and no integer-valued term reads a float
    /// variable any more. This test is that containment argument, so that
    /// removing the quarantine breaks a test naming the reason.
    #[test]
    fn a_float_constant_never_reaches_an_integer_term() {
        let c = Operand::Const(Const::Double(3.5));
        assert_eq!(encode_operand(&LiaTheory::new(""), &c, &Vec::new()), "0");
        for rv in [
            Rvalue::Bin(BinOp::Add, c.clone(), v(0)),
            Rvalue::Neg(c.clone()),
            Rvalue::Cmp(CmpKind::FloatG, c.clone(), v(0)),
            Rvalue::Cast(Ty::Int, Ty::Double, c.clone()),
        ] {
            let (e, _) = lia(&rv);
            assert!(
                e.starts_with("f_f"),
                "a float constant must not be computed on: {rv:?} gave {e}"
            );
        }
        // The one surviving reader, and it writes a float-typed variable.
        let (e, _) = lia(&Rvalue::Use(c));
        assert_eq!(e, "0");
    }
}
