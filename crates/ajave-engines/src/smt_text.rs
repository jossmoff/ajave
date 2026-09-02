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
pub fn encode_operand<T: SmtTheory, V: VarLookup>(
    theory: &T,
    op: &Operand,
    vars: &V,
) -> String {
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
    /// `wide` reports whether an operand is 64-bit, which the IR carries on the
    /// variable rather than on the operation.
    pub fn rvalue<V: VarLookup>(
        &mut self,
        rv: &Rvalue,
        vars: &V,
        wide: &dyn Fn(&Operand) -> bool,
    ) -> String {
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

    fn models_cast(&self, _to: &Ty, _from: &Ty) -> bool {
        true
    }

    fn sort_of(&self, wide: bool) -> String {
        if wide { "(_ BitVec 64)".into() } else { "(_ BitVec 32)".into() }
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
            BinOp::Div | BinOp::Rem | BinOp::And | BinOp::Or | BinOp::Xor
                | BinOp::Shl | BinOp::Shr | BinOp::UShr
        )
    }

    fn models_cast(&self, to: &Ty, from: &Ty) -> bool {
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
