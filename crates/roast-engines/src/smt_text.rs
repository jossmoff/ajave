//! Shared SMT-LIB2 text encoding for operands and rvalues.
//!
//! CHC uses bitvector theory; interpolation/IMC/CEGAR use linear integer
//! arithmetic. The structure of operand and rvalue encoding is identical
//! across both — only the constants and operator names differ. This module
//! captures that shared structure via the `SmtTheory` trait.

use roast_ir::*;

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
    fn encode_cast(&self, ty: &Ty, operand: &str) -> String;
    fn encode_cmp(&self, left: &str, right: &str) -> String;
    fn encode_fresh(&self) -> String;

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

/// Encode an rvalue using the given theory and variable lookup.
pub fn encode_rvalue<T: SmtTheory, V: VarLookup>(
    theory: &T,
    rvalue: &Rvalue,
    vars: &V,
) -> String {
    match rvalue {
        Rvalue::Use(o) => encode_operand(theory, o, vars),
        Rvalue::Nondet(..) | Rvalue::Havoc(_) => theory.encode_fresh(),
        Rvalue::Bin(op, a, b) => {
            let left = encode_operand(theory, a, vars);
            let right = encode_operand(theory, b, vars);
            theory.encode_binop(op, &left, &right)
        }
        Rvalue::Neg(o) => {
            let operand = encode_operand(theory, o, vars);
            theory.encode_neg(&operand)
        }
        Rvalue::Cast(ty, o) => {
            let operand = encode_operand(theory, o, vars);
            theory.encode_cast(ty, &operand)
        }
        Rvalue::Cmp(a, b) => {
            let left = encode_operand(theory, a, vars);
            let right = encode_operand(theory, b, vars);
            theory.encode_cmp(&left, &right)
        }
        _ => theory.encode_fresh(),
    }
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

    fn encode_cast(&self, ty: &Ty, operand: &str) -> String {
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

    fn encode_fresh(&self) -> String {
        static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let id = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        format!("bv_fresh{id}")
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
            BinOp::Div => format!("(div {} {})", left, right),
            BinOp::Rem => format!("(mod {} {})", left, right),
            BinOp::Eq => format!("(ite (= {} {}) 1 0)", left, right),
            BinOp::Ne => format!("(ite (not (= {} {})) 1 0)", left, right),
            BinOp::Lt => format!("(ite (< {} {}) 1 0)", left, right),
            BinOp::Le => format!("(ite (<= {} {}) 1 0)", left, right),
            BinOp::Gt => format!("(ite (> {} {}) 1 0)", left, right),
            BinOp::Ge => format!("(ite (>= {} {}) 1 0)", left, right),
            // Bitwise operations: not available in LIA, use fresh unconstrained.
            _ => self.encode_fresh(),
        }
    }

    fn encode_neg(&self, operand: &str) -> String {
        format!("(- 0 {})", operand)
    }

    fn encode_cast(&self, _ty: &Ty, operand: &str) -> String {
        operand.to_string()
    }

    fn encode_cmp(&self, left: &str, right: &str) -> String {
        format!(
            "(ite (< {} {}) (- 1) (ite (= {} {}) 0 1))",
            left, right, left, right
        )
    }

    fn encode_fresh(&self) -> String {
        static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let id = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        format!("{}fresh{id}", self.prefix)
    }

    fn encode_nonzero(&self, operand: &str) -> String {
        format!("(not (= {} 0))", operand)
    }

    fn encode_is_zero(&self, operand: &str) -> String {
        format!("(= {} 0)", operand)
    }
}
