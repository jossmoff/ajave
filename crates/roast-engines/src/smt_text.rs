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

    /// Takes the fresh pool because not every theory can express every
    /// operator: LIA has no bitwise operations and has to havoc them.
    fn encode_binop(&self, op: &BinOp, left: &str, right: &str, fresh: &mut FreshPool) -> String;

    /// Can this theory express `&`, `|`, `^` and the shifts exactly?
    fn supports_bitwise(&self) -> bool;
    fn encode_neg(&self, operand: &str) -> String;
    fn encode_cast(&self, ty: &Ty, operand: &str) -> String;
    fn encode_cmp(&self, left: &str, right: &str) -> String;

    /// How this theory declares a symbol of the given bit width. CHC emits a
    /// sorted bitvector binding; LIA ignores the width and emits `Int`.
    fn declare_sort(&self, width: u32) -> String;

    fn encode_nonzero(&self, operand: &str) -> String;
    fn encode_is_zero(&self, operand: &str) -> String;
}

/// A source of fresh symbols, and the record of every one handed out.
///
/// Replaces a `SmtTheory::encode_fresh` that minted names from a global
/// `AtomicU64` and told nobody. Two things were wrong with that. The names were
/// never bound anywhere -- neither declared nor quantified -- so any body
/// containing a `Nondet`, an array read or an allocation produced a script with
/// an undeclared symbol in it, and z3 answers such a script by *dropping the
/// offending clause* and printing a verdict anyway. And a global counter makes
/// the emitted text depend on how many bodies were encoded earlier in the
/// process, so the same input produced different scripts run to run.
///
/// Callers must bind everything in `issued` -- CHC by extending the clause's
/// `forall` prefix, LIA by emitting declarations.
#[derive(Debug, Default)]
pub struct FreshPool {
    prefix: String,
    next: u32,
    issued: Vec<(String, u32)>,
}

impl FreshPool {
    pub fn new(prefix: &str) -> Self {
        FreshPool {
            prefix: prefix.to_string(),
            next: 0,
            issued: Vec::new(),
        }
    }

    /// Mint a symbol of the given bit width and record it for binding.
    pub fn make(&mut self, width: u32) -> String {
        let name = format!("{}fresh{}", self.prefix, self.next);
        self.next += 1;
        self.issued.push((name.clone(), width));
        name
    }

    /// Every symbol handed out so far, with its width.
    pub fn issued(&self) -> &[(String, u32)] {
        &self.issued
    }

    /// Symbols handed out since `mark`, for callers that bind per clause.
    pub fn issued_since(&self, mark: usize) -> &[(String, u32)] {
        &self.issued[mark.min(self.issued.len())..]
    }

    pub fn mark(&self) -> usize {
        self.issued.len()
    }
}

/// Bit width an rvalue's result occupies. Only Long/Double are wide.
pub fn width_of_ty(ty: &Ty) -> u32 {
    match ty {
        Ty::Long | Ty::Double => 64,
        _ => 32,
    }
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

/// Encode an rvalue using the given theory and variable lookup.
///
/// Anything this cannot express precisely becomes a fresh symbol from `fresh`,
/// which the caller is then obliged to bind. `is_precise` says in advance which
/// rvalues those are, from the same match, so a guard cannot drift out of step
/// with the encoder.
pub fn encode_rvalue<T: SmtTheory, V: VarLookup>(
    theory: &T,
    rvalue: &Rvalue,
    vars: &V,
    fresh: &mut FreshPool,
) -> String {
    match rvalue {
        Rvalue::Use(o) => encode_operand(theory, o, vars),
        Rvalue::Nondet(ty, _) => fresh.make(width_of_ty(ty)),
        Rvalue::Havoc(ty) => fresh.make(width_of_ty(ty)),
        Rvalue::Bin(op, a, b) => {
            let left = encode_operand(theory, a, vars);
            let right = encode_operand(theory, b, vars);
            theory.encode_binop(op, &left, &right, fresh)
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
        // Everything else -- field and array reads, allocations, calls,
        // instance-of -- is unmodelled. `is_precise` reports the same set.
        _ => fresh.make(32),
    }
}

/// Does `encode_rvalue` express this rvalue exactly under `theory`, or fall
/// back to a fresh unconstrained symbol? Kept adjacent to the match above so
/// the two stay in agreement.
pub fn is_precise<T: SmtTheory>(theory: &T, rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Bin(op, ..) => match op {
            BinOp::And | BinOp::Or | BinOp::Xor | BinOp::Shl | BinOp::Shr | BinOp::UShr => {
                theory.supports_bitwise()
            }
            _ => true,
        },
        Rvalue::Use(_) | Rvalue::Neg(_) | Rvalue::Cast(..) | Rvalue::Cmp(..) => true,
        _ => false,
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

    fn encode_binop(&self, op: &BinOp, left: &str, right: &str, fresh: &mut FreshPool) -> String {
        let _ = &mut *fresh;
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

    fn declare_sort(&self, width: u32) -> String {
        format!("(_ BitVec {width})")
    }

    fn supports_bitwise(&self) -> bool {
        true
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

    fn encode_binop(&self, op: &BinOp, left: &str, right: &str, fresh: &mut FreshPool) -> String {
        let _ = &mut *fresh;
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
            // Bitwise operations: not available in LIA, so havoc. `is_precise`
            // reports this via `supports_bitwise`, which is what keeps the
            // proving engines from trusting a result over such a body.
            _ => fresh.make(32),
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

    fn declare_sort(&self, _width: u32) -> String {
        "Int".to_string()
    }

    fn supports_bitwise(&self) -> bool {
        false
    }

    fn encode_nonzero(&self, operand: &str) -> String {
        format!("(not (= {} 0))", operand)
    }

    fn encode_is_zero(&self, operand: &str) -> String {
        format!("(= {} 0)", operand)
    }
}

// ---------------------------------------------------------------------------
// The shared per-block walk
// ---------------------------------------------------------------------------
//
// CHC and the LIA encoder used to carry a copy each of the loop below: seed a
// variable map, fold assignments into it, collect `Assume`s as path conditions,
// emit an error clause per `Check`, then switch on the terminator. Around 120
// lines apiece, and they had already drifted -- CHC ignores `Return` and `Halt`
// where the LIA version emits a clause for them.
//
// `SmtTheory` had factored out the leaves (constants, operators) but not the
// walk. This is the walk. What differs between the two encoders is only what
// they *do* with each edge, which is `ClauseSink`.

/// One outgoing edge of a block, fully encoded and ready to be rendered.
pub struct Transition<'a> {
    pub from: BlockId,
    /// `None` for a terminator that leaves the body (`Return`, `Halt`).
    pub to: Option<BlockId>,
    /// Path conditions plus any edge-specific guard (branch taken, switch case).
    pub conds: &'a [String],
    /// Equalities binding each variable's post-state, `(= v3' <expr>)`-shaped
    /// once the sink applies its own naming.
    pub var_exprs: &'a [String],
    /// Bindings introduced for intermediate results in this block.
    pub bindings: &'a [String],
    /// Fresh symbols this block introduced, which the sink must bind.
    pub fresh: &'a [(String, u32)],
}

/// An obligation that can be violated in this block.
pub struct ErrorSite<'a> {
    pub block: BlockId,
    pub obligation: ObligationId,
    /// Path conditions plus "the safety condition is zero".
    pub conds: &'a [String],
    pub bindings: &'a [String],
    pub fresh: &'a [(String, u32)],
}

/// What an encoder does with the edges the walk produces.
pub trait ClauseSink {
    fn transition(&mut self, t: Transition<'_>);
    fn error(&mut self, e: ErrorSite<'_>);
}

/// Walk every block of `body`, encoding statements with `theory` and handing
/// each outgoing edge and error site to `sink`.
///
/// `obligations` selects which `Check` statements produce error sites; it is a
/// set rather than a slice because both callers were doing a linear `contains`
/// on it once per `Check`.
pub fn walk_body<T: SmtTheory, S: ClauseSink>(
    body: &Body,
    theory: &T,
    obligations: &std::collections::HashSet<ObligationId>,
    fresh: &mut FreshPool,
    sink: &mut S,
) {
    let n_vars = body.vars.len();

    for block in &body.blocks {
        // Each variable starts the block holding its entry value. The sink
        // decides what "v3" actually renders as.
        let mut var_exprs: Vec<String> = (0..n_vars).map(|i| format!("v{i}")).collect();
        let mut path_conds: Vec<String> = Vec::new();
        let mut bindings: Vec<String> = Vec::new();
        let fresh_mark = fresh.mark();

        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(vid, rv) => {
                    let expr = encode_rvalue(theory, rv, &var_exprs, fresh);
                    // Name non-trivial results instead of substituting their
                    // text into the variable map. Substitution made a statement
                    // that mentions a variable twice double that variable's
                    // rendered size, so a block of n such statements produced a
                    // string of size O(2^n) with nothing bounding it before the
                    // solver saw it. Naming keeps the output linear in
                    // statements and hands the solver structure it can share.
                    if is_trivial_expr(&expr) {
                        var_exprs[vid.0 as usize] = expr;
                    } else {
                        let width = body
                            .vars
                            .get(vid.0 as usize)
                            .map(|v| width_of_ty(&v.ty))
                            .unwrap_or(32);
                        let tmp = fresh.make(width);
                        bindings.push(format!("(= {tmp} {expr})"));
                        var_exprs[vid.0 as usize] = tmp;
                    }
                }
                Stmt::Assume(op) => {
                    let expr = encode_operand(theory, op, &var_exprs);
                    path_conds.push(theory.encode_nonzero(&expr));
                }
                Stmt::Check(oid) if obligations.contains(oid) => {
                    let ob = body.obligation(*oid);
                    let cond_expr = encode_operand(theory, &ob.cond, &var_exprs);
                    let mut conds = path_conds.clone();
                    conds.push(theory.encode_is_zero(&cond_expr));
                    sink.error(ErrorSite {
                        block: block.id,
                        obligation: *oid,
                        conds: &conds,
                        bindings: &bindings,
                        fresh: fresh.issued_since(fresh_mark),
                    });
                }
                _ => {}
            }
        }

        let emit = |sink: &mut S, to: Option<BlockId>, extra: &[String], fresh: &FreshPool| {
            let mut conds = path_conds.clone();
            conds.extend_from_slice(extra);
            sink.transition(Transition {
                from: block.id,
                to,
                conds: &conds,
                var_exprs: &var_exprs,
                bindings: &bindings,
                fresh: fresh.issued_since(fresh_mark),
            });
        };

        match &block.term {
            Terminator::Goto(t) => emit(sink, Some(*t), &[], fresh),
            Terminator::Branch { cond, then_, else_ } => {
                let cond_expr = encode_operand(theory, cond, &var_exprs);
                let nz = theory.encode_nonzero(&cond_expr);
                let z = theory.encode_is_zero(&cond_expr);
                emit(sink, Some(*then_), std::slice::from_ref(&nz), fresh);
                emit(sink, Some(*else_), std::slice::from_ref(&z), fresh);
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let val_expr = encode_operand(theory, value, &var_exprs);
                let mut neg_cases = Vec::new();
                for (cv, target) in cases {
                    let eq = format!("(= {} {})", val_expr, theory.encode_int(*cv));
                    emit(sink, Some(*target), std::slice::from_ref(&eq), fresh);
                    neg_cases.push(format!("(not {eq})"));
                }
                emit(sink, Some(*default), &neg_cases, fresh);
            }
            // Leaving the body. CHC used to drop these silently while the LIA
            // encoder emitted a clause; now both see the edge and decide.
            Terminator::Return(_) | Terminator::Halt => emit(sink, None, &[], fresh),
            // Nothing sound to say past a Diverge, and an explicit Throw's
            // handler routing is not modelled by either text encoder.
            Terminator::Throw(_) | Terminator::Diverge(_) => {}
        }
    }
}

/// A bare symbol or literal — cheap enough to substitute rather than name.
fn is_trivial_expr(e: &str) -> bool {
    !e.starts_with('(')
}

/// Conjoin a list of SMT conditions, collapsing the degenerate cases.
pub fn conjoin(parts: &[String]) -> String {
    match parts.len() {
        0 => "true".to_string(),
        1 => parts[0].clone(),
        _ => format!("(and {})", parts.join(" ")),
    }
}
