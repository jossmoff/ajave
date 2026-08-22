//! Benchmark shape analysis.
//!
//! One walk over a method body producing every structural fact any engine
//! needs to decide whether it can handle that body. The portfolio uses this to
//! select a solver and theory per benchmark instead of running every engine on
//! everything.
//!
//! **This is the only walk.** There used to be a second one in
//! `body_analysis::body_uses_havoced_ops`, computing an overlapping predicate
//! by hand, and the two disagreed: it counted any `Rvalue::Call` as a havoced
//! operation while `has_heap_ops` did not. So `suitable_for_proving()`
//! (`!has_heap_ops`) would have admitted a body full of unmodelled calls that
//! `body_uses_havoced_ops` exists specifically to reject -- a false TRUE
//! waiting for its first caller, which it never got because
//! `suitable_for_proving` was dead code. Both predicates now derive from the
//! fields below, so they cannot drift again.
//!
//! Note that the two predicates remain deliberately *different*, which is why
//! this struct records calls and heap access separately rather than merging
//! them: a transcendental-math body is nothing but calls, and NRA has to accept
//! it, while the LIA/bitvector proving engines have to reject it.

use roast_ir::*;

/// Summary of which language features a method body uses.
#[derive(Clone, Debug, Default)]
pub struct BodyShape {
    /// Uses transcendental Math calls (sin, cos, exp, log, pow, sqrt, etc.).
    pub has_transcendental_math: bool,
    /// Reads or writes the heap: field access, static access, instance-of, or
    /// an explicit `Havoc`. Does *not* include method calls — see `has_calls`.
    pub has_heap_ops: bool,
    /// Contains at least one `Rvalue::Call`. Tracked separately from
    /// `has_heap_ops` because the two have different consumers: an unresolved
    /// call is havoc as far as a simplified proving encoding is concerned, but
    /// a `Math.sin` call is exactly what the NRA engine wants to see.
    pub has_calls: bool,
    /// Uses string operations.
    pub has_string_ops: bool,
    /// Uses array operations.
    pub has_array_ops: bool,
    /// Has back-edges (loops).
    pub has_loops: bool,
    /// Uses nonlinear integer arithmetic (multiplication of two variables).
    pub has_nonlinear_int: bool,
    /// Uses floating-point types.
    pub has_float_types: bool,
    /// Number of variables.
    pub num_vars: usize,
    /// Number of blocks.
    pub num_blocks: usize,
}

/// Analyze a method body and return a shape summary.
pub fn analyze(body: &Body) -> BodyShape {
    let mut shape = BodyShape {
        num_vars: body.vars.len(),
        num_blocks: body.blocks.len(),
        ..Default::default()
    };

    // Check variable types for floats/doubles.
    for var_info in &body.vars {
        if matches!(var_info.ty, Ty::Float | Ty::Double) {
            shape.has_float_types = true;
            break;
        }
    }

    shape.has_loops = crate::body_analysis::body_has_loops(body);

    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(_, rvalue) => analyze_rvalue(rvalue, &mut shape),
                Stmt::PutField { .. } => shape.has_heap_ops = true,
                // PutStatic and ArrayStore are deliberately *not* recorded as
                // heap ops, matching what the predicate this replaces did. They
                // are unobservable within a single body unless it also reads
                // them back, and the corresponding reads (GetStatic, ArrayLoad)
                // are what the encoders actually have to worry about.
                _ => {}
            }
        }
    }

    shape
}

fn analyze_rvalue(rvalue: &Rvalue, shape: &mut BodyShape) {
    match rvalue {
        Rvalue::Call { target, .. } => {
            shape.has_calls = true;
            if roast_models::is_transcendental_math(&target.class, &target.name) {
                shape.has_transcendental_math = true;
                shape.has_float_types = true;
            }
            if roast_models::STR_OWNERS.contains(&target.class.as_str()) {
                shape.has_string_ops = true;
            }
        }
        Rvalue::GetStatic(_)
        | Rvalue::GetField { .. }
        | Rvalue::InstanceOf { .. }
        | Rvalue::Havoc(_) => {
            shape.has_heap_ops = true;
        }
        Rvalue::ArrayLoad { .. } | Rvalue::ArrayLength(_) | Rvalue::NewArray { .. } => {
            shape.has_array_ops = true;
        }
        Rvalue::Bin(BinOp::Mul, Operand::Var(_), Operand::Var(_)) => {
            shape.has_nonlinear_int = true;
        }
        _ => {}
    }
}

impl BodyShape {
    /// Does this body use an operation the simplified SMT/LIA encodings leave
    /// unconstrained?
    ///
    /// The shared soundness guard of the whole proving half of the portfolio
    /// (k-induction, IMC, CEGAR, CHC). Those encodings model integer arithmetic
    /// and nothing else, so an UNSAT over a body containing anything else would
    /// look exactly like a proof while proving nothing. Method calls count:
    /// the encodings are intraprocedural, so a callee's effects are invisible.
    pub fn uses_havoced_ops(&self) -> bool {
        self.has_heap_ops || self.has_calls
    }

    /// Returns `true` if the body is suitable for proving engines that use
    /// simplified encodings (CHC, IMC, CEGAR, k-induction).
    pub fn suitable_for_proving(&self) -> bool {
        !self.uses_havoced_ops()
    }

    /// Returns `true` if the body is suitable for the NRA (nonlinear real
    /// arithmetic) engine — i.e. it uses transcendental math and doesn't
    /// use heap operations that the NRA encoding can't model.
    ///
    /// Deliberately does not exclude `has_calls`: a transcendental body is made
    /// of calls, and those calls are precisely what this engine encodes.
    pub fn suitable_for_nra(&self) -> bool {
        self.has_transcendental_math && !self.has_heap_ops
    }
}
