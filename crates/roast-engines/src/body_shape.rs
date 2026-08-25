//! Benchmark shape analysis.
//!
//! Inspects a method body and produces a `BodyShape` summary describing which
//! language features it uses. The engine portfolio uses this to select the
//! most effective solver and theory for each benchmark.

use roast_ir::*;

/// Summary of which language features a method body uses.
#[derive(Clone, Debug, Default)]
pub struct BodyShape {
    /// Uses transcendental Math calls (sin, cos, exp, log, pow, sqrt, etc.).
    pub has_transcendental_math: bool,
    /// Uses heap operations (field access, instance-of, method calls, havoc).
    pub has_heap_ops: bool,
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

    // Check for loops via back-edges.
    shape.has_loops = crate::body_analysis::body_has_loops(body);

    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(_, rvalue) => analyze_rvalue(rvalue, &mut shape),
                Stmt::PutField { .. } => {
                    shape.has_heap_ops = true;
                }
                _ => {}
            }
        }
    }

    shape
}

fn analyze_rvalue(rvalue: &Rvalue, shape: &mut BodyShape) {
    match rvalue {
        Rvalue::Call { target, .. } => {
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
    /// Returns `true` if the body is suitable for the NRA (nonlinear real
    /// arithmetic) engine — i.e. it uses transcendental math or float types
    /// and doesn't use heap operations that the NRA encoding can't model.
    pub fn suitable_for_nra(&self) -> bool {
        (self.has_transcendental_math || self.has_float_types) && !self.has_heap_ops
    }

    /// Returns `true` if the body is suitable for proving engines that use
    /// simplified encodings (CHC, IMC, CEGAR, k-induction).
    pub fn suitable_for_proving(&self) -> bool {
        !self.has_heap_ops
    }
}
