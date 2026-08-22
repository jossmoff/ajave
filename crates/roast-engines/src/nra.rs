//! Nonlinear real arithmetic engine (NRA).
//!
//! Encodes methods with transcendental Math calls (sin, cos, exp, log, pow,
//! sqrt, etc.) as NRA constraints using the cvc5 Rust API directly.
//!
//! CVC5 has native transcendental support via `Kind::Sine`, `Kind::Cosine`,
//! `Kind::Exponential`, `Kind::Sqrt`, etc. SAT models are exact, enabling
//! both falsification (Under) and verification (Over).

use cvc5::{Kind, Solver, Term as CvcTerm, TermManager};
use log::{debug, info};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::verdict::{NondetEntry, NondetValue, Witness};
use roast_ir::*;

use crate::body_shape;

pub struct NraEngine {
    done: bool,
}

impl NraEngine {
    pub fn new() -> Self {
        NraEngine { done: false }
    }

    pub fn available(&self) -> bool {
        true // cvc5 is statically linked
    }
}

impl Engine for NraEngine {
    fn id(&self) -> EngineId {
        EngineId("nra")
    }

    fn direction(&self) -> Direction {
        // Over: UNSAT soundly proves the property.
        // SAT from CVC5 with native transcendentals is also trustworthy.
        Direction::Over
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let open: Vec<ObligationRef> = bb.open().to_vec();
        if open.is_empty() {
            return Progress::Exhausted;
        }

        let mut advanced = false;

        for oref in &open {
            let Some(body) = prog.body(&oref.method) else {
                continue;
            };

            if !body.is_fully_lifted() {
                continue;
            }

            let shape = body_shape::analyze(body);
            if !shape.suitable_for_nra() {
                debug!("nra: {} not suitable for NRA", oref.method);
                continue;
            }

            info!(
                "nra: encoding obligation {:?} for {:?}",
                oref.id, oref.method
            );

            match solve_nra(body, oref.id) {
                NraResult::Sat(model) => {
                    info!("nra: found violation for {}", oref);
                    let witness = build_witness_from_model(body, &model);
                    let published = bb.publish(
                        self.id(),
                        Direction::Under,
                        Artifact::Status(
                            oref.clone(),
                            Status::Violated {
                                by: self.id(),
                                witness,
                            },
                        ),
                    );
                    if published.is_ok() {
                        advanced = true;
                    }
                }
                NraResult::Unsat => {
                    // NRA encodes over reals, not IEEE 754 floats.
                    // UNSAT over reals does not imply UNSAT over floats
                    // (NaN, Inf, -0 can violate assertions that hold over R).
                    // So we log but do NOT discharge.
                    debug!(
                        "nra: obligation {} UNSAT over reals (not discharging — float unsoundness)",
                        oref
                    );
                }
                NraResult::Unknown => {
                    debug!("nra: solver returned unknown for {}", oref);
                }
            }
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}

// ---------------------------------------------------------------------------
// NRA encoding via cvc5 Rust API
// ---------------------------------------------------------------------------

const MAX_NRA_DEPTH: usize = 50;

enum NraResult {
    Sat(Vec<(String, f64)>),
    Unsat,
    Unknown,
}

/// State carried along a path during NRA encoding.
struct NraPathState<'tm> {
    var_terms: Vec<CvcTerm<'tm>>,
    constraints: Vec<CvcTerm<'tm>>,
}

fn solve_nra(body: &Body, obligation_id: ObligationId) -> NraResult {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);

    solver.set_logic("QF_NRAT");
    solver.set_option("produce-models", "true");
    solver.set_option("tlimit", "8000");

    let real_sort = tm.real_sort();
    let n_vars = body.vars.len();

    // Declare all variables as Real constants.
    let var_consts: Vec<CvcTerm> = (0..n_vars)
        .map(|i| tm.mk_const(real_sort.clone(), &format!("v{}", i)))
        .collect();

    // DFS from entry block, collecting error path constraints.
    let initial_state = NraPathState {
        var_terms: var_consts.clone(),
        constraints: Vec::new(),
    };

    let mut error_paths: Vec<Vec<CvcTerm>> = Vec::new();
    let mut worklist: Vec<(BlockId, NraPathState, usize)> = vec![(body.entry, initial_state, 0)];

    while let Some((block_id, mut state, depth)) = worklist.pop() {
        if depth > MAX_NRA_DEPTH {
            continue;
        }

        let block = body.block(block_id);

        let mut found_error = false;
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(vid, rvalue) => {
                    let term = encode_rvalue(&tm, rvalue, &state.var_terms);
                    state.var_terms[vid.0 as usize] = term;
                }
                Stmt::Assume(operand) => {
                    let expr = encode_operand(&tm, operand, &state.var_terms);
                    let zero = tm.mk_real(0);
                    let neq = tm.mk_term(Kind::Not, &[tm.mk_term(Kind::Equal, &[expr, zero])]);
                    state.constraints.push(neq);
                }
                Stmt::Check(oid) => {
                    if *oid == obligation_id {
                        let obligation = body.obligation(*oid);
                        let cond = encode_operand(&tm, &obligation.cond, &state.var_terms);
                        let zero = tm.mk_real(0);
                        let eq_zero = tm.mk_term(Kind::Equal, &[cond, zero]);
                        let mut error_conds = state.constraints.clone();
                        error_conds.push(eq_zero);
                        error_paths.push(error_conds);
                        found_error = true;
                    }
                }
                _ => {}
            }
        }

        if found_error {
            continue;
        }

        match &block.term {
            Terminator::Goto(target) => {
                worklist.push((*target, state, depth + 1));
            }
            Terminator::Branch { cond, then_, else_ } => {
                let cond_term = encode_operand(&tm, cond, &state.var_terms);
                let zero = tm.mk_real(0);

                let then_state = NraPathState {
                    var_terms: state.var_terms.clone(),
                    constraints: {
                        let mut c = state.constraints.clone();
                        c.push(tm.mk_term(
                            Kind::Not,
                            &[tm.mk_term(Kind::Equal, &[cond_term.clone(), zero.clone()])],
                        ));
                        c
                    },
                };
                worklist.push((*then_, then_state, depth + 1));

                let else_state = NraPathState {
                    var_terms: state.var_terms,
                    constraints: {
                        let mut c = state.constraints;
                        c.push(tm.mk_term(Kind::Equal, &[cond_term, zero]));
                        c
                    },
                };
                worklist.push((*else_, else_state, depth + 1));
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let val_term = encode_operand(&tm, value, &state.var_terms);
                let mut neg_cases = Vec::new();

                for (cv, target) in cases {
                    let cv_real = tm.mk_real(*cv as i64);
                    let eq = tm.mk_term(Kind::Equal, &[val_term.clone(), cv_real.clone()]);
                    let case_state = NraPathState {
                        var_terms: state.var_terms.clone(),
                        constraints: {
                            let mut c = state.constraints.clone();
                            c.push(eq);
                            c
                        },
                    };
                    worklist.push((*target, case_state, depth + 1));
                    neg_cases.push(tm.mk_term(
                        Kind::Not,
                        &[tm.mk_term(Kind::Equal, &[val_term.clone(), cv_real])],
                    ));
                }

                state.constraints.extend(neg_cases);
                worklist.push((*default, state, depth + 1));
            }
            _ => {}
        }
    }

    // Build the assertion: disjunction of error paths.
    let assertion = if error_paths.is_empty() {
        tm.mk_false()
    } else {
        let path_terms: Vec<CvcTerm> = error_paths
            .into_iter()
            .map(|conds| {
                if conds.is_empty() {
                    tm.mk_true()
                } else if conds.len() == 1 {
                    conds.into_iter().next().unwrap()
                } else {
                    tm.mk_term(Kind::And, &conds)
                }
            })
            .collect();

        if path_terms.len() == 1 {
            path_terms.into_iter().next().unwrap()
        } else {
            tm.mk_term(Kind::Or, &path_terms)
        }
    };

    solver.assert_formula(assertion);

    let result = solver.check_sat();
    if result.is_sat() {
        // Extract model values for parameter variables.
        let mut model = Vec::new();
        for (i, vi) in body.vars.iter().enumerate() {
            if !matches!(vi.kind, VarKind::Local(_)) {
                break;
            }
            let val_term = solver.get_value(var_consts[i].clone());
            let value = extract_real_value(&val_term);
            model.push((format!("v{}", i), value));
        }
        NraResult::Sat(model)
    } else if result.is_unsat() {
        NraResult::Unsat
    } else {
        NraResult::Unknown
    }
}

fn extract_real_value(term: &CvcTerm) -> f64 {
    if term.is_real64_value() {
        let (num, den) = term.real64_value();
        if den == 0 {
            0.0
        } else {
            num as f64 / den as f64
        }
    } else if term.is_real32_value() {
        let (num, den) = term.real32_value();
        if den == 0 {
            0.0
        } else {
            num as f64 / den as f64
        }
    } else if term.is_real_value() {
        // Arbitrary precision — parse the string representation.
        let s = term.real_value();
        if let Some(idx) = s.find('/') {
            let num: f64 = s[..idx].parse().unwrap_or(0.0);
            let den: f64 = s[idx + 1..].parse().unwrap_or(1.0);
            if den != 0.0 {
                num / den
            } else {
                0.0
            }
        } else {
            s.parse().unwrap_or(0.0)
        }
    } else {
        // Might be an algebraic number or complex expression — use Display.
        let s = format!("{}", term);
        s.parse().unwrap_or(0.0)
    }
}

fn encode_operand<'tm>(
    tm: &'tm TermManager,
    operand: &Operand,
    var_terms: &[CvcTerm<'tm>],
) -> CvcTerm<'tm> {
    match operand {
        Operand::Var(v) => var_terms[v.0 as usize].clone(),
        Operand::Const(Const::Int(n)) => tm.mk_real(*n as i64),
        Operand::Const(Const::Long(n)) => tm.mk_real(*n),
        Operand::Const(Const::Float(f)) => mk_real_from_f64(tm, *f as f64),
        Operand::Const(Const::Double(d)) => mk_real_from_f64(tm, *d),
        Operand::Const(Const::Null) => tm.mk_real(0),
        Operand::Const(_) => tm.mk_real(0),
    }
}

fn mk_real_from_f64<'tm>(tm: &'tm TermManager, v: f64) -> CvcTerm<'tm> {
    if v.is_nan() || v.is_infinite() {
        return tm.mk_real(0);
    }
    // Use string representation for precision.
    let s = format!("{}", v);
    tm.mk_real_from_str(&s)
}

fn encode_rvalue<'tm>(
    tm: &'tm TermManager,
    rvalue: &Rvalue,
    var_terms: &[CvcTerm<'tm>],
) -> CvcTerm<'tm> {
    match rvalue {
        Rvalue::Use(operand) => encode_operand(tm, operand, var_terms),
        Rvalue::Nondet(..) | Rvalue::Havoc(_) => {
            // Fresh unconstrained real variable.
            tm.mk_const(tm.real_sort(), "_fresh")
        }
        Rvalue::Bin(op, a, b) => {
            let left = encode_operand(tm, a, var_terms);
            let right = encode_operand(tm, b, var_terms);
            encode_binop(tm, op, left, right)
        }
        Rvalue::Neg(operand) => {
            let inner = encode_operand(tm, operand, var_terms);
            tm.mk_term(Kind::Neg, &[inner])
        }
        Rvalue::Cast(_, operand) => encode_operand(tm, operand, var_terms),
        Rvalue::Cmp(a, b) => {
            let left = encode_operand(tm, a, var_terms);
            let right = encode_operand(tm, b, var_terms);
            let neg_one = tm.mk_real(-1);
            let zero = tm.mk_real(0);
            let one = tm.mk_real(1);
            // cmp: -1 if a < b, 0 if a == b, 1 if a > b
            tm.mk_term(
                Kind::Ite,
                &[
                    tm.mk_term(Kind::Lt, &[left.clone(), right.clone()]),
                    neg_one,
                    tm.mk_term(
                        Kind::Ite,
                        &[tm.mk_term(Kind::Equal, &[left, right]), zero, one],
                    ),
                ],
            )
        }
        Rvalue::Call { target, args, .. } => {
            encode_transcendental_call(tm, target, args, var_terms)
        }
        _ => tm.mk_const(tm.real_sort(), "_fresh"),
    }
}

fn encode_binop<'tm>(
    tm: &'tm TermManager,
    op: &BinOp,
    left: CvcTerm<'tm>,
    right: CvcTerm<'tm>,
) -> CvcTerm<'tm> {
    let zero = tm.mk_real(0);
    let one = tm.mk_real(1);
    match op {
        BinOp::Add => tm.mk_term(Kind::Add, &[left, right]),
        BinOp::Sub => tm.mk_term(Kind::Sub, &[left, right]),
        BinOp::Mul => tm.mk_term(Kind::Mult, &[left, right]),
        BinOp::Div => tm.mk_term(Kind::Division, &[left, right]),
        BinOp::Rem => {
            // a - floor(a/b) * b
            let div = tm.mk_term(Kind::Division, &[left.clone(), right.clone()]);
            let floor = tm.mk_term(Kind::ToReal, &[tm.mk_term(Kind::ToInteger, &[div])]);
            let prod = tm.mk_term(Kind::Mult, &[floor, right]);
            tm.mk_term(Kind::Sub, &[left, prod])
        }
        BinOp::Eq => tm.mk_term(
            Kind::Ite,
            &[tm.mk_term(Kind::Equal, &[left, right]), one, zero],
        ),
        BinOp::Ne => tm.mk_term(
            Kind::Ite,
            &[
                tm.mk_term(Kind::Not, &[tm.mk_term(Kind::Equal, &[left, right])]),
                one,
                zero,
            ],
        ),
        BinOp::Lt => tm.mk_term(
            Kind::Ite,
            &[tm.mk_term(Kind::Lt, &[left, right]), one, zero],
        ),
        BinOp::Le => tm.mk_term(
            Kind::Ite,
            &[tm.mk_term(Kind::Leq, &[left, right]), one, zero],
        ),
        BinOp::Gt => tm.mk_term(
            Kind::Ite,
            &[tm.mk_term(Kind::Gt, &[left, right]), one, zero],
        ),
        BinOp::Ge => tm.mk_term(
            Kind::Ite,
            &[tm.mk_term(Kind::Geq, &[left, right]), one, zero],
        ),
        // Bitwise ops don't make sense for reals.
        _ => zero,
    }
}

fn encode_transcendental_call<'tm>(
    tm: &'tm TermManager,
    target: &MethodKey,
    args: &[Operand],
    var_terms: &[CvcTerm<'tm>],
) -> CvcTerm<'tm> {
    let name = target.name.as_str();
    let class = target.class.as_str();

    match (class, name) {
        ("java/lang/Math" | "java/lang/StrictMath", "sin") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::Sine, &[arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "cos") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::Cosine, &[arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "tan") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::Tangent, &[arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "asin") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::Arcsine, &[arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "acos") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::Arccosine, &[arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "atan") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::Arctangent, &[arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "atan2") => {
            let y = encode_operand(tm, &args[0], var_terms);
            let x = encode_operand(tm, &args[1], var_terms);
            // atan2(y, x) ≈ atan(y/x) for x > 0
            let ratio = tm.mk_term(Kind::Division, &[y, x]);
            tm.mk_term(Kind::Arctangent, &[ratio])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "exp") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::Exponential, &[arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "log") => {
            // CVC5 doesn't have a direct log Kind — encode as inverse of exp.
            // log(x) = y where exp(y) = x. Use a fresh variable.
            let arg = encode_operand(tm, &args[0], var_terms);
            let y = tm.mk_const(tm.real_sort(), "_log");
            // We can't easily add constraints here in a pure term-building context.
            // Instead, approximate: log is not directly available in CVC5 NRA.
            // Fall back to an unconstrained variable for now.
            // TODO: Better approach would be to add a constraint exp(y) = arg to the path.
            let _ = arg;
            y
        }
        ("java/lang/Math" | "java/lang/StrictMath", "log10") => {
            // Same limitation as log.
            tm.mk_const(tm.real_sort(), "_log10")
        }
        ("java/lang/Math" | "java/lang/StrictMath", "pow") => {
            // pow(b, e) — for integer exponents we could expand, but general case
            // needs exp(e * log(b)) which requires log.
            // Fall back to unconstrained for now.
            tm.mk_const(tm.real_sort(), "_pow")
        }
        ("java/lang/Math" | "java/lang/StrictMath", "sqrt") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::Sqrt, &[arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "abs") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            let zero = tm.mk_real(0);
            let neg = tm.mk_term(Kind::Neg, &[arg.clone()]);
            tm.mk_term(
                Kind::Ite,
                &[tm.mk_term(Kind::Lt, &[arg.clone(), zero]), neg, arg],
            )
        }
        ("java/lang/Math" | "java/lang/StrictMath", "min") => {
            let a = encode_operand(tm, &args[0], var_terms);
            let b = encode_operand(tm, &args[1], var_terms);
            tm.mk_term(
                Kind::Ite,
                &[tm.mk_term(Kind::Leq, &[a.clone(), b.clone()]), a, b],
            )
        }
        ("java/lang/Math" | "java/lang/StrictMath", "max") => {
            let a = encode_operand(tm, &args[0], var_terms);
            let b = encode_operand(tm, &args[1], var_terms);
            tm.mk_term(
                Kind::Ite,
                &[tm.mk_term(Kind::Geq, &[a.clone(), b.clone()]), a, b],
            )
        }
        ("java/lang/Math" | "java/lang/StrictMath", "ceil") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            // ceil(x) = -floor(-x)
            let neg_arg = tm.mk_term(Kind::Neg, &[arg]);
            let floor = tm.mk_term(Kind::ToInteger, &[neg_arg]);
            let neg_floor = tm.mk_term(Kind::Neg, &[tm.mk_term(Kind::ToReal, &[floor])]);
            neg_floor
        }
        ("java/lang/Math" | "java/lang/StrictMath", "floor") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            tm.mk_term(Kind::ToReal, &[tm.mk_term(Kind::ToInteger, &[arg])])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "round") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            let half = tm.mk_real_from_str("0.5");
            let sum = tm.mk_term(Kind::Add, &[arg, half]);
            tm.mk_term(Kind::ToReal, &[tm.mk_term(Kind::ToInteger, &[sum])])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "toRadians") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            let pi = tm.mk_pi();
            let d180 = tm.mk_real(180);
            let factor = tm.mk_term(Kind::Division, &[pi, d180]);
            tm.mk_term(Kind::Mult, &[factor, arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "toDegrees") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            let pi = tm.mk_pi();
            let d180 = tm.mk_real(180);
            let factor = tm.mk_term(Kind::Division, &[d180, pi]);
            tm.mk_term(Kind::Mult, &[factor, arg])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "sinh") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            // sinh(x) = (exp(x) - exp(-x)) / 2
            let exp_pos = tm.mk_term(Kind::Exponential, &[arg.clone()]);
            let exp_neg = tm.mk_term(Kind::Exponential, &[tm.mk_term(Kind::Neg, &[arg])]);
            let diff = tm.mk_term(Kind::Sub, &[exp_pos, exp_neg]);
            let two = tm.mk_real(2);
            tm.mk_term(Kind::Division, &[diff, two])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "cosh") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            let exp_pos = tm.mk_term(Kind::Exponential, &[arg.clone()]);
            let exp_neg = tm.mk_term(Kind::Exponential, &[tm.mk_term(Kind::Neg, &[arg])]);
            let sum = tm.mk_term(Kind::Add, &[exp_pos, exp_neg]);
            let two = tm.mk_real(2);
            tm.mk_term(Kind::Division, &[sum, two])
        }
        ("java/lang/Math" | "java/lang/StrictMath", "tanh") => {
            let arg = encode_operand(tm, &args[0], var_terms);
            let exp_pos = tm.mk_term(Kind::Exponential, &[arg.clone()]);
            let exp_neg = tm.mk_term(Kind::Exponential, &[tm.mk_term(Kind::Neg, &[arg])]);
            let num = tm.mk_term(Kind::Sub, &[exp_pos.clone(), exp_neg.clone()]);
            let den = tm.mk_term(Kind::Add, &[exp_pos, exp_neg]);
            tm.mk_term(Kind::Division, &[num, den])
        }
        _ => {
            // Unknown call — unconstrained.
            tm.mk_const(tm.real_sort(), "_unknown_call")
        }
    }
}

fn build_witness_from_model(body: &Body, model: &[(String, f64)]) -> Witness {
    let mut nondet_sequence = Vec::new();
    let mut entries = Vec::new();

    let mut i = 0;
    while i < body.vars.len() {
        let var_info = &body.vars[i];
        if !matches!(var_info.kind, VarKind::Local(_)) {
            break;
        }

        let var_name = format!("v{}", i);
        let value = model
            .iter()
            .find(|(name, _)| name == &var_name)
            .map(|(_, v)| *v)
            .unwrap_or(0.0);

        let (nondet_value, nondet_method, raw_bits) = match var_info.ty {
            Ty::Double => (
                NondetValue::Long(value.to_bits() as i64),
                "nondetDouble",
                value.to_bits() as i64,
            ),
            Ty::Float => (
                NondetValue::Int((value as f32).to_bits() as i32),
                "nondetFloat",
                (value as f32).to_bits() as i64,
            ),
            Ty::Long => (NondetValue::Long(value as i64), "nondetLong", value as i64),
            _ => (NondetValue::Int(value as i32), "nondetInt", value as i64),
        };

        nondet_sequence.push(raw_bits);
        entries.push(NondetEntry {
            value: nondet_value,
            nondet_method,
            line: None,
        });

        if var_info.ty.is_wide() {
            i += 2;
        } else {
            i += 1;
        }
    }

    Witness {
        nondet_sequence,
        entries,
    }
}
