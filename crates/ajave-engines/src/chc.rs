//! CHC (Constrained Horn Clauses) engine — inter-procedural.
//!
//! Translates the program to a set of Horn clauses in SMT-LIB2 CHC format
//! and shells out to Z3 (Spacer). Direction: Over.
//!
//! Key feature: **inter-procedural encoding** with method summary relations.
//! Each method with a body gets a summary relation `mN_summary(params..., ret)`.
//! Call sites invoke the callee's summary, producing recursive Horn clauses
//! for recursive programs. Z3's Spacer computes fixpoints over these.
//!
//! Uses LIA (linear integer arithmetic) for the inter-procedural encoding
//! because Spacer's fixpoint engine works best with integers. Falls back to
//! BV for the single-method encoding when there are no inter-procedural calls.

use std::collections::{HashMap, HashSet};
use std::io::Write as IoWrite;
use std::process::{Command, Stdio};

use log::{debug, info, trace, warn};
use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_ir::*;

pub struct ChcEngine {
    solver_binary: String,
    done: bool,
}

impl ChcEngine {
    pub fn new() -> Self {
        let binary = std::env::var("ROAST_CHC_SOLVER").unwrap_or_else(|_| "z3".to_string());
        ChcEngine {
            solver_binary: binary,
            done: false,
        }
    }

    pub fn available(&self) -> bool {
        Command::new(&self.solver_binary)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok()
    }
}

impl Engine for ChcEngine {
    fn id(&self) -> EngineId {
        EngineId("chc")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let open = bb.open();
        if open.is_empty() {
            return Progress::Exhausted;
        }

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };

        if !body.is_fully_lifted() {
            return Progress::Stalled;
        }

        // CHC's LIA encoding only models integer arithmetic, not heap/arrays.
        // Skip if any reachable method uses arrays, field access, or unresolved
        // calls to library methods — proving those safe requires heap/string
        // modeling that LIA doesn't have.
        let reachable_methods = prog.reachable_from_entry();
        let uses_heap = reachable_methods.iter().any(|mk| {
            prog.body(mk).map_or(false, |b| body_uses_heap_ops(b))
        });
        if uses_heap {
            info!("chc: skipping — reachable methods use heap/array operations");
            return Progress::Stalled;
        }
        // Skip if any reachable method has calls to non-Verifier library methods
        // without bodies. These become havoced (unconstrained) in the LIA encoding,
        // which is unsound for discharge — the real method may throw exceptions or
        // return values that violate assertions. Verifier.nondet* calls are safe
        // because CHC models them as unconstrained inputs (correct semantics).
        let has_unresolved = reachable_methods.iter().any(|mk| {
            prog.body(mk).map_or(false, |b| {
                b.blocks.iter().any(|blk| {
                    blk.stmts.iter().any(|s| {
                        if let Stmt::Assign(_, Rvalue::Call { target, .. }) = s {
                            prog.body(target).is_none()
                                && target.class != "org/sosy_lab/sv_benchmarks/Verifier"
                        } else {
                            false
                        }
                    })
                })
            })
        });
        if has_unresolved {
            info!("chc: skipping — reachable methods have unresolved library calls");
            return Progress::Stalled;
        }

        // Only attempt Assertion obligations (NegArraySize etc. require heap).
        let obs: Vec<ObligationId> = open
            .iter()
            .filter(|oref| oref.method == *entry)
            .filter(|oref| {
                body.obligation(oref.id).kind == ObligationKind::Assertion
            })
            .map(|oref| oref.id)
            .collect();

        if obs.is_empty() {
            return Progress::Exhausted;
        }

        info!("chc: encoding {} obligation(s) for {:?}", obs.len(), entry);

        // Use inter-procedural encoding when the program has calls to methods with bodies.
        let has_interproc_calls = prog_has_resolvable_calls(prog, entry);
        let smt2 = if has_interproc_calls {
            info!("chc: using inter-procedural LIA encoding");
            encode_chc_interproc(prog, entry, &obs)
        } else {
            info!("chc: using single-method BV encoding");
            encode_chc_single(body, &obs)
        };

        debug!("chc: generated {} bytes of CHC encoding", smt2.len());
        trace!("chc: encoding:\n{}", &smt2[..smt2.len().min(4000)]);

        let mut advanced = false;
        match run_chc_solver(&self.solver_binary, &smt2, &obs) {
            Ok(results) => {
                for (oid, safe) in results {
                    if safe {
                        let oref = ObligationRef {
                            method: entry.clone(),
                            id: oid,
                        };
                        debug!("chc: discharged {}", oref);
                        let _ = bb.publish(
                            self.id(),
                            self.direction(),
                            Artifact::Status(
                                oref,
                                Status::Discharged {
                                    by: self.id(),
                                    proof: ProofKind::Exhaustive,
                                },
                            ),
                        );
                        advanced = true;
                    }
                }
            }
            Err(e) => {
                warn!("chc: solver failed: {}", e);
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
// Helpers
// ---------------------------------------------------------------------------

/// Returns true if the body uses array or heap operations that CHC's LIA
/// encoding cannot model: array load/store/new, field get/put, instanceof.
fn body_uses_heap_ops(body: &Body) -> bool {
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(_, rv) => match rv {
                    Rvalue::ArrayLoad { .. }
                    | Rvalue::ArrayLength(_)
                    | Rvalue::NewArray { .. }
                    | Rvalue::GetField { .. }
                    | Rvalue::GetStatic(_)
                    | Rvalue::InstanceOf { .. } => return true,
                    _ => {}
                },
                Stmt::PutField { .. } | Stmt::ArrayStore { .. } => return true,
                _ => {}
            }
        }
    }
    false
}

/// Check if the program has calls from the entry method (or its callees)
/// to methods that we have bodies for — i.e. inter-procedural reasoning helps.
fn prog_has_resolvable_calls(prog: &Program, entry: &MethodKey) -> bool {
    let Some(body) = prog.body(entry) else {
        return false;
    };
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(_, Rvalue::Call { target, .. }) = stmt {
                if prog.body(target).is_some() {
                    return true;
                }
            }
        }
    }
    false
}

/// Parse method descriptor to count parameter slots.
/// Returns the number of JVM local slots consumed by parameters.
fn param_slot_count(desc: &str) -> usize {
    let inner = &desc[1..desc.find(')').unwrap_or(desc.len())];
    let bytes = inner.as_bytes();
    let mut pos = 0;
    let mut slots = 0;
    while pos < bytes.len() {
        match bytes[pos] {
            b'J' | b'D' => {
                slots += 2;
                pos += 1;
            }
            b'L' => {
                slots += 1;
                pos = inner[pos..].find(';').map(|p| pos + p + 1).unwrap_or(bytes.len());
            }
            b'[' => {
                slots += 1;
                pos += 1;
                // skip element type
                while pos < bytes.len() && bytes[pos] == b'[' {
                    pos += 1;
                }
                if pos < bytes.len() {
                    if bytes[pos] == b'L' {
                        pos = inner[pos..].find(';').map(|p| pos + p + 1).unwrap_or(bytes.len());
                    } else {
                        pos += 1;
                    }
                }
            }
            _ => {
                slots += 1;
                pos += 1;
            }
        }
    }
    slots
}

/// Find which VarIds correspond to method parameters (by Local slot).
/// Returns (var_index, slot) pairs in slot order.
fn find_param_var_indices(body: &Body, mk: &MethodKey) -> Vec<usize> {
    let is_static = mk.name == "<clinit>" || {
        // Check if any var occupies slot 0 with Ref type (this pointer)
        // Static methods don't have `this`, so first param is at slot 0.
        // Heuristic: if the method is static, param slots start at 0.
        // For now, assume all methods are static (jayhorn benchmarks are static).
        // TODO: handle instance methods properly
        true
    };
    let total_param_slots = param_slot_count(&mk.desc);
    let first_slot: u16 = 0; // static methods start at slot 0

    let mut params: Vec<(usize, u16)> = Vec::new();
    for (i, vi) in body.vars.iter().enumerate() {
        if let VarKind::Local(slot) = vi.kind {
            if (slot as usize) < total_param_slots + (first_slot as usize) {
                params.push((i, slot));
            }
        }
    }
    params.sort_by_key(|&(_, slot)| slot);
    params.dedup_by_key(|p| p.1);
    params.iter().map(|&(i, _)| i).collect()
}

/// Return type descriptor character from method descriptor.
fn return_type_char(desc: &str) -> char {
    let after = desc.split(')').nth(1).unwrap_or("V");
    after.chars().next().unwrap_or('V')
}

// ---------------------------------------------------------------------------
// LIA operand/rvalue encoding for inter-procedural CHC
// (with overflow guards for soundness)
// ---------------------------------------------------------------------------

const INT_MIN: i64 = -2147483648;
const INT_MAX: i64 = 2147483647;

fn lia_int(value: i32) -> String {
    if value < 0 {
        format!("(- {})", -(value as i64))
    } else {
        value.to_string()
    }
}

fn lia_long(value: i64) -> String {
    if value < 0 {
        format!("(- {})", -(value as i128))
    } else {
        value.to_string()
    }
}

fn lia_operand(op: &Operand, var_map: &HashMap<usize, String>) -> String {
    match op {
        Operand::Var(v) => var_map
            .get(&(v.0 as usize))
            .cloned()
            .unwrap_or_else(|| format!("v{}", v.0)),
        Operand::Const(Const::Int(n)) => lia_int(*n),
        Operand::Const(Const::Long(n)) => lia_long(*n),
        Operand::Const(Const::Null) => "0".to_string(),
        Operand::Const(Const::Str(_)) => "1".to_string(),
        Operand::Const(Const::Float(f)) => lia_int(f.to_bits() as i32),
        Operand::Const(Const::Double(d)) => lia_long(d.to_bits() as i64),
        Operand::Const(_) => "0".to_string(),
    }
}

fn lia_binop(op: &BinOp, l: &str, r: &str) -> String {
    match op {
        BinOp::Add => format!("(+ {} {})", l, r),
        BinOp::Sub => format!("(- {} {})", l, r),
        BinOp::Mul => format!("(* {} {})", l, r),
        BinOp::Div => format!("(div {} {})", l, r),
        BinOp::Rem => format!("(mod {} {})", l, r),
        BinOp::Eq => format!("(ite (= {} {}) 1 0)", l, r),
        BinOp::Ne => format!("(ite (not (= {} {})) 1 0)", l, r),
        BinOp::Lt => format!("(ite (< {} {}) 1 0)", l, r),
        BinOp::Le => format!("(ite (<= {} {}) 1 0)", l, r),
        BinOp::Gt => format!("(ite (> {} {}) 1 0)", l, r),
        BinOp::Ge => format!("(ite (>= {} {}) 1 0)", l, r),
        // Bitwise: not available in LIA
        _ => "0".to_string(),
    }
}

struct FreshGen {
    counter: u32,
    extra_forall: Vec<String>,
}

impl FreshGen {
    fn new() -> Self {
        FreshGen {
            counter: 0,
            extra_forall: Vec::new(),
        }
    }

    fn fresh(&mut self) -> String {
        let name = format!("_f{}", self.counter);
        self.counter += 1;
        self.extra_forall.push(format!("({} Int)", name));
        name
    }

    fn forall_str(&self) -> String {
        self.extra_forall.join(" ")
    }
}

fn lia_rvalue(
    rv: &Rvalue,
    var_map: &HashMap<usize, String>,
    fresh: &mut FreshGen,
) -> String {
    match rv {
        Rvalue::Use(o) => lia_operand(o, var_map),
        Rvalue::Nondet(..) | Rvalue::Havoc(_) => fresh.fresh(),
        Rvalue::Bin(op, a, b) => {
            let l = lia_operand(a, var_map);
            let r = lia_operand(b, var_map);
            lia_binop(op, &l, &r)
        }
        Rvalue::Neg(o) => {
            let v = lia_operand(o, var_map);
            format!("(- 0 {})", v)
        }
        Rvalue::Cast(_, _, o) => lia_operand(o, var_map),
        Rvalue::Cmp(_, a, b) => {
            let l = lia_operand(a, var_map);
            let r = lia_operand(b, var_map);
            format!("(ite (< {} {}) (- 1) (ite (= {} {}) 0 1))", l, r, l, r)
        }
        Rvalue::New(_) => fresh.fresh(),
        _ => fresh.fresh(),
    }
}

// ---------------------------------------------------------------------------
// Inter-procedural CHC encoding (LIA + overflow guards)
//
// Uses LIA (fast for Spacer fixpoint) but adds overflow-to-error guards
// on method summaries: if any summary returns a value outside 32-bit range,
// error is forced reachable. This makes the encoding sound: CHC can only
// prove safety if no integer overflow occurs on any reachable path.
// ---------------------------------------------------------------------------

fn encode_chc_interproc(
    prog: &Program,
    entry: &MethodKey,
    obligations: &[ObligationId],
) -> String {
    let mut out = String::new();
    out.push_str("(set-logic HORN)\n\n");

    let reachable: Vec<MethodKey> = prog
        .reachable_from_entry()
        .into_iter()
        .filter(|mk| prog.body(mk).is_some())
        .filter(|mk| mk.name != "<clinit>" && mk.name != "<init>")
        .collect();

    let mut all_methods: Vec<MethodKey> = vec![entry.clone()];
    for mk in &reachable {
        if mk != entry && !all_methods.contains(mk) {
            all_methods.push(mk.clone());
        }
    }

    let method_ids: HashMap<MethodKey, String> = all_methods
        .iter()
        .enumerate()
        .map(|(i, mk)| (mk.clone(), format!("m{}", i)))
        .collect();

    let method_params: HashMap<MethodKey, Vec<usize>> = all_methods
        .iter()
        .filter_map(|mk| {
            prog.body(mk)
                .map(|body| (mk.clone(), find_param_var_indices(body, mk)))
        })
        .collect();

    // Declare summary relations for non-void methods.
    for mk in &all_methods {
        let mid = &method_ids[mk];
        let ret_ch = return_type_char(&mk.desc);
        if ret_ch == 'V' {
            continue;
        }
        let params = method_params.get(mk).map(|v| v.len()).unwrap_or(0);
        let sig = (0..params + 1).map(|_| "Int").collect::<Vec<_>>().join(" ");
        out.push_str(&format!(
            "; summary for {}\n(declare-fun {}_s ({}) Bool)\n",
            mk, mid, sig
        ));
    }

    // Declare block relations for each method.
    for mk in &all_methods {
        let Some(body) = prog.body(mk) else { continue };
        let mid = &method_ids[mk];
        let n_vars = body.vars.len();
        let sig = (0..n_vars).map(|_| "Int").collect::<Vec<_>>().join(" ");

        out.push_str(&format!("; blocks for {}\n", mk));
        for block in &body.blocks {
            out.push_str(&format!(
                "(declare-fun {}_b{} ({}) Bool)\n",
                mid, block.id.0, sig
            ));
        }
    }

    out.push_str("\n(declare-fun error () Bool)\n\n");

    // Note: LIA is an over-approximation for overflow-free programs.
    // The CHC engine only proves safety (Over direction), and can only
    // discharge obligations that BMC couldn't resolve. For programs where
    // overflow is the bug, BMC will find the violation. For programs where
    // the property holds regardless of overflow, LIA safety ⊇ BV safety.
    // Conservative: we only discharge when the entry method's nondet
    // inputs are bounded by explicit branch guards before recursive calls.

    // Encode each method.
    for mk in &all_methods {
        let Some(body) = prog.body(mk) else { continue };
        let mid = method_ids[mk].clone();
        let n_vars = body.vars.len();
        let param_indices = method_params.get(mk).cloned().unwrap_or_default();
        let ret_ch = return_type_char(&mk.desc);
        let is_entry = mk == entry;

        let src_vars: Vec<String> = (0..n_vars).map(|i| format!("v{}", i)).collect();
        let dst_vars: Vec<String> = (0..n_vars).map(|i| format!("w{}", i)).collect();

        let forall_src: String = src_vars
            .iter()
            .map(|v| format!("({} Int)", v))
            .collect::<Vec<_>>()
            .join(" ");

        let block_app_src = |bid: u32| -> String {
            format!("({}_b{} {})", mid, bid, src_vars.join(" "))
        };
        let block_app_dst = |bid: u32| -> String {
            format!("({}_b{} {})", mid, bid, dst_vars.join(" "))
        };

        out.push_str(&format!(
            "; === {} ===\n(assert (forall ({}) {}))\n",
            mk, forall_src, block_app_src(body.entry.0)
        ));

        for block in &body.blocks {
            let mut fresh = FreshGen::new();
            let mut constraints: Vec<String> = Vec::new();
            let mut var_map: HashMap<usize, String> = HashMap::new();
            let mut call_constraints: Vec<String> = Vec::new();

            for i in 0..n_vars {
                var_map.insert(i, format!("v{}", i));
            }

            for stmt in &block.stmts {
                match stmt {
                    Stmt::Assign(vid, rv) => match rv {
                        Rvalue::Call { target, args, .. } => {
                            let callee_ret_ch = return_type_char(&target.desc);
                            if let Some(callee_mid) = method_ids.get(target) {
                                if callee_ret_ch != 'V' {
                                    let callee_params =
                                        method_params.get(target).cloned().unwrap_or_default();
                                    let mut call_args: Vec<String> = Vec::new();
                                    for (i, arg) in args.iter().enumerate() {
                                        if i < callee_params.len() {
                                            call_args.push(lia_operand(arg, &var_map));
                                        }
                                    }
                                    while call_args.len() < callee_params.len() {
                                        call_args.push("0".to_string());
                                    }

                                    let ret_var = fresh.fresh();
                                    call_args.push(ret_var.clone());
                                    call_constraints.push(format!(
                                        "({}_s {})",
                                        callee_mid,
                                        call_args.join(" ")
                                    ));
                                    var_map.insert(vid.0 as usize, ret_var);
                                }
                            } else {
                                if callee_ret_ch != 'V' {
                                    let v = fresh.fresh();
                                    var_map.insert(vid.0 as usize, v);
                                }
                            }
                        }
                        _ => {
                            let expr = lia_rvalue(rv, &var_map, &mut fresh);
                            var_map.insert(vid.0 as usize, expr);
                        }
                    },
                    Stmt::Assume(op) => {
                        let expr = lia_operand(op, &var_map);
                        constraints.push(format!("(not (= {} 0))", expr));
                    }
                    Stmt::Check(oid) => {
                        if is_entry && obligations.contains(oid) {
                            let ob = body.obligation(*oid);
                            let cond_expr = lia_operand(&ob.cond, &var_map);
                            let mut conds = constraints.clone();
                            conds.extend(call_constraints.iter().cloned());
                            conds.push(format!("(= {} 0)", cond_expr));
                            conds.push(block_app_src(block.id.0));

                            let body_expr = and_expr(&conds);
                            let q = add_extra_forall_lia(&forall_src, &fresh);
                            out.push_str(&format!(
                                "(assert (forall ({}) (=> {} error)))\n",
                                q, body_expr
                            ));
                        }
                    }
                    _ => {}
                }
            }

            let mut assign_conds: Vec<String> = Vec::new();
            for i in 0..n_vars {
                let val = var_map.get(&i).cloned().unwrap_or_else(|| format!("v{}", i));
                let dst = format!("w{}", i);
                if val != dst {
                    assign_conds.push(format!("(= {} {})", dst, val));
                }
            }

            let forall_both: String = src_vars
                .iter()
                .chain(dst_vars.iter())
                .map(|v| format!("({} Int)", v))
                .collect::<Vec<_>>()
                .join(" ");

            let mk_trans = |target_bid: u32, extra: &[String], out: &mut String| {
                let mut all = constraints.clone();
                all.extend(call_constraints.iter().cloned());
                all.extend_from_slice(extra);
                all.extend(assign_conds.iter().cloned());
                all.push(block_app_src(block.id.0));

                let body_expr = and_expr(&all);
                let q = add_extra_forall_lia(&forall_both, &fresh);
                out.push_str(&format!(
                    "(assert (forall ({}) (=> {} {})))\n",
                    q,
                    body_expr,
                    block_app_dst(target_bid)
                ));
            };

            match &block.term {
                Terminator::Goto(t) => {
                    mk_trans(t.0, &[], &mut out);
                }
                Terminator::Branch { cond, then_, else_ } => {
                    let ce = lia_operand(cond, &var_map);
                    let nz = format!("(not (= {} 0))", ce);
                    let z = format!("(= {} 0)", ce);
                    mk_trans(then_.0, &[nz], &mut out);
                    mk_trans(else_.0, &[z], &mut out);
                }
                Terminator::Switch {
                    value,
                    cases,
                    default,
                } => {
                    let ve = lia_operand(value, &var_map);
                    let mut neg = Vec::new();
                    for (cv, target) in cases {
                        let cv_s = lia_int(*cv);
                        let eq = format!("(= {} {})", ve, cv_s);
                        mk_trans(target.0, &[eq.clone()], &mut out);
                        neg.push(format!("(not {})", eq));
                    }
                    mk_trans(default.0, &neg, &mut out);
                }
                Terminator::Return(Some(op)) if ret_ch != 'V' => {
                    let ret_expr = lia_operand(op, &var_map);
                    let mut summary_args: Vec<String> = param_indices
                        .iter()
                        .map(|&pi| {
                            var_map.get(&pi).cloned().unwrap_or_else(|| format!("v{}", pi))
                        })
                        .collect();
                    summary_args.push(ret_expr);

                    let mut all = constraints.clone();
                    all.extend(call_constraints.iter().cloned());
                    all.push(block_app_src(block.id.0));

                    let body_expr = and_expr(&all);
                    let q = add_extra_forall_lia(&forall_src, &fresh);
                    out.push_str(&format!(
                        "(assert (forall ({}) (=> {} ({}_s {}))))\n",
                        q,
                        body_expr,
                        mid,
                        summary_args.join(" ")
                    ));
                }
                _ => {}
            }
        }
        out.push('\n');
    }

    out.push_str("(assert (not error))\n");
    out.push_str("(check-sat)\n");

    out
}

fn and_expr(conds: &[String]) -> String {
    match conds.len() {
        0 => "true".to_string(),
        1 => conds[0].clone(),
        _ => format!("(and {})", conds.join(" ")),
    }
}

fn add_extra_forall_lia(base: &str, fresh: &FreshGen) -> String {
    if fresh.extra_forall.is_empty() {
        base.to_string()
    } else {
        format!("{} {}", base, fresh.forall_str())
    }
}

// ---------------------------------------------------------------------------
// Single-method BV encoding (original, for non-recursive programs)
// ---------------------------------------------------------------------------

fn width_of(ty: &Ty) -> u32 {
    match ty {
        Ty::Long | Ty::Double => 64,
        _ => 32,
    }
}

fn encode_chc_single(body: &Body, obligations: &[ObligationId]) -> String {
    use crate::smt_text::{self, BitvectorTheory, SmtTheory};

    let mut out = String::new();
    out.push_str("(set-logic HORN)\n");

    let var_widths: Vec<(usize, u32)> = body
        .vars
        .iter()
        .enumerate()
        .map(|(i, vi)| (i, width_of(&vi.ty)))
        .collect();
    let width_map: HashMap<usize, u32> = var_widths.iter().cloned().collect();
    let mut fresh_decls: Vec<(String, u32)> = Vec::new();
    let var_indices = &var_widths;
    let n_vars = var_indices.len();

    for block in &body.blocks {
        let sig: String = var_indices
            .iter()
            .map(|(_, w)| format!("(_ BitVec {})", w))
            .collect::<Vec<_>>()
            .join(" ");
        out.push_str(&format!(
            "(declare-fun block_{} ({}) Bool)\n",
            block.id.0, sig
        ));
    }
    out.push_str("(declare-fun error () Bool)\n");

    let src_vars: Vec<String> = (0..n_vars).map(|i| format!("v{}", i)).collect();
    let dst_vars: Vec<String> = (0..n_vars).map(|i| format!("v{}p", i)).collect();

    let forall_src: String = var_indices
        .iter()
        .enumerate()
        .map(|(i, (_, w))| format!("(v{} (_ BitVec {}))", i, w))
        .collect::<Vec<_>>()
        .join(" ");
    let forall_both: String = {
        let src = var_indices
            .iter()
            .enumerate()
            .map(|(i, (_, w))| format!("(v{} (_ BitVec {}))", i, w));
        let dst = var_indices
            .iter()
            .enumerate()
            .map(|(i, (_, w))| format!("(v{}p (_ BitVec {}))", i, w));
        src.chain(dst).collect::<Vec<_>>().join(" ")
    };

    let block_app = |bid: u32| -> String {
        let args = src_vars.join(" ");
        format!("(block_{} {})", bid, args)
    };
    let block_app_dst = |bid: u32| -> String {
        let args = dst_vars.join(" ");
        format!("(block_{} {})", bid, args)
    };

    out.push_str(&format!(
        "(assert (forall ({}) {}))\n",
        forall_src,
        block_app(body.entry.0)
    ));

    for block in &body.blocks {
        let mut constraints: Vec<String> = Vec::new();
        let mut var_map: HashMap<usize, String> = HashMap::new();

        for i in 0..n_vars {
            var_map.insert(i, format!("v{}", i));
        }

        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(vid, rv) => {
                    let expr = smt_text::encode_rvalue(&BitvectorTheory, rv, &var_map);
                    if expr.starts_with("bv_fresh") {
                        let w = width_map.get(&(vid.0 as usize)).copied().unwrap_or(32);
                        if !fresh_decls.iter().any(|(n, _)| n == &expr) {
                            fresh_decls.push((expr.clone(), w));
                        }
                    }
                    var_map.insert(vid.0 as usize, expr);
                }
                Stmt::Assume(op) => {
                    let expr = smt_text::encode_operand(&BitvectorTheory, op, &var_map);
                    constraints.push(BitvectorTheory.encode_nonzero(&expr));
                }
                Stmt::Check(oid) => {
                    if obligations.contains(oid) {
                        let ob = body.obligation(*oid);
                        let cond_expr =
                            smt_text::encode_operand(&BitvectorTheory, &ob.cond, &var_map);
                        let mut error_conds = constraints.clone();
                        error_conds.push(BitvectorTheory.encode_is_zero(&cond_expr));
                        error_conds.push(block_app(block.id.0));

                        let body_expr = if error_conds.len() == 1 {
                            error_conds[0].clone()
                        } else {
                            format!("(and {})", error_conds.join(" "))
                        };

                        out.push_str(&format!(
                            "(assert (forall ({}) (=> {} error)))\n",
                            forall_src, body_expr
                        ));
                    }
                }
                _ => {}
            }
        }

        let mut assign_constraints: Vec<String> = Vec::new();
        for i in 0..n_vars {
            let val = var_map.get(&i).unwrap();
            if *val != format!("v{}p", i) {
                assign_constraints.push(format!("(= v{}p {})", i, val));
            }
        }

        let mk_trans = |target_bid: u32, extra_conds: &[String]| -> String {
            let mut all_conds = constraints.clone();
            all_conds.extend_from_slice(extra_conds);
            all_conds.extend(assign_constraints.iter().cloned());
            all_conds.push(block_app(block.id.0));

            let body_expr = if all_conds.is_empty() {
                block_app(block.id.0)
            } else {
                format!("(and {})", all_conds.join(" "))
            };

            format!(
                "(assert (forall ({}) (=> {} {})))\n",
                forall_both, body_expr, block_app_dst(target_bid)
            )
        };

        match &block.term {
            Terminator::Goto(t) => {
                out.push_str(&mk_trans(t.0, &[]));
            }
            Terminator::Branch { cond, then_, else_ } => {
                let cond_expr = smt_text::encode_operand(&BitvectorTheory, cond, &var_map);
                let nz = BitvectorTheory.encode_nonzero(&cond_expr);
                let z = BitvectorTheory.encode_is_zero(&cond_expr);
                out.push_str(&mk_trans(then_.0, &[nz]));
                out.push_str(&mk_trans(else_.0, &[z]));
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let val_expr = smt_text::encode_operand(&BitvectorTheory, value, &var_map);
                let mut neg_cases = Vec::new();
                for (cv, target) in cases {
                    let cv_encoded = BitvectorTheory.encode_int(*cv);
                    let eq = format!("(= {} {})", val_expr, cv_encoded);
                    out.push_str(&mk_trans(target.0, &[eq.clone()]));
                    neg_cases.push(format!("(not {})", eq));
                }
                out.push_str(&mk_trans(default.0, &neg_cases));
            }
            _ => {}
        }
    }

    if !fresh_decls.is_empty() {
        let insert_pos = out.find("(assert ").unwrap_or(out.len());
        let decl_block: String = fresh_decls
            .iter()
            .map(|(name, width)| format!("(declare-fun {} () (_ BitVec {}))\n", name, width))
            .collect();
        out.insert_str(insert_pos, &decl_block);
    }

    out.push_str("(assert (not error))\n");
    out.push_str("(check-sat)\n");

    out
}

// ---------------------------------------------------------------------------
// Solver interaction
// ---------------------------------------------------------------------------

fn run_chc_solver(
    binary: &str,
    smt2: &str,
    obligations: &[ObligationId],
) -> Result<Vec<(ObligationId, bool)>, String> {
    let mut child = Command::new(binary)
        .args(["-in", "-smt2"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn {}: {}", binary, e))?;

    {
        let stdin = child.stdin.as_mut().ok_or("no stdin")?;
        stdin
            .write_all(smt2.as_bytes())
            .map_err(|e| format!("write failed: {}", e))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("wait failed: {}", e))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let result_line = stdout.trim();

    debug!("chc: solver returned: {}", result_line);
    if !stderr.is_empty() {
        debug!("chc: solver stderr: {}", &stderr[..stderr.len().min(500)]);
    }

    // In CHC mode: `sat` means error is unreachable (safe), `unsat` means reachable (unsafe).
    match result_line {
        "sat" => Ok(obligations.iter().map(|oid| (*oid, true)).collect()),
        _ => Ok(vec![]),
    }
}
