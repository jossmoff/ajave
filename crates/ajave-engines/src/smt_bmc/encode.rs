//! SMT encoding: operands, rvalues, binary ops, and core IR-to-SMT translation.
//!
//! Specialized encodings live in sibling modules:
//! - `math_encode` — Math/Integer/Long/Short/Byte method calls
//! - `char_encode` — Character utility methods
//! - `str_encode` — toString / string-producing methods

use ajave_core::smt::Term;
use ajave_ir::*;

use super::ExploreCtx;

/// Encode float/double **arithmetic** in the FloatingPoint theory, not just
/// comparisons.
///
/// Off, arithmetic runs on the bitvector path: faster, but a model satisfying
/// it need not satisfy the real float semantics, so witnesses fail JVM replay
/// and the point is lost. On, models are genuine float models and the witness
/// replays.
///
/// **Off by default. Measured on both properties, after getting it wrong once.**
///
/// With it off, float arithmetic runs on the bitvector path: a model satisfying
/// it need not satisfy real float semantics, so the branch condition is tainted,
/// `handle_branch` never imposes it, and the witness is arbitrary. Turning it on
/// fixes that — and makes proofs much harder.
///
/// float-nonlinear-calculation, 87 tasks, idle machine:
///
/// | property | FPA off | FPA on |
/// |---|---|---|
/// | valid-assert         | 18, 53s  | 35, 381s |
/// | no-runtime-exception | 166, 32s | 114, 381s |
///
/// Across the whole corpus that is roughly +7 on valid-assert and -69 on
/// no-runtime-exception: **net -62**.
///
/// The asymmetry is the point. FPA helps *falsification*, because a model over
/// real float semantics yields a witness that replays. It hurts *proving*,
/// because the formulas become hard enough that the solver returns `unknown`
/// instead of `unsat` — the losses are UNKNOWNs with **zero timeouts**, so this
/// is not the budget, it is discharges that no longer complete.
/// no-runtime-exception is overwhelmingly a proving problem (511 correct TRUE
/// against 16 correct FALSE corpus-wide), so it pays the cost and collects none
/// of the benefit.
///
/// This was enabled by default on a valid-assert-only measurement and had to be
/// reverted. A default justified on one property is not justified.
///
/// `AJAVE_FP_ARITH=1` enables it, and it is worth revisiting if the solver gets
/// better at FP (see #27, Bitwuzla) or if it can be scoped to falsification.
pub(super) fn fp_arith() -> bool {
    static CACHE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CACHE.get_or_init(|| {
        std::env::var("AJAVE_FP_ARITH").map(|v| v == "1").unwrap_or(false)
    })
}

impl<'a> ExploreCtx<'a> {
    pub(super) fn can_inline(&self, target: &MethodKey, is_virtual: bool) -> bool {
        if self.call_depth >= super::MAX_CALL_DEPTH {
            return false;
        }
        if is_virtual {
            let targets = self.prog.devirtualise(target);
            !targets.is_empty() && targets.iter().all(|t| self.prog.body(t).is_some())
        } else {
            self.prog.body(target).is_some()
        }
    }

    pub(super) fn encode_operand(&mut self, op: &Operand) -> Term {
        match op {
            Operand::Var(v) => self.get_var(*v),
            Operand::Const(Const::Int(n)) => self.solver.bv_const(*n as i64, 32),
            Operand::Const(Const::Long(n)) => self.solver.bv_const(*n, 64),
            Operand::Const(Const::Null) => self.solver.bv_const(0, 32),
            Operand::Const(Const::Str(_)) => self.solver.bv_const(1, 32),
            Operand::Const(Const::Float(f)) => self.solver.bv_const(f.to_bits() as i64, 32),
            Operand::Const(Const::Double(d)) => self.solver.bv_const(d.to_bits() as i64, 64),
            Operand::Const(_) => self.solver.bv_const(0, 32),
        }
    }

    pub(super) fn encode_str_operand(&mut self, op: &Operand) -> Option<Term> {
        match op {
            Operand::Var(v) => self.str_vars.get(v).copied(),
            Operand::Const(Const::Str(s)) => Some(self.solver.str_const(s)),
            _ => None,
        }
    }

    pub(super) fn encode_rvalue(&mut self, rv: &Rvalue) -> Term {
        match rv {
            Rvalue::Use(o) => self.encode_operand(o),
            Rvalue::Nondet(ty, jvm_byte) => {
                let w = self.width_of_ty(ty);
                let idx = self.nondet_terms.len();
                let t = self.solver.fresh_bv(&format!("nd_{idx}"), w);
                if *ty == Ty::Str {
                    self.assert_nonzero(t);
                }
                let range: Option<(i64, i64)> = match jvm_byte {
                    Some(b'Z') => Some((0, 1)),
                    Some(b'B') => Some((-128, 127)),
                    Some(b'S') => Some((-32768, 32767)),
                    Some(b'C') if self.ascii_only => Some((0, 127)),
                    Some(b'C') => Some((0, 0xFFFF)),
                    _ => None,
                };
                if let Some((lo, hi)) = range {
                    let lo_t = self.solver.bv_const(lo, w);
                    let hi_t = self.solver.bv_const(hi, w);
                    let ge = self.solver.bvsge(t, lo_t);
                    let le = self.solver.bvsle(t, hi_t);
                    let c = self.solver.and(ge, le);
                    self.solver.assert(c);
                }
                let str_term = if *ty == Ty::Str {
                    Some(self.solver.fresh_str(&format!("nds_{idx}")))
                } else {
                    None
                };
                if *ty != Ty::Ref {
                    self.nondet_terms.push((idx, t, w, *ty, str_term));
                }
                t
            }
            Rvalue::Havoc(ty) => {
                let w = self.width_of_ty(ty);
                self.solver.fresh_bv("hv", w)
            }
            Rvalue::Bin(op, a, b) => self.encode_binop(*op, a, b),
            Rvalue::Neg(o) => {
                let t = self.encode_operand(o);
                self.solver.bvneg(t)
            }
            Rvalue::Cast(ty, src, o) => {
                let t = self.encode_operand(o);
                match (src, ty) {
                    // Integer width changes
                    (Ty::Int, Ty::Long) => self.solver.sign_extend(t, 32),     // i2l
                    (Ty::Long, Ty::Int) => self.solver.extract(t, 31, 0),      // l2i
                    // Int → Float/Double
                    (Ty::Int, Ty::Float) => self.encode_i2f(t),                // i2f
                    (Ty::Int, Ty::Double) => self.encode_i2d(t),               // i2d
                    (Ty::Long, Ty::Float) => self.solver.fresh_bv("l2f", 32),  // l2f
                    (Ty::Long, Ty::Double) => self.encode_l2d(t),              // l2d
                    // Float/Double → Int
                    (Ty::Float, Ty::Int) => self.encode_f2i(t),                // f2i
                    (Ty::Float, Ty::Long) => self.encode_f2l(t),               // f2l
                    (Ty::Double, Ty::Int) => self.encode_d2i(t),               // d2i
                    (Ty::Double, Ty::Long) => self.encode_d2l(t),              // d2l
                    // Float ↔ Double
                    (Ty::Float, Ty::Double) => self.encode_f2d(t),             // f2d
                    (Ty::Double, Ty::Float) => self.solver.fresh_bv("d2f", 32),// d2f
                    _ => t,
                }
            }
            Rvalue::Cmp(kind, a, b) => {
                let at = self.encode_operand(a);
                let bt = self.encode_operand(b);
                let aw = self.width_of_operand(a);
                let bw = self.width_of_operand(b);
                match kind {
                    CmpKind::Long => {
                        let (at, bt) = if aw < bw {
                            (self.solver.sign_extend(at, bw - aw), bt)
                        } else if bw < aw {
                            (at, self.solver.sign_extend(bt, aw - bw))
                        } else {
                            (at, bt)
                        };
                        let lt = self.solver.bvslt(at, bt);
                        let eq = self.solver.bveq(at, bt);
                        let minus1 = self.solver.bv_const(-1, 32);
                        let zero = self.solver.bv_const(0, 32);
                        let one = self.solver.bv_const(1, 32);
                        let inner = self.solver.ite(eq, zero, one);
                        self.solver.ite(lt, minus1, inner)
                    }
                    CmpKind::FloatL | CmpKind::FloatG => {
                        // `dcmpl`/`dcmpg`/`fcmpl`/`fcmpg` (JVMS 6.5): push -1
                        // if a < b, 0 if a == b, 1 if a > b. When either
                        // operand is NaN the result is -1 for the `l` form and
                        // 1 for the `g` form — that asymmetry is the whole
                        // reason javac emits two instructions.
                        //
                        // Encoded in the FloatingPoint theory rather than over
                        // bit patterns: `fp.eq` gives IEEE equality, so -0.0
                        // compares equal to 0.0 and NaN compares unequal to
                        // everything, neither of which a bitwise comparison
                        // gets right.
                        let w = if aw == 64 || bw == 64 { 64 } else { 32 };
                        let af = self.encode_fp_operand(a, w);
                        let bf = self.encode_fp_operand(b, w);

                        let a_nan = self.solver.fp_is_nan(af);
                        let b_nan = self.solver.fp_is_nan(bf);
                        let either_nan = self.solver.or(a_nan, b_nan);

                        let lt = self.solver.fp_lt(af, bf);
                        let eq = self.solver.fp_eq(af, bf);

                        let minus1 = self.solver.bv_const(-1, 32);
                        let zero = self.solver.bv_const(0, 32);
                        let one = self.solver.bv_const(1, 32);

                        let nan_val = if *kind == CmpKind::FloatL { minus1 } else { one };
                        let ordered = {
                            let inner = self.solver.ite(eq, zero, one);
                            self.solver.ite(lt, minus1, inner)
                        };
                        self.solver.ite(either_nan, nan_val, ordered)
                    }
                }
            }
            Rvalue::GetStatic(fk) => {
                self.ensure_clinit(&fk.class);
                let k = Self::field_key_raw(fk);
                if let Some(&t) = self.statics.get(&k) {
                    t
                } else if self.is_program_class(&fk.class) {
                    let w = Self::field_elem_width(&fk.desc);
                    let t = self.solver.bv_const(0, w);
                    self.statics.insert(k, t);
                    t
                } else {
                    let w = Self::field_elem_width(&fk.desc);
                    let t = self.solver.fresh_bv("static", w);
                    if fk.desc.starts_with('L') || fk.desc.starts_with('[') {
                        let zero = self.solver.bv_const(0, 32);
                        let eq = self.solver.bveq(t, zero);
                        let neq = self.solver.not(eq);
                        self.solver.assert(neq);
                    }
                    self.statics.insert(k, t);
                    t
                }
            }
            Rvalue::GetField { field, obj, .. } => {
                let obj_term = self.encode_operand(obj);
                let k = self.field_key_resolved(field);
                let w = Self::field_elem_width(&field.desc);
                let arr = self.get_field_array(&k, w);
                self.solver.array_select(arr, obj_term)
            }
            Rvalue::New(class) => {
                let id = self.next_alloc_id;
                self.next_alloc_id += 1;
                let ref_term = self.solver.bv_const(id, 32);
                let type_id = self.get_type_id(class);
                let type_id_term = self.solver.bv_const(type_id, 32);
                let new_ta = self.solver.array_store(self.type_array, ref_term, type_id_term);
                self.type_array = new_ta;
                ref_term
            }
            Rvalue::NewArray { len, .. } => {
                let id = self.next_alloc_id;
                self.next_alloc_id += 1;
                let ref_term = self.solver.bv_const(id, 32);
                let len_term = self.encode_operand(len);
                let zero = self.solver.bv_const(0, 32);
                let arr_term = self.solver.const_array(zero, 32);
                self.array_map.push((ref_term, arr_term, len_term));
                ref_term
            }
            Rvalue::ArrayLength(arr_op) => {
                let ref_term = self.encode_operand(arr_op);
                self.array_length_lookup(ref_term)
            }
            Rvalue::ArrayLoad { arr, idx } => {
                let ref_term = self.encode_operand(arr);
                let idx_term = self.encode_operand(idx);
                self.array_select_lookup(ref_term, idx_term)
            }
            Rvalue::InstanceOf { obj, class } => {
                let obj_term = self.encode_operand(obj);
                let zero = self.solver.bv_const(0, 32);
                let one = self.solver.bv_const(1, 32);
                let null_check = self.solver.bveq(obj_term, zero);
                let not_null = self.solver.not(null_check);
                if class == "java/lang/Object" {
                    return self.solver.ite(not_null, one, zero);
                }
                if matches!(obj, Operand::Const(Const::Str(_))) {
                    let is_str = self.prog.is_subtype("java/lang/String", class);
                    return if is_str { one } else { zero };
                }
                let obj_type = self.solver.array_select(self.type_array, obj_term);
                let subtypes = self.subtype_ids(class);
                let ff = self.solver.bool_const(false);
                let mut is_instance = ff;
                for sid in subtypes {
                    let st = self.solver.bv_const(sid, 32);
                    let eq = self.solver.bveq(obj_type, st);
                    is_instance = self.solver.or(is_instance, eq);
                }
                let result_bool = self.solver.and(not_null, is_instance);
                self.solver.ite(result_bool, one, zero)
            }
            Rvalue::Call { target, .. } => {
                let w = Self::ret_width_from_desc(&target.desc);
                self.solver.fresh_bv("havoc", w)
            }
        }
    }

    // ── Array helpers ───────────────────────────────────────────────────

    pub(super) fn array_contents_lookup(&mut self, ref_term: Term) -> Term {
        let pairs: Vec<(Term, Term, Term)> = self.array_map.clone();
        let mut result = self.solver.fresh_array("arr_default", 32);
        for (r, arr, _len) in &pairs {
            let eq = self.solver.bveq(ref_term, *r);
            result = self.solver.ite(eq, *arr, result);
        }
        result
    }

    pub(super) fn array_length_lookup(&mut self, ref_term: Term) -> Term {
        let pairs: Vec<(Term, Term, Term)> = self.array_map.clone();
        let mut result = self.solver.fresh_bv("len_default", 32);
        for (r, _arr, len) in &pairs {
            let eq = self.solver.bveq(ref_term, *r);
            result = self.solver.ite(eq, *len, result);
        }
        result
    }

    pub(super) fn array_select_lookup(&mut self, ref_term: Term, idx_term: Term) -> Term {
        let arr = self.array_contents_lookup(ref_term);
        self.solver.array_select(arr, idx_term)
    }

    pub(super) fn array_store_update(&mut self, ref_term: Term, idx_term: Term, val_term: Term) {
        let arr = self.array_contents_lookup(ref_term);
        let new_arr = self.solver.array_store(arr, idx_term, val_term);
        let len = self.array_length_lookup(ref_term);
        self.array_map.push((ref_term, new_arr, len));
    }

    // ── Binary operations ───────────────────────────────────────────────

    /// The FP width of an operand, when it is a float or double.
    ///
    /// Uses the declared type rather than the tracked bitvector width, since
    /// the latter cannot distinguish a double from a long.
    pub(super) fn fp_width_of_operand(&self, op: &Operand) -> Option<u32> {
        match op {
            Operand::Var(v) => match self.body.var(*v).ty {
                Ty::Float => Some(32),
                Ty::Double => Some(64),
                _ => None,
            },
            Operand::Const(Const::Float(_)) => Some(32),
            Operand::Const(Const::Double(_)) => Some(64),
            _ => None,
        }
    }

    /// An operand as a FloatingPoint-sorted term.
    ///
    /// Float variables carry their FP term in `fp_vars`; anything else is
    /// reinterpreted from its bit pattern, which is exactly
    /// `Double.longBitsToDouble` and so loses nothing.
    pub(super) fn encode_fp_operand(&mut self, op: &Operand, width: u32) -> Term {
        match op {
            Operand::Var(v) => {
                if let Some(&t) = self.fp_vars.get(v) {
                    return t;
                }
                let bv = self.encode_operand(op);
                let t = self.solver.fp_from_bits(bv, width);
                self.fp_vars.insert(*v, t);
                t
            }
            Operand::Const(Const::Float(f)) => self.solver.fp_const(*f as f64, 32),
            Operand::Const(Const::Double(d)) => self.solver.fp_const(*d, 64),
            _ => {
                let bv = self.encode_operand(op);
                self.solver.fp_from_bits(bv, width)
            }
        }
    }

    /// Encode `a op b` in the FloatingPoint theory.
    ///
    /// Arithmetic returns an FP term (the caller stores it in `fp_vars`);
    /// comparisons return the 0/1 integer the JVM's branch encoding expects.
    /// `fp.eq` gives IEEE equality, so NaN compares unequal to everything
    /// including itself, and -0.0 equals 0.0 — both of which a bitvector
    /// comparison on the raw pattern gets wrong.
    pub(super) fn encode_fp_binop(
        &mut self, op: BinOp, a: &Operand, b: &Operand, width: u32,
    ) -> Option<Term> {
        let at = self.encode_fp_operand(a, width);
        let bt = self.encode_fp_operand(b, width);
        let bool_to_int = |s: &mut Self, cmp: Term| {
            let one = s.solver.bv_const(1, 32);
            let zero = s.solver.bv_const(0, 32);
            s.solver.ite(cmp, one, zero)
        };
        // Arithmetic yields an FP term. Every other part of the encoder
        // expects bitvectors, so hand back the bit pattern and stash the FP
        // term in `pending_fp` for the assignment site to attach to the
        // destination variable — keeping full precision for later float
        // operations instead of round-tripping through unconstrained bits.
        let mut arith = |s: &mut Self, r: Term| {
            s.pending_fp = Some(r);
            s.solver.fp_to_bits(r, width)
        };
        Some(match op {
            BinOp::Add => { let r = self.solver.fp_add(at, bt); arith(self, r) }
            BinOp::Sub => { let r = self.solver.fp_sub(at, bt); arith(self, r) }
            BinOp::Mul => { let r = self.solver.fp_mul(at, bt); arith(self, r) }
            BinOp::Div => { let r = self.solver.fp_div(at, bt); arith(self, r) }
            BinOp::Rem => { let r = self.solver.fp_rem(at, bt); arith(self, r) }
            BinOp::Eq => { let c = self.solver.fp_eq(at, bt); bool_to_int(self, c) }
            BinOp::Ne => {
                let c = self.solver.fp_eq(at, bt);
                let n = self.solver.not(c);
                bool_to_int(self, n)
            }
            BinOp::Lt => { let c = self.solver.fp_lt(at, bt); bool_to_int(self, c) }
            BinOp::Le => { let c = self.solver.fp_le(at, bt); bool_to_int(self, c) }
            BinOp::Gt => { let c = self.solver.fp_gt(at, bt); bool_to_int(self, c) }
            BinOp::Ge => { let c = self.solver.fp_ge(at, bt); bool_to_int(self, c) }
            // Bitwise and shift operators do not apply to floats in Java.
            _ => return None,
        })
    }

    pub(super) fn encode_binop(&mut self, op: BinOp, a: &Operand, b: &Operand) -> Term {
        // Route float/double *comparisons* through the FloatingPoint theory.
        //
        // Arithmetic is deliberately left on the bitvector path. Encoding it in
        // FPA is more faithful, but measured ~2.5x slower end-to-end, and the
        // extra time pushed transcendental benchmarks past the timeout — losing
        // more than the precision gained. Comparisons are where the bitvector
        // encoding is actually *wrong* (NaN compares equal to itself, -0.0
        // differs from 0.0) and they cost almost nothing to encode, so that is
        // where the theory earns its keep. Arithmetic remains float-tainted,
        // which keeps it from being claimed as precise.
        // Arithmetic goes through FPA when `fp_arith()` is on.
        //
        // With it off, `1.5 - d1 * (1.0 - d2)` is computed with *integer*
        // operations on raw bit patterns, so a satisfying model is not a
        // satisfying float model. BMC still publishes the violation and lets
        // JVM replay arbitrate — which is sound, but for
        // float-nonlinear-calculation the bitvector model is essentially never
        // a real one, so 18 of 25 sampled tasks found the violation and then
        // withdrew it. Those are points computed correctly and discarded.
        let fp_op = if fp_arith() {
            matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt
                     | BinOp::Ge | BinOp::Add | BinOp::Sub | BinOp::Mul
                     | BinOp::Div | BinOp::Rem)
        } else {
            matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
        };
        if fp_op {
            if let (Some(wa), Some(wb)) =
                (self.fp_width_of_operand(a), self.fp_width_of_operand(b))
            {
                let w = wa.max(wb);
                if let Some(t) = self.encode_fp_binop(op, a, b, w) {
                    return t;
                }
            }
        }
        let at = self.encode_operand(a);
        let bt = self.encode_operand(b);
        let aw = self.width_of_operand(a);
        let bw = self.width_of_operand(b);
        let (at, bt) = if !matches!(op, BinOp::Shl | BinOp::Shr | BinOp::UShr) && aw != bw {
            if aw < bw {
                (self.solver.sign_extend(at, bw - aw), bt)
            } else {
                (at, self.solver.sign_extend(bt, aw - bw))
            }
        } else {
            (at, bt)
        };
        match op {
            BinOp::Add => self.solver.bvadd(at, bt),
            BinOp::Sub => self.solver.bvsub(at, bt),
            BinOp::Mul => self.solver.bvmul(at, bt),
            BinOp::Div => self.solver.bvsdiv(at, bt),
            BinOp::Rem => self.solver.bvsrem(at, bt),
            BinOp::And => self.solver.bvand(at, bt),
            BinOp::Or => self.solver.bvor(at, bt),
            BinOp::Xor => self.solver.bvxor(at, bt),
            BinOp::Shl | BinOp::Shr | BinOp::UShr => {
                let aw = self.width_of_operand(a);
                let mask = if aw == 64 { 0x3F } else { 0x1F };
                let mask_t = self.solver.bv_const(mask, 32);
                let bt = self.solver.bvand(bt, mask_t);
                let bt = if aw == 64 {
                    self.solver.zero_extend(bt, 32)
                } else {
                    bt
                };
                match op {
                    BinOp::Shl => self.solver.bvshl(at, bt),
                    BinOp::Shr => self.solver.bvashr(at, bt),
                    BinOp::UShr => self.solver.bvlshr(at, bt),
                    _ => unreachable!(),
                }
            }
            BinOp::Eq => {
                let cmp = self.solver.bveq(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Ne => {
                let cmp = self.solver.bveq(at, bt);
                let ncmp = self.solver.not(cmp);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(ncmp, one, zero)
            }
            BinOp::Lt => {
                let cmp = self.solver.bvslt(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Le => {
                let cmp = self.solver.bvsle(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Gt => {
                let cmp = self.solver.bvsgt(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
            BinOp::Ge => {
                let cmp = self.solver.bvsge(at, bt);
                let one = self.solver.bv_const(1, 32);
                let zero = self.solver.bv_const(0, 32);
                self.solver.ite(cmp, one, zero)
            }
        }
    }
}
