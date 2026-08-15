//! SMT encoding: operands, rvalues, binary ops, and core IR-to-SMT translation.
//!
//! Specialized encodings live in sibling modules:
//! - `math_encode` — Math/Integer/Long/Short/Byte method calls
//! - `char_encode` — Character utility methods
//! - `str_encode` — toString / string-producing methods

use roast_core::smt::Term;
use roast_ir::*;

use super::ExploreCtx;

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
                        // IEEE 754 float comparison via bit-pattern totalOrder
                        if aw == 64 || bw == 64 {
                            // double comparison
                            let a_nan = self.fp_is_nan_64(at);
                            let b_nan = self.fp_is_nan_64(bt);
                            let either_nan = self.solver.or(a_nan, b_nan);
                            let nan_val = if *kind == CmpKind::FloatL {
                                self.solver.bv_const(-1, 32)
                            } else {
                                self.solver.bv_const(1, 32)
                            };
                            let cmp = self.fp_compare_bv64(at, bt);
                            self.solver.ite(either_nan, nan_val, cmp)
                        } else {
                            // float comparison
                            let a_nan = self.fp_is_nan_32(at);
                            let b_nan = self.fp_is_nan_32(bt);
                            let either_nan = self.solver.or(a_nan, b_nan);
                            let nan_val = if *kind == CmpKind::FloatL {
                                self.solver.bv_const(-1, 32)
                            } else {
                                self.solver.bv_const(1, 32)
                            };
                            let cmp = self.fp_compare_bv32(at, bt);
                            self.solver.ite(either_nan, nan_val, cmp)
                        }
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
            Rvalue::Call { .. } => self.solver.fresh_bv("havoc", 32),
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

    pub(super) fn encode_binop(&mut self, op: BinOp, a: &Operand, b: &Operand) -> Term {
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
