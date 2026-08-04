//! SMT encoding: operands, rvalues, binary ops, string calls, math calls.

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

    pub(super) fn str_call_modelled(&self, target: &MethodKey, args: &[Operand]) -> bool {
        let has_recv_str = args.first().map_or(false, |a| match a {
            Operand::Var(v) => self.str_vars.contains_key(v),
            Operand::Const(Const::Str(_)) => true,
            _ => false,
        });
        let has_arg1_str = args.get(1).map_or(false, |a| match a {
            Operand::Var(v) => self.str_vars.contains_key(v),
            Operand::Const(Const::Str(_)) => true,
            _ => false,
        });
        match target.name.as_str() {
            "length" | "isEmpty" | "toString" => has_recv_str,
            "contains" | "equals" | "startsWith" | "endsWith" | "concat" => {
                has_recv_str && has_arg1_str
            }
            "charAt" | "substring" => has_recv_str,
            "indexOf" => has_recv_str && has_arg1_str,
            "valueOf" => true,
            _ => false,
        }
    }

    pub(super) fn math_call_modelled(&self, target: &MethodKey) -> bool {
        match target.class.as_str() {
            "java/lang/Math" | "java/lang/StrictMath" => matches!(
                target.name.as_str(),
                "abs" | "min" | "max" | "addExact" | "subtractExact"
                    | "multiplyExact" | "negateExact" | "floorDiv" | "floorMod"
            ),
            "java/lang/Integer" => matches!(
                target.name.as_str(),
                "parseInt" | "max" | "min" | "sum"
                    | "reverse" | "reverseBytes" | "numberOfLeadingZeros"
                    | "numberOfTrailingZeros" | "bitCount" | "highestOneBit"
                    | "lowestOneBit" | "signum" | "toUnsignedLong"
                    | "divideUnsigned" | "remainderUnsigned" | "compareUnsigned"
            ),
            "java/lang/Long" => matches!(
                target.name.as_str(),
                "parseLong" | "max" | "min" | "sum" | "signum"
                    | "divideUnsigned" | "remainderUnsigned" | "compareUnsigned"
            ),
            _ => false,
        }
    }

    pub(super) fn encode_math_call(&mut self, target: &MethodKey, args: &[Operand]) -> Term {
        let class = target.class.as_str();
        let name = target.name.as_str();
        match (class, name) {
            ("java/lang/Math" | "java/lang/StrictMath", "abs") => {
                let a = self.encode_operand(&args[0]);
                let w = self.width_of_operand(&args[0]);
                let zero = self.solver.bv_const(0, w);
                let neg = self.solver.bvneg(a);
                let is_neg = self.solver.bvslt(a, zero);
                self.solver.ite(is_neg, neg, a)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "min")
            | ("java/lang/Integer" | "java/lang/Long", "min") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let lt = self.solver.bvslt(a, b);
                self.solver.ite(lt, a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "max")
            | ("java/lang/Integer" | "java/lang/Long", "max") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                let gt = self.solver.bvsgt(a, b);
                self.solver.ite(gt, a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "addExact")
            | ("java/lang/Integer" | "java/lang/Long", "sum") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvadd(a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "subtractExact") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsub(a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "multiplyExact") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvmul(a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "negateExact") => {
                let a = self.encode_operand(&args[0]);
                self.solver.bvneg(a)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "floorDiv") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsdiv(a, b)
            }
            ("java/lang/Math" | "java/lang/StrictMath", "floorMod") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsrem(a, b)
            }
            ("java/lang/Integer" | "java/lang/Long", "signum") => {
                let a = self.encode_operand(&args[0]);
                let w = self.width_of_operand(&args[0]);
                let zero = self.solver.bv_const(0, w);
                let one = self.solver.bv_const(1, 32);
                let mone = self.solver.bv_const(-1, 32);
                let zero32 = self.solver.bv_const(0, 32);
                let is_neg = self.solver.bvslt(a, zero);
                let is_zero = self.solver.bveq(a, zero);
                let inner = self.solver.ite(is_zero, zero32, one);
                self.solver.ite(is_neg, mone, inner)
            }
            ("java/lang/Integer", "toUnsignedLong") => {
                let a = self.encode_operand(&args[0]);
                self.solver.zero_extend(a, 32)
            }
            ("java/lang/Integer" | "java/lang/Long", "divideUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsdiv(a, b)
            }
            ("java/lang/Integer" | "java/lang/Long", "remainderUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsrem(a, b)
            }
            ("java/lang/Integer" | "java/lang/Long", "compareUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsub(a, b)
            }
            ("java/lang/Integer", "parseInt") | ("java/lang/Long", "parseLong") => {
                let w = if class == "java/lang/Long" { 64 } else { 32 };
                self.solver.fresh_bv("parse", w)
            }
            _ => {
                self.solver.fresh_bv("math_hv", 32)
            }
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

    pub(super) fn encode_str_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
    ) -> Option<(Term, Option<Term>)> {
        let recv_str = args.first().and_then(|a| self.encode_str_operand(a));
        let one = self.solver.bv_const(1, 32);
        let zero = self.solver.bv_const(0, 32);

        match target.name.as_str() {
            "length" => {
                let s = recv_str?;
                let len_int = self.solver.str_len(s);
                let len_bv = self.solver.int_to_bv32(len_int);
                Some((len_bv, None))
            }
            "isEmpty" => {
                let s = recv_str?;
                let len_int = self.solver.str_len(s);
                let zero_int = self.solver.int_const(0);
                let eq = self.solver.bveq(len_int, zero_int);
                let r = self.solver.ite(eq, one, zero);
                Some((r, None))
            }
            "contains" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_contains(s, t);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "equals" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_eq(s, t);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "startsWith" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_prefixof(t, s);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "endsWith" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let b = self.solver.str_suffixof(t, s);
                let r = self.solver.ite(b, one, zero);
                Some((r, None))
            }
            "charAt" => {
                let s = recv_str?;
                let idx_bv = self.encode_operand(args.get(1)?);
                let idx_int = self.solver.bv32_to_int(idx_bv);
                let ch_str = self.solver.str_at(s, idx_int);
                let ch_int = self.solver.str_to_int(ch_str);
                let ch_bv = self.solver.int_to_bv32(ch_int);
                Some((ch_bv, None))
            }
            "indexOf" => {
                let s = recv_str?;
                let arg1 = args.get(1)?;
                let needle = self.encode_str_operand(arg1)?;
                let start = self.solver.int_const(0);
                let idx_int = self.solver.str_indexof(s, needle, start);
                let idx_bv = self.solver.int_to_bv32(idx_int);
                Some((idx_bv, None))
            }
            "substring" => {
                let s = recv_str?;
                let start_bv = self.encode_operand(args.get(1)?);
                let start_int = self.solver.bv32_to_int(start_bv);
                let len_int = if let Some(end_op) = args.get(2) {
                    let end_bv = self.encode_operand(end_op);
                    let diff_bv = self.solver.bvsub(end_bv, start_bv);
                    self.solver.bv32_to_int(diff_bv)
                } else {
                    let total = self.solver.str_len(s);
                    let total_bv = self.solver.int_to_bv32(total);
                    let diff = self.solver.bvsub(total_bv, start_bv);
                    self.solver.bv32_to_int(diff)
                };
                let result = self.solver.str_substr(s, start_int, len_int);
                Some((one, Some(result)))
            }
            "concat" => {
                let s = recv_str?;
                let t = args.get(1).and_then(|a| self.encode_str_operand(a))?;
                let result = self.solver.str_concat(s, t);
                Some((one, Some(result)))
            }
            "toString" => {
                let s = recv_str?;
                Some((one, Some(s)))
            }
            "valueOf" => {
                let arg_bv = self.encode_operand(args.first()?);
                let arg_int = self.solver.bv32_to_int(arg_bv);
                let result = self.solver.str_from_int(arg_int);
                Some((one, Some(result)))
            }
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
                    Some(b'C') => Some((0, 65535)),
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
            Rvalue::Cast(ty, o) => {
                let t = self.encode_operand(o);
                match ty {
                    Ty::Long => self.solver.sign_extend(t, 32),
                    Ty::Int => self.solver.extract(t, 31, 0),
                    _ => t,
                }
            }
            Rvalue::Cmp(a, b) => {
                let at = self.encode_operand(a);
                let bt = self.encode_operand(b);
                let aw = self.width_of_operand(a);
                let bw = self.width_of_operand(b);
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
            Rvalue::GetStatic(fk) => {
                self.ensure_clinit(&fk.class);
                let k = Self::field_key(fk);
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
                let k = Self::field_key(field);
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
                let arr_term = self.solver.fresh_array("arr", 32);
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
                let null_check = self.solver.bveq(obj_term, zero);
                let obj_type = self.solver.array_select(self.type_array, obj_term);
                let subtypes = self.subtype_ids(class);
                let ff = self.solver.bool_const(false);
                let mut is_instance = ff;
                for sid in subtypes {
                    let st = self.solver.bv_const(sid, 32);
                    let eq = self.solver.bveq(obj_type, st);
                    is_instance = self.solver.or(is_instance, eq);
                }
                let not_null = self.solver.not(null_check);
                let result_bool = self.solver.and(not_null, is_instance);
                let one = self.solver.bv_const(1, 32);
                self.solver.ite(result_bool, one, zero)
            }
            Rvalue::Call { .. } => self.solver.fresh_bv("havoc", 32),
        }
    }

    pub(super) fn array_contents_lookup(&mut self, ref_term: Term) -> Term {
        let pairs: Vec<(Term, Term, Term)> = self.array_map.clone();
        let mut result = self.solver.fresh_array("arr_default", 32);
        for (r, arr, _len) in pairs.iter().rev() {
            let eq = self.solver.bveq(ref_term, *r);
            result = self.solver.ite(eq, *arr, result);
        }
        result
    }

    pub(super) fn array_length_lookup(&mut self, ref_term: Term) -> Term {
        let pairs: Vec<(Term, Term, Term)> = self.array_map.clone();
        let mut result = self.solver.fresh_bv("len_default", 32);
        for (r, _arr, len) in pairs.iter().rev() {
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
