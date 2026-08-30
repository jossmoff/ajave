//! SMT-LIB2 process-based solver backend.
//!
//! Spawns a solver binary (z3, bitwuzla, cvc5) and communicates via stdin/stdout
//! using the SMT-LIB2 text protocol. Zero C++ build dependencies; solver-agnostic
//! at runtime.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use log::{debug, trace};

use crate::smt::{SatResult, Solver, SolverFactory, Sort, Term};

pub struct SmtLib {
    child: Child,
    stdin: BufWriter<ChildStdin>,
    stdout: BufReader<ChildStdout>,
    next_id: u64,
    term_names: HashMap<u64, String>,
    term_sorts: HashMap<u64, Sort>,
    /// Cache for bv_const: (value, width) -> Term to avoid creating duplicates.
    bv_const_cache: HashMap<(i64, u32), Term>,
    /// Cache for bool constants.
    bool_true: Option<Term>,
    bool_false: Option<Term>,
}

impl SmtLib {
    /// Send a command without flushing. Commands are batched in the BufWriter
    /// and only flushed before operations that read a response.
    fn send(&mut self, cmd: &str) {
        trace!("smt>> {cmd}");
        let _ = writeln!(self.stdin, "{cmd}");
    }

    /// Flush buffered commands and read a response line from the solver.
    fn read_line(&mut self) -> String {
        let _ = self.stdin.flush();
        let mut line = String::new();
        let _ = self.stdout.read_line(&mut line);
        let result = line.trim().to_string();
        trace!("smt<< {result}");
        result
    }

    fn alloc(&mut self, name: String, sort: Sort) -> Term {
        let id = self.next_id;
        self.next_id += 1;
        self.term_names.insert(id, name);
        self.term_sorts.insert(id, sort);
        Term(id)
    }

    fn name(&self, t: Term) -> &str {
        self.term_names
            .get(&t.0)
            .map(|s| s.as_str())
            .unwrap_or("??")
    }

    fn sort(&self, t: Term) -> Sort {
        self.term_sorts.get(&t.0).copied().unwrap_or(Sort::Bv(32))
    }

    fn sort_str(s: Sort) -> &'static str {
        match s {
            Sort::Bool => "Bool",
            Sort::Bv(32) => "(_ BitVec 32)",
            Sort::Bv(64) => "(_ BitVec 64)",
            Sort::Str => "String",
            Sort::Int => "Int",
            Sort::Array { idx: 32, elem: 32 } => "(Array (_ BitVec 32) (_ BitVec 32))",
            Sort::Array { idx: 32, elem: 64 } => "(Array (_ BitVec 32) (_ BitVec 64))",
            Sort::StrArray => "(Array (_ BitVec 32) String)",
            Sort::Fp(32) => "Float32",
            Sort::Fp(64) => "Float64",
            _ => "", // fallback handled below
        }
    }

    fn sort_str_dynamic(s: Sort) -> String {
        let cached = Self::sort_str(s);
        if !cached.is_empty() {
            return cached.to_string();
        }
        match s {
            Sort::Bv(w) => format!("(_ BitVec {w})"),
            Sort::Fp(w) => format!("(_ FloatingPoint {} {})",
                                   if w == 32 { 8 } else { 11 },
                                   if w == 32 { 24 } else { 53 }),
            Sort::Array { idx, elem } => {
                format!("(Array (_ BitVec {idx}) (_ BitVec {elem}))")
            }
            _ => unreachable!(),
        }
    }

    fn define_term(&mut self, prefix: &str, expr: &str, sort: Sort) -> Term {
        let id = self.next_id;
        let name = format!("{prefix}_{id}");
        let cached = Self::sort_str(sort);
        if !cached.is_empty() {
            self.send(&format!("(define-const {name} {cached} {expr})"));
        } else {
            let sort_s = Self::sort_str_dynamic(sort);
            self.send(&format!("(define-const {name} {sort_s} {expr})"));
        }
        self.alloc(name, sort)
    }


    /// FP arithmetic carrying the round-nearest-even mode Java mandates.
    fn fp_binop_rne(&mut self, op: &str, a: Term, b: Term) -> Term {
        let sort = self.sort(a);
        let id = self.next_id;
        let name = format!("t_{id}");
        let an = self.name(a);
        let bn = self.name(b);
        let sort_s = Self::sort_str_dynamic(sort);
        self.send(&format!(
            "(define-const {name} {sort_s} ({op} RNE {an} {bn}))"
        ));
        self.alloc(name, sort)
    }

    fn unop_same_sort(&mut self, op: &str, a: Term) -> Term {
        let sort = self.sort(a);
        let id = self.next_id;
        let name = format!("t_{id}");
        let an = self.name(a);
        let sort_s = Self::sort_str_dynamic(sort);
        self.send(&format!("(define-const {name} {sort_s} ({op} {an}))"));
        self.alloc(name, sort)
    }

    fn unop_bool(&mut self, op: &str, a: Term) -> Term {
        let id = self.next_id;
        let name = format!("t_{id}");
        let an = self.name(a);
        self.send(&format!("(define-const {name} Bool ({op} {an}))"));
        self.alloc(name, Sort::Bool)
    }

    /// Apply an indexed conversion operator, optionally with a rounding mode.
    fn convert(&mut self, op: &str, a: Term, to: Sort, rounded: bool) -> Term {
        let id = self.next_id;
        let name = format!("t_{id}");
        let an = self.name(a);
        let sort_s = Self::sort_str_dynamic(to);
        let inner = if rounded {
            format!("({op} RNE {an})")
        } else {
            format!("({op} {an})")
        };
        self.send(&format!("(define-const {name} {sort_s} {inner})"));
        self.alloc(name, to)
    }

    fn binop(&mut self, op: &str, a: Term, b: Term) -> Term {
        let sort = self.sort(a);
        // Build inline: (define-const t_N <sort> (<op> <a> <b>))
        let id = self.next_id;
        let name = format!("t_{id}");
        let an = self.name(a);
        let bn = self.name(b);
        let cached = Self::sort_str(sort);
        if !cached.is_empty() {
            self.send(&format!("(define-const {name} {cached} ({op} {an} {bn}))"));
        } else {
            let sort_s = Self::sort_str_dynamic(sort);
            self.send(&format!("(define-const {name} {sort_s} ({op} {an} {bn}))"));
        }
        self.alloc(name, sort)
    }

    fn binop_bool(&mut self, op: &str, a: Term, b: Term) -> Term {
        let id = self.next_id;
        let name = format!("t_{id}");
        let an = self.name(a);
        let bn = self.name(b);
        self.send(&format!("(define-const {name} Bool ({op} {an} {bn}))"));
        self.alloc(name, Sort::Bool)
    }
}

impl Solver for SmtLib {
    fn name(&self) -> &'static str {
        "smtlib"
    }

    fn fresh_bv(&mut self, name: &str, width: u32) -> Term {
        let sort = Sort::Bv(width);
        let sname = format!("{name}_{}", self.next_id);
        let cached = Self::sort_str(sort);
        if !cached.is_empty() {
            self.send(&format!("(declare-const {sname} {cached})"));
        } else {
            let sort_s = Self::sort_str_dynamic(sort);
            self.send(&format!("(declare-const {sname} {sort_s})"));
        }
        self.alloc(sname, sort)
    }

    fn bv_const(&mut self, value: i64, width: u32) -> Term {
        if let Some(&t) = self.bv_const_cache.get(&(value, width)) {
            return t;
        }
        let sort = Sort::Bv(width);
        // Convert to unsigned representation for SMT-LIB2 bitvector literal.
        let uval = match width {
            32 => (value as i32 as u32) as u64,
            64 => value as u64,
            _ => (value as u64) & ((1u64 << width) - 1),
        };
        let name = if width % 4 == 0 {
            // Hex literal: exact number of hex digits
            let hex_digits = (width as usize) / 4;
            format!("#x{uval:0>hex_digits$x}")
        } else {
            // Binary literal for non-nibble-aligned widths
            let bin_digits = width as usize;
            format!("#b{uval:0>bin_digits$b}")
        };
        let t = self.alloc(name, sort);
        self.bv_const_cache.insert((value, width), t);
        t
    }

    fn bool_const(&mut self, value: bool) -> Term {
        if value {
            if let Some(t) = self.bool_true {
                return t;
            }
            let t = self.alloc("true".to_string(), Sort::Bool);
            self.bool_true = Some(t);
            t
        } else {
            if let Some(t) = self.bool_false {
                return t;
            }
            let t = self.alloc("false".to_string(), Sort::Bool);
            self.bool_false = Some(t);
            t
        }
    }

    fn bvadd(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvadd", a, b)
    }
    fn bvsub(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvsub", a, b)
    }
    fn bvmul(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvmul", a, b)
    }
    fn bvsdiv(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvsdiv", a, b)
    }
    fn bvsrem(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvsrem", a, b)
    }
    fn bvudiv(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvudiv", a, b)
    }
    fn bvurem(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvurem", a, b)
    }
    fn bvneg(&mut self, a: Term) -> Term {
        let an = self.name(a).to_string();
        let sort = self.sort(a);
        let expr = format!("(bvneg {an})");
        self.define_term("t", &expr, sort)
    }

    fn bvand(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvand", a, b)
    }
    fn bvor(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvor", a, b)
    }
    fn bvxor(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvxor", a, b)
    }
    fn bvshl(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvshl", a, b)
    }
    fn bvashr(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvashr", a, b)
    }
    fn bvlshr(&mut self, a: Term, b: Term) -> Term {
        self.binop("bvlshr", a, b)
    }

    fn bveq(&mut self, a: Term, b: Term) -> Term {
        // SMT-LIB2 uses `=` for equality, which returns Bool
        self.binop_bool("=", a, b)
    }
    fn bvslt(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("bvslt", a, b)
    }
    fn bvsle(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("bvsle", a, b)
    }
    fn bvsgt(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("bvsgt", a, b)
    }
    fn bvsge(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("bvsge", a, b)
    }

    fn bvult(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("bvult", a, b)
    }

    fn sign_extend(&mut self, t: Term, extra_bits: u32) -> Term {
        let tn = self.name(t).to_string();
        let sort = match self.sort(t) {
            Sort::Bv(w) => Sort::Bv(w + extra_bits),
            s => s,
        };
        let expr = format!("((_ sign_extend {extra_bits}) {tn})");
        self.define_term("t", &expr, sort)
    }

    fn zero_extend(&mut self, t: Term, extra_bits: u32) -> Term {
        let tn = self.name(t).to_string();
        let sort = match self.sort(t) {
            Sort::Bv(w) => Sort::Bv(w + extra_bits),
            s => s,
        };
        let expr = format!("((_ zero_extend {extra_bits}) {tn})");
        self.define_term("t", &expr, sort)
    }

    fn extract(&mut self, t: Term, hi: u32, lo: u32) -> Term {
        let tn = self.name(t).to_string();
        let width = hi - lo + 1;
        let expr = format!("((_ extract {hi} {lo}) {tn})");
        self.define_term("t", &expr, Sort::Bv(width))
    }

    fn concat(&mut self, hi: Term, lo: Term) -> Term {
        let hn = self.name(hi).to_string();
        let ln = self.name(lo).to_string();
        let hi_w = match self.sort(hi) { Sort::Bv(w) => w, _ => 32 };
        let lo_w = match self.sort(lo) { Sort::Bv(w) => w, _ => 32 };
        let expr = format!("(concat {hn} {ln})");
        self.define_term("t", &expr, Sort::Bv(hi_w + lo_w))
    }


    // ── IEEE-754 floating point ─────────────────────────────────────────

    fn fresh_fp(&mut self, name: &str, width: u32) -> Term {
        let sort = Sort::Fp(width);
        let sname = format!("{name}_{}", self.next_id);
        let sort_s = Self::sort_str_dynamic(sort);
        self.send(&format!("(declare-const {sname} {sort_s})"));
        self.alloc(sname, sort)
    }

    fn fp_const(&mut self, value: f64, width: u32) -> Term {
        let sort = Sort::Fp(width);
        // Emit the exact bit pattern rather than a decimal literal: decimal
        // text would be re-rounded by the solver and need not denote the same
        // float the JVM had.
        let name = if value.is_nan() {
            format!("(_ NaN {} {})", if width == 32 { 8 } else { 11 },
                    if width == 32 { 24 } else { 53 })
        } else if value.is_infinite() {
            let kind = if value > 0.0 { "+oo" } else { "-oo" };
            format!("(_ {kind} {} {})", if width == 32 { 8 } else { 11 },
                    if width == 32 { 24 } else { 53 })
        } else if width == 32 {
            let bits = (value as f32).to_bits();
            format!("((_ to_fp 8 24) #x{bits:08x})")
        } else {
            let bits = value.to_bits();
            format!("((_ to_fp 11 53) #x{bits:016x})")
        };
        self.alloc(name, sort)
    }

    fn fp_add(&mut self, a: Term, b: Term) -> Term {
        self.fp_binop_rne("fp.add", a, b)
    }
    fn fp_sub(&mut self, a: Term, b: Term) -> Term {
        self.fp_binop_rne("fp.sub", a, b)
    }
    fn fp_mul(&mut self, a: Term, b: Term) -> Term {
        self.fp_binop_rne("fp.mul", a, b)
    }
    fn fp_div(&mut self, a: Term, b: Term) -> Term {
        self.fp_binop_rne("fp.div", a, b)
    }
    fn fp_rem(&mut self, a: Term, b: Term) -> Term {
        // fp.rem takes no rounding mode.
        self.binop("fp.rem", a, b)
    }
    fn fp_neg(&mut self, a: Term) -> Term {
        self.unop_same_sort("fp.neg", a)
    }
    fn fp_abs(&mut self, a: Term) -> Term {
        self.unop_same_sort("fp.abs", a)
    }

    fn fp_eq(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("fp.eq", a, b)
    }
    fn fp_lt(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("fp.lt", a, b)
    }
    fn fp_le(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("fp.leq", a, b)
    }
    fn fp_gt(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("fp.gt", a, b)
    }
    fn fp_ge(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("fp.geq", a, b)
    }
    fn fp_is_nan(&mut self, a: Term) -> Term {
        self.unop_bool("fp.isNaN", a)
    }
    fn fp_is_infinite(&mut self, a: Term) -> Term {
        self.unop_bool("fp.isInfinite", a)
    }

    fn fp_from_bits(&mut self, bits: Term, width: u32) -> Term {
        let (e, m) = if width == 32 { (8, 24) } else { (11, 53) };
        self.convert(&format!("(_ to_fp {e} {m})"), bits, Sort::Fp(width), false)
    }

    fn fp_to_bits(&mut self, f: Term, width: u32) -> Term {
        // SMT-LIB has no direct float-to-bits, so introduce a fresh bitvector
        // and tie it to the float by the inverse conversion.
        //
        // The NaN case needs care. `doubleToRawLongBits` is unspecified across
        // NaN payloads, so any NaN pattern is acceptable — but "any NaN" is not
        // the same as "anything". Writing this as
        //
        //     (or (fp.isNaN f) (= (to_fp bv) f))
        //
        // is satisfied outright by the first disjunct whenever `f` is NaN,
        // which leaves `bv` completely unconstrained: the solver may report a
        // bit pattern that is not NaN and bears no relation to the value it
        // reasoned about. Witnesses are read out of exactly these bitvectors,
        // so the model and the reported witness silently diverge, and the
        // witness then fails JVM replay. That was losing most of
        // float-nonlinear-calculation (#56).
        //
        // The conditional form keeps the payload freedom while still requiring
        // `bv` to decode to *a* NaN.
        let (e, m) = if width == 32 { (8, 24) } else { (11, 53) };
        let bv = self.fresh_bv("fpbits", width);
        let bvn = self.name(bv);
        let fname = self.name(f);
        self.send(&format!(
            "(assert (ite (fp.isNaN {fname}) \
                          (fp.isNaN ((_ to_fp {e} {m}) {bvn})) \
                          (= ((_ to_fp {e} {m}) {bvn}) {fname})))"
        ));
        bv
    }

    fn fp_convert(&mut self, f: Term, to_width: u32) -> Term {
        let (e, m) = if to_width == 32 { (8, 24) } else { (11, 53) };
        self.convert(&format!("(_ to_fp {e} {m})"), f, Sort::Fp(to_width), true)
    }

    fn sbv_to_fp(&mut self, bv: Term, width: u32) -> Term {
        let (e, m) = if width == 32 { (8, 24) } else { (11, 53) };
        self.convert(&format!("(_ to_fp {e} {m})"), bv, Sort::Fp(width), true)
    }

    fn fp_to_sbv(&mut self, f: Term, width: u32) -> Term {
        // Java narrowing from float to int truncates toward zero (JLS 5.1.3).
        self.convert(&format!("(_ fp.to_sbv {width})"), f, Sort::Bv(width), true)
    }

    fn ite(&mut self, cond: Term, then_: Term, else_: Term) -> Term {
        let sort = self.sort(then_);
        let id = self.next_id;
        let name = format!("t_{id}");
        let cn = self.name(cond);
        let tn = self.name(then_);
        let en = self.name(else_);
        let cached = Self::sort_str(sort);
        if !cached.is_empty() {
            self.send(&format!("(define-const {name} {cached} (ite {cn} {tn} {en}))"));
        } else {
            let sort_s = Self::sort_str_dynamic(sort);
            self.send(&format!("(define-const {name} {sort_s} (ite {cn} {tn} {en}))"));
        }
        self.alloc(name, sort)
    }

    fn not(&mut self, t: Term) -> Term {
        let tn = self.name(t).to_string();
        let expr = format!("(not {tn})");
        self.define_term("t", &expr, Sort::Bool)
    }

    fn and(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("and", a, b)
    }

    fn or(&mut self, a: Term, b: Term) -> Term {
        self.binop_bool("or", a, b)
    }

    fn int_const(&mut self, value: i64) -> Term {
        let name = if value < 0 {
            format!("(- {})", -value)
        } else {
            value.to_string()
        };
        self.alloc(name, Sort::Int)
    }

    fn int_to_bv32(&mut self, t: Term) -> Term {
        // Z3: ((_ int2bv 32) x) — requires non-negative x for predictable results.
        let tn = self.name(t).to_string();
        let expr = format!("((_ int2bv 32) {tn})");
        self.define_term("t", &expr, Sort::Bv(32))
    }

    fn bv32_to_int(&mut self, t: Term) -> Term {
        let tn = self.name(t).to_string();
        let expr = format!("(bv2int {tn})");
        self.define_term("t", &expr, Sort::Int)
    }

    fn fresh_str(&mut self, name: &str) -> Term {
        let sname = format!("{name}_{}", self.next_id);
        self.send(&format!("(declare-const {sname} String)"));
        self.alloc(sname, Sort::Str)
    }

    fn str_const(&mut self, value: &str) -> Term {
        // Escape for SMT-LIB2 string literals (double up backslashes and quotes).
        let escaped = value.replace('\\', "\\\\").replace('"', "\"\"");
        let name = format!("\"{}\"", escaped);
        self.alloc(name, Sort::Str)
    }

    fn str_len(&mut self, s: Term) -> Term {
        let sn = self.name(s).to_string();
        let expr = format!("(str.len {sn})");
        self.define_term("t", &expr, Sort::Int)
    }

    fn str_contains(&mut self, haystack: Term, needle: Term) -> Term {
        let hn = self.name(haystack).to_string();
        let nn = self.name(needle).to_string();
        let expr = format!("(str.contains {hn} {nn})");
        self.define_term("t", &expr, Sort::Bool)
    }

    fn str_prefixof(&mut self, pre: Term, s: Term) -> Term {
        let pn = self.name(pre).to_string();
        let sn = self.name(s).to_string();
        let expr = format!("(str.prefixof {pn} {sn})");
        self.define_term("t", &expr, Sort::Bool)
    }

    fn str_suffixof(&mut self, suf: Term, s: Term) -> Term {
        let sfn = self.name(suf).to_string();
        let sn = self.name(s).to_string();
        let expr = format!("(str.suffixof {sfn} {sn})");
        self.define_term("t", &expr, Sort::Bool)
    }

    fn str_concat(&mut self, a: Term, b: Term) -> Term {
        let an = self.name(a).to_string();
        let bn = self.name(b).to_string();
        let expr = format!("(str.++ {an} {bn})");
        self.define_term("t", &expr, Sort::Str)
    }

    fn str_substr(&mut self, s: Term, offset: Term, len: Term) -> Term {
        let sn = self.name(s).to_string();
        let on = self.name(offset).to_string();
        let ln = self.name(len).to_string();
        let expr = format!("(str.substr {sn} {on} {ln})");
        self.define_term("t", &expr, Sort::Str)
    }

    fn str_indexof(&mut self, s: Term, t: Term, start: Term) -> Term {
        let sn = self.name(s).to_string();
        let tn = self.name(t).to_string();
        let start_n = self.name(start).to_string();
        let expr = format!("(str.indexof {sn} {tn} {start_n})");
        self.define_term("t", &expr, Sort::Int)
    }

    fn str_at(&mut self, s: Term, i: Term) -> Term {
        let sn = self.name(s).to_string();
        let in_ = self.name(i).to_string();
        let expr = format!("(str.at {sn} {in_})");
        self.define_term("t", &expr, Sort::Str)
    }

    fn str_to_int(&mut self, s: Term) -> Term {
        let sn = self.name(s).to_string();
        let expr = format!("(str.to_int {sn})");
        self.define_term("t", &expr, Sort::Int)
    }

    fn str_from_int(&mut self, i: Term) -> Term {
        let in_ = self.name(i).to_string();
        let expr = format!("(str.from_int {in_})");
        self.define_term("t", &expr, Sort::Str)
    }

    fn str_eq(&mut self, a: Term, b: Term) -> Term {
        let an = self.name(a).to_string();
        let bn = self.name(b).to_string();
        let expr = format!("(= {an} {bn})");
        self.define_term("t", &expr, Sort::Bool)
    }

    fn str_to_code(&mut self, s: Term) -> Term {
        let sn = self.name(s).to_string();
        let expr = format!("(str.to_code {sn})");
        self.define_term("t", &expr, Sort::Int)
    }

    fn str_from_code(&mut self, i: Term) -> Term {
        let in_ = self.name(i).to_string();
        let expr = format!("(str.from_code {in_})");
        self.define_term("t", &expr, Sort::Str)
    }

    fn str_replace_all(&mut self, s: Term, from: Term, to: Term) -> Term {
        let sn = self.name(s).to_string();
        let fn_ = self.name(from).to_string();
        let tn = self.name(to).to_string();
        let expr = format!("(str.replace_all {sn} {fn_} {tn})");
        self.define_term("t", &expr, Sort::Str)
    }

    fn str_lt(&mut self, a: Term, b: Term) -> Term {
        let an = self.name(a).to_string();
        let bn = self.name(b).to_string();
        let expr = format!("(str.< {an} {bn})");
        self.define_term("t", &expr, Sort::Bool)
    }

    fn fresh_array(&mut self, name: &str, elem_width: u32) -> Term {
        let sort = Sort::Array { idx: 32, elem: elem_width };
        let sname = format!("{name}_{}", self.next_id);
        let cached = Self::sort_str(sort);
        if !cached.is_empty() {
            self.send(&format!("(declare-const {sname} {cached})"));
        } else {
            let sort_s = Self::sort_str_dynamic(sort);
            self.send(&format!("(declare-const {sname} {sort_s})"));
        }
        self.alloc(sname, sort)
    }

    fn const_array(&mut self, val: Term, elem_width: u32) -> Term {
        let vn = self.name(val).to_string();
        let sort = Sort::Array { idx: 32, elem: elem_width };
        let cached = Self::sort_str(sort);
        let expr = if !cached.is_empty() {
            format!("((as const {cached}) {vn})")
        } else {
            let sort_s = Self::sort_str_dynamic(sort);
            format!("((as const {sort_s}) {vn})")
        };
        self.define_term("carr", &expr, sort)
    }

    fn array_select(&mut self, arr: Term, idx: Term) -> Term {
        let an = self.name(arr).to_string();
        let in_ = self.name(idx).to_string();
        let elem_sort = match self.sort(arr) {
            Sort::StrArray => Sort::Str,
            Sort::Array { elem, .. } => Sort::Bv(elem),
            _ => Sort::Bv(32),
        };
        let expr = format!("(select {an} {in_})");
        self.define_term("t", &expr, elem_sort)
    }

    fn array_store(&mut self, arr: Term, idx: Term, val: Term) -> Term {
        let an = self.name(arr).to_string();
        let in_ = self.name(idx).to_string();
        let vn = self.name(val).to_string();
        let sort = self.sort(arr);
        let expr = format!("(store {an} {in_} {vn})");
        self.define_term("t", &expr, sort)
    }

    fn fresh_str_array(&mut self, name: &str) -> Term {
        let sname = format!("{name}_{}", self.next_id);
        self.send(&format!("(declare-const {sname} (Array (_ BitVec 32) String))"));
        self.alloc(sname, Sort::StrArray)
    }

    fn const_str_array(&mut self, val: Term) -> Term {
        let vn = self.name(val).to_string();
        let expr = format!("((as const (Array (_ BitVec 32) String)) {vn})");
        self.define_term("carr", &expr, Sort::StrArray)
    }

    fn assert(&mut self, t: Term) {
        let tn = self.name(t).to_string();
        self.send(&format!("(assert {tn})"));
    }

    fn push(&mut self) {
        self.send("(push 1)");
    }

    fn pop(&mut self) {
        self.send("(pop 1)");
    }

    fn check_sat(&mut self) -> SatResult {
        self.send("(check-sat)");
        let resp = self.read_line();
        match resp.as_str() {
            "sat" => SatResult::Sat,
            "unsat" => SatResult::Unsat,
            _ => SatResult::Unknown,
        }
    }

    fn get_value_i64(&mut self, t: Term) -> Option<i64> {
        let tn = self.name(t).to_string();
        self.send(&format!("(get-value ({tn}))"));
        let resp = self.read_line();
        parse_bv_value(&resp)
    }

    fn get_value_string(&mut self, t: Term) -> Option<String> {
        let tn = self.name(t).to_string();
        self.send(&format!("(get-value ({tn}))"));
        let resp = self.read_line();
        parse_string_value(&resp)
    }
}

impl Drop for SmtLib {
    fn drop(&mut self) {
        let _ = self.stdin.flush();
        let _ = writeln!(self.stdin, "(exit)");
        let _ = self.stdin.flush();
        let _ = self.child.wait();
    }
}

/// Parse a bitvector value from an SMT-LIB2 `(get-value ...)` response.
/// Handles formats: `#xHEX`, `#bBIN`, `(_ bvN M)`, `(- ...)` for negative.
fn parse_bv_value(resp: &str) -> Option<i64> {
    // Response format: ((name value))
    // Find the value part after the term name.
    let inner = resp.trim_start_matches('(').trim_end_matches(')');
    // Find the last token group — could be `#xABCD`, `#b0101`, `(_ bv42 32)`.
    if let Some(pos) = inner.find("#x") {
        let hex = inner[pos + 2..].trim_end_matches(')').trim_end_matches(' ');
        let val = u64::from_str_radix(hex, 16).ok()?;
        // Determine width from hex digit count to do sign extension.
        let digits = hex.len();
        let width = digits * 4;
        return Some(sign_extend_to_i64(val, width));
    }
    if let Some(pos) = inner.find("#b") {
        let bin = inner[pos + 2..].trim_end_matches(')').trim_end_matches(' ');
        let val = u64::from_str_radix(bin, 2).ok()?;
        let width = bin.len();
        return Some(sign_extend_to_i64(val, width));
    }
    // (_ bvN W) format
    if let Some(pos) = inner.find("(_ bv") {
        let rest = &inner[pos + 5..];
        let parts: Vec<&str> = rest.trim_end_matches(')').split_whitespace().collect();
        if parts.len() >= 2 {
            let val: u64 = parts[0].parse().ok()?;
            let width: usize = parts[1].parse().ok()?;
            return Some(sign_extend_to_i64(val, width));
        }
    }
    None
}

/// Parse a string value from an SMT-LIB2 `(get-value ...)` response.
/// Response format: `((name "value"))`.
fn parse_string_value(resp: &str) -> Option<String> {
    // Parse SMT-LIB2 string literal from `(get-value ...)` response.
    // Response format: `((name "content"))`.  In SMT-LIB2 `""` inside a
    // string literal represents a single `"`, so naive rfind-based parsing
    // breaks on strings containing quotes.
    let bytes = resp.as_bytes();
    // Find the first `"` — this opens the string literal value.
    let open = bytes.iter().position(|&b| b == b'"')?;
    let mut result = String::new();
    let mut i = open + 1;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                result.push('"');
                i += 2;
            } else {
                break; // closing quote
            }
        } else {
            result.push(bytes[i] as char);
            i += 1;
        }
    }
    Some(result)
}

fn sign_extend_to_i64(val: u64, width: usize) -> i64 {
    if width >= 64 {
        val as i64
    } else if width == 0 {
        0
    } else {
        let sign_bit = 1u64 << (width - 1);
        if val & sign_bit != 0 {
            // Sign-extend: fill upper bits with 1s.
            let mask = !((1u64 << width) - 1);
            (val | mask) as i64
        } else {
            val as i64
        }
    }
}

pub struct SmtLibFactory {
    solver_binary: String,
    extra_args: Vec<String>,
}

impl SmtLibFactory {
    /// Read solver config from environment. Returns `None` if the solver binary
    /// is not found on PATH.
    pub fn from_env() -> Option<Self> {
        let binary = std::env::var("ROAST_SMT_SOLVER").unwrap_or_else(|_| "z3".to_string());

        // Check if binary exists on PATH.
        let check = Command::new("which")
            .arg(&binary)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
        match check {
            Ok(s) if s.success() => {}
            _ => {
                debug!("smt: solver binary '{binary}' not found on PATH, skipping SMT engine");
                return None;
            }
        }

        let extra_args = default_args(&binary);
        debug!("smt: using solver '{binary}' with args {extra_args:?}");
        Some(SmtLibFactory {
            solver_binary: binary,
            extra_args,
        })
    }
}

fn default_args(binary: &str) -> Vec<String> {
    // Strip path to get just the binary name for matching.
    let name = binary.rsplit('/').next().unwrap_or(binary);
    match name {
        // Fixed seeds. z3's model choice is affected by internal randomness,
        // and a different (still valid) model means a different witness — only
        // some of which reproduce on a real JVM, so the verdict flips between
        // FALSE and UNKNOWN across identical runs (#66). A verifier must not
        // depend on a solver's random seed.
        "z3" => vec![
            "-in".into(),
            "-smt2".into(),
            "sat.random_seed=0".into(),
            "smt.random_seed=0".into(),
            "nlsat.seed=0".into(),
        ],
        "bitwuzla" => vec!["--smt2".into()],
        "cvc5" => vec!["--lang".into(), "smt2".into(), "--incremental".into()],
        _ => vec![],
    }
}

impl SolverFactory for SmtLibFactory {
    fn create(&self) -> Result<Box<dyn Solver>, String> {
        let mut child = Command::new(&self.solver_binary)
            .args(&self.extra_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|e| format!("failed to spawn {}: {e}", self.solver_binary))?;

        let stdin = child.stdin.take().ok_or("no stdin")?;
        let stdout = child.stdout.take().ok_or("no stdout")?;

        let mut solver = SmtLib {
            child,
            stdin: BufWriter::new(stdin),
            stdout: BufReader::new(stdout),
            next_id: 0,
            term_names: HashMap::new(),
            term_sorts: HashMap::new(),
            bv_const_cache: HashMap::new(),
            bool_true: None,
            bool_false: None,
        };

        // Preamble
        solver.send("(set-logic ALL)");
        solver.send("(set-option :produce-models true)");

        Ok(Box::new(solver))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_hex_value() {
        assert_eq!(parse_bv_value("((x_0 #x00000001))"), Some(1));
        assert_eq!(parse_bv_value("((x_0 #xffffffff))"), Some(-1));
        assert_eq!(parse_bv_value("((x_0 #x000003e8))"), Some(1000));
    }

    #[test]
    fn parse_bv_decimal() {
        assert_eq!(parse_bv_value("((x_0 (_ bv1000 32)))"), Some(1000));
    }

    #[test]
    fn sign_extend_works() {
        assert_eq!(sign_extend_to_i64(0xFFFFFFFF, 32), -1i64);
        assert_eq!(sign_extend_to_i64(1, 32), 1i64);
        assert_eq!(sign_extend_to_i64(0x80000000, 32), i32::MIN as i64);
    }
}
