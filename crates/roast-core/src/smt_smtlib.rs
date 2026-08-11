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
        let hex_digits = (width as usize) / 4;
        let name = format!("#x{uval:0>hex_digits$x}");
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
        let elem_width = match self.sort(arr) {
            Sort::Array { elem, .. } => elem,
            _ => 32,
        };
        let expr = format!("(select {an} {in_})");
        self.define_term("t", &expr, Sort::Bv(elem_width))
    }

    fn array_store(&mut self, arr: Term, idx: Term, val: Term) -> Term {
        let an = self.name(arr).to_string();
        let in_ = self.name(idx).to_string();
        let vn = self.name(val).to_string();
        let sort = self.sort(arr);
        let expr = format!("(store {an} {in_} {vn})");
        self.define_term("t", &expr, sort)
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
    let start = resp.rfind('"')?;
    // Find the matching opening quote by scanning backwards.
    let inner = &resp[..start];
    let open = inner.rfind('"')?;
    let raw = &resp[open + 1..start];
    // Unescape SMT-LIB2 string: `""` → `"`, `\\` → `\`.
    Some(raw.replace("\"\"", "\"").replace("\\\\", "\\"))
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
        "z3" => vec!["-in".into(), "-smt2".into()],
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
