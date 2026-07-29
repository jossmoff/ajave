//! Tier 2, made real: bounded concrete execution over a small candidate set
//! for every `nondet` value, with exceptional control flow actually routed
//! through the handlers the frontend already computed.
//!
//! This is deliberately not full BMC -- there's no solver, no unrolling
//! variable, no SMT encoding. It is exactly the "self-certifying falsifier"
//! described early on: enumerate a handful of representative values
//! (0, ±1, extremes, and for strings a small pool) rather than solving for
//! one, execute the program for real against each combination, and report a
//! bug the moment a `Check` fails somewhere the exception can't be caught.
//! Because the values are concrete, the witness is just "here is what we ran"
//! -- no independent trust in the engine is required to believe it, only the
//! interpreter's own determinism (confirmed by `certify::JvmReplay`).
//!
//! String tracking: `nondetString()` produces a `Nondet(Ty::Str)` rvalue in
//! the IR. The engine picks one of `STRING_CANDIDATES` by using the raw choice
//! value as a modular index, allocates a fresh reference ID, and records the
//! content in `str_store`. String method calls remain in the IR as
//! `Rvalue::Call` (via `CallModel::StrCall`) so this interpreter can evaluate
//! them against the tracked content instead of returning Unknown.

use std::collections::HashMap;

use log::{debug, info};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::verdict::Witness;
use roast_ir::*;
use roast_models as models;

/// A small pool of representative strings. Index 0 is the empty string so
/// that the all-zero probe (which gives the slot count) tests the empty-string
/// case, which is the most common degenerate input.
const STRING_CANDIDATES: &[&str] = &["", "a", "ab", "abcde", "aaaaa", "hello", "abc", "test"];

#[derive(Clone, Copy, Debug, PartialEq)]
enum Value {
    I32(i32),
    I64(i64),
    /// Unique allocation identity.  0 = null; 1 = non-null constant (string
    /// literals, class objects, any opaque non-null ref we didn't allocate
    /// ourselves); values ≥ 2 are fresh allocations from `alloc_id`.
    Ref(u64),
    Unknown,
}

impl Value {
    fn as_i64(self) -> i64 {
        match self {
            Value::I32(v) => v as i64,
            Value::I64(v) => v,
            _ => 0,
        }
    }
    fn nonzero(self) -> bool {
        match self {
            Value::I32(v) => v != 0,
            Value::I64(v) => v != 0,
            Value::Ref(id) => id != 0,
            Value::Unknown => false,
        }
    }
}

const INT_CANDIDATES: [i32; 7] = [0, 1, -1, 2, -2, i32::MAX, i32::MIN];

#[allow(dead_code)]
const LONG_CANDIDATES: [i64; 5] = [0, 1, -1, i64::MAX, i64::MIN];

/// Map a raw choice integer to an index into `STRING_CANDIDATES`.
fn str_idx(raw: i64, len: usize) -> usize {
    ((raw % len as i64 + len as i64) % len as i64) as usize
}

/// Outcome of running one concrete path to completion.
enum Outcome {
    /// Ran to a `Return` with nothing amiss.
    Clean,
    /// `Verifier.assume` failed: this path is uninteresting, not unsafe.
    Halted,
    /// A `Check` failed with nothing able to catch it.
    Violated {
        oid: ObligationId,
        witness: Vec<i64>,
    },
    /// Ran out of budget or hit something we can't interpret.
    Inconclusive,
}

/// The evaluator for everything except `Nondet` and string method `Call`s,
/// which `run_with_choices` intercepts before they ever reach here.
struct Run {
    store: HashMap<VarId, Value>,
}

impl Run {
    fn eval(&self, op: &Operand) -> Value {
        match op {
            Operand::Var(v) => self.store.get(v).copied().unwrap_or(Value::Unknown),
            Operand::Const(Const::Int(n)) => Value::I32(*n),
            Operand::Const(Const::Long(n)) => Value::I64(*n),
            Operand::Const(Const::Null) => Value::Ref(0),
            // String literals and class constants are non-null, but we don't
            // allocate a unique ID for them (they're interned constants).
            Operand::Const(_) => Value::Ref(1),
        }
    }

    fn eval_rvalue(&mut self, rv: &Rvalue) -> Value {
        match rv {
            Rvalue::Use(o) => self.eval(o),
            Rvalue::Neg(o) => match self.eval(o) {
                Value::I32(v) => Value::I32(v.wrapping_neg()),
                Value::I64(v) => Value::I64(v.wrapping_neg()),
                _ => Value::Unknown,
            },
            Rvalue::Bin(op, a, b) => self.eval_bin(*op, self.eval(a), self.eval(b)),
            Rvalue::New(_cls) => Value::Unknown, // handled in run_with_choices
            Rvalue::NewArray { .. } => Value::Ref(0), // handled in run_with_choices
            Rvalue::GetStatic(_) | Rvalue::GetField { .. } | Rvalue::ArrayLoad { .. } => {
                Value::Unknown
            }
            Rvalue::ArrayLength(_) => Value::Unknown,
            Rvalue::InstanceOf { .. } => Value::Unknown,
            // String/StringBuilder calls are intercepted in run_with_choices
            // before reaching here. Any remaining Call (unmodelled code that
            // survived the lifter without diverging) returns Unknown.
            Rvalue::Call { .. } => Value::Unknown,
            Rvalue::Cast(ty, o) => match (ty, self.eval(o)) {
                (Ty::Int, Value::I64(v)) => Value::I32(v as i32),
                (Ty::Long, Value::I32(v)) => Value::I64(v as i64),
                (_, v) => v,
            },
            Rvalue::Cmp(a, b) => {
                let av = self.eval(a);
                let bv = self.eval(b);
                if matches!(av, Value::Unknown) || matches!(bv, Value::Unknown) {
                    return Value::Unknown;
                }
                let (x, y) = (av.as_i64(), bv.as_i64());
                Value::I32(x.cmp(&y) as i32)
            }
            Rvalue::Nondet(_) => unreachable!("Nondet is handled in run_with_choices"),
        }
    }

    fn eval_bin(&self, op: BinOp, a: Value, b: Value) -> Value {
        use BinOp::*;

        // Unknown propagation: any unknown operand yields an unknown result.
        if matches!(a, Value::Unknown) || matches!(b, Value::Unknown) {
            return Value::Unknown;
        }

        let wide = matches!(a, Value::I64(_)) || matches!(b, Value::I64(_));
        match op {
            Eq | Ne | Lt | Le | Gt | Ge => {
                if let (Value::Ref(na), Value::Ref(nb)) = (a, b) {
                    let eq = na == nb;
                    return Value::I32(match op {
                        Eq => eq as i32,
                        Ne => !eq as i32,
                        _ => 0,
                    });
                }
                let (x, y) = (a.as_i64(), b.as_i64());
                let r = match op {
                    Eq => x == y,
                    Ne => x != y,
                    Lt => x < y,
                    Le => x <= y,
                    Gt => x > y,
                    Ge => x >= y,
                    _ => unreachable!(),
                };
                Value::I32(r as i32)
            }
            Add | Sub | Mul | Div | Rem if wide => {
                let (x, y) = (a.as_i64(), b.as_i64());
                Value::I64(match op {
                    Add => x.wrapping_add(y),
                    Sub => x.wrapping_sub(y),
                    Mul => x.wrapping_mul(y),
                    Div => x.checked_div(y).unwrap_or(0),
                    Rem => x.checked_rem(y).unwrap_or(0),
                    _ => unreachable!(),
                })
            }
            Add | Sub | Mul | Div | Rem => {
                let (x, y) = (a.as_i64() as i32, b.as_i64() as i32);
                Value::I32(match op {
                    Add => x.wrapping_add(y),
                    Sub => x.wrapping_sub(y),
                    Mul => x.wrapping_mul(y),
                    Div => x.checked_div(y).unwrap_or(0),
                    Rem => x.checked_rem(y).unwrap_or(0),
                    _ => unreachable!(),
                })
            }
            And | Or | Xor | Shl | Shr | UShr => {
                let (x, y) = (a.as_i64() as i32, b.as_i64() as i32);
                Value::I32(match op {
                    And => x & y,
                    Or => x | y,
                    Xor => x ^ y,
                    Shl => x.wrapping_shl(y as u32),
                    Shr => x.wrapping_shr(y as u32),
                    UShr => ((x as u32) >> (y as u32 & 31)) as i32,
                    _ => unreachable!(),
                })
            }
        }
    }
}

/// Find a handler in `block`'s exceptional edges matching `class`, preferring
/// the first that covers it (mirrors JVM handler-table ordering: first match
/// wins).
fn route(prog: &Program, block: &Block, class: &str) -> Option<BlockId> {
    for e in &block.exceptional {
        match &e.class {
            None => return Some(e.target),
            Some(c) if prog.is_subtype(class, c) => return Some(e.target),
            _ => {}
        }
    }
    None
}

/// Look up the string content for an operand, consulting both the string store
/// (for String values) and the StringBuilder store.
fn get_str_content<'a>(
    op: &Operand,
    store: &HashMap<VarId, Value>,
    str_store: &'a HashMap<u64, String>,
    sb_store: &'a HashMap<u64, String>,
) -> Option<String> {
    match op {
        Operand::Const(Const::Str(s)) => Some(s.clone()),
        Operand::Var(vid) => match store.get(vid)? {
            Value::Ref(aid) => str_store.get(aid).or_else(|| sb_store.get(aid)).cloned(),
            _ => None,
        },
        _ => None,
    }
}

/// Extract the allocation ID from a Var operand.
fn get_ref_id(op: &Operand, store: &HashMap<VarId, Value>) -> Option<u64> {
    match op {
        Operand::Var(vid) => match store.get(vid)? {
            Value::Ref(aid) => Some(*aid),
            _ => None,
        },
        _ => None,
    }
}

/// Evaluate a string/StringBuilder method call, returning the result value.
/// Mutates `str_store`, `sb_store`, and `alloc_id` for allocating new strings
/// and mutating StringBuilder content in place (keyed by allocation ID).
fn eval_str_call(
    target: &MethodKey,
    args: &[Operand],
    store: &HashMap<VarId, Value>,
    str_store: &mut HashMap<u64, String>,
    sb_store: &mut HashMap<u64, String>,
    alloc_id: &mut u64,
) -> Value {
    let recv_aid = args.first().and_then(|a| get_ref_id(a, store));

    // Content look-up helper (cannot be a closure since it would conflict with
    // the mutable borrows of str_store/sb_store below).
    macro_rules! str_of {
        ($op:expr) => {
            get_str_content($op, store, str_store, sb_store)
        };
    }

    macro_rules! recv_str {
        () => {
            recv_aid.and_then(|aid| str_store.get(&aid).cloned())
        };
    }
    macro_rules! recv_sb {
        () => {
            recv_aid.and_then(|aid| sb_store.get(&aid).cloned())
        };
    }

    macro_rules! alloc_str {
        ($s:expr) => {{
            let aid = *alloc_id;
            *alloc_id += 1;
            str_store.insert(aid, $s);
            Value::Ref(aid)
        }};
    }

    match target.name.as_str() {
        // ---- String / StringBuilder / StringBuffer constructors ----
        "<init>" => {
            if let Some(aid) = recv_aid {
                let init = str_of!(args.get(1).unwrap_or(&Operand::Const(Const::Null)))
                    .unwrap_or_default();
                if target.class == "java/lang/String" {
                    // new String(s) — copies content into an immutable String.
                    str_store.insert(aid, init);
                } else {
                    // StringBuilder/StringBuffer — mutable.
                    sb_store.insert(aid, init);
                }
            }
            // void return — the temp that receives this is unused
            Value::I32(0)
        }

        // ---- StringBuilder.append ----
        "append" => {
            if let Some(aid) = recv_aid {
                let to_append: Option<String> = if let Some(arg) = args.get(1) {
                    match str_of!(arg) {
                        Some(s) => Some(s),
                        None => match arg {
                            Operand::Var(vid) => match store.get(vid).copied() {
                                Some(Value::I32(n)) => Some(n.to_string()),
                                Some(Value::I64(n)) => Some(n.to_string()),
                                _ => None,
                            },
                            Operand::Const(Const::Int(n)) => Some(n.to_string()),
                            _ => None,
                        },
                    }
                } else {
                    None
                };
                if let Some(s) = to_append {
                    sb_store.entry(aid).or_default().push_str(&s);
                } else {
                    // Unknown append: content is no longer known
                    sb_store.remove(&aid);
                }
            }
            // append returns `this`
            args.first()
                .and_then(|a| match a {
                    Operand::Var(vid) => store.get(vid).copied(),
                    _ => None,
                })
                .unwrap_or(Value::Unknown)
        }

        // ---- StringBuilder.toString ----
        "toString" => {
            if let Some(content) = recv_sb!() {
                alloc_str!(content)
            } else {
                Value::Unknown
            }
        }

        // ---- StringBuilder.reverse ----
        "reverse" => {
            if let Some(aid) = recv_aid {
                if let Some(s) = sb_store.get_mut(&aid) {
                    *s = s.chars().rev().collect();
                }
            }
            args.first()
                .and_then(|a| match a {
                    Operand::Var(vid) => store.get(vid).copied(),
                    _ => None,
                })
                .unwrap_or(Value::Unknown)
        }

        // ---- StringBuilder.setCharAt ----
        "setCharAt" => {
            if let Some(aid) = recv_aid {
                let idx_v = args.get(1).and_then(|a| match a {
                    Operand::Var(vid) => match store.get(vid) {
                        Some(Value::I32(n)) => Some(*n),
                        _ => None,
                    },
                    Operand::Const(Const::Int(n)) => Some(*n),
                    _ => None,
                });
                let ch_v = args.get(2).and_then(|a| match a {
                    Operand::Var(vid) => match store.get(vid) {
                        Some(Value::I32(n)) => Some(*n),
                        _ => None,
                    },
                    Operand::Const(Const::Int(n)) => Some(*n),
                    _ => None,
                });
                if let (Some(i), Some(c)) = (idx_v, ch_v) {
                    if let Some(s) = sb_store.get_mut(&aid) {
                        let i = i as usize;
                        if i < s.len() {
                            let ch = char::from_u32(c as u32).unwrap_or('\0');
                            let mut cs: Vec<char> = s.chars().collect();
                            cs[i] = ch;
                            *s = cs.into_iter().collect();
                        }
                    }
                }
            }
            Value::I32(0) // void
        }

        // ---- StringBuilder.delete ----
        "delete" => {
            if let Some(aid) = recv_aid {
                let start = args.get(1).and_then(|a| match a {
                    Operand::Var(vid) => match store.get(vid) {
                        Some(Value::I32(n)) => Some(*n as usize),
                        _ => None,
                    },
                    Operand::Const(Const::Int(n)) => Some(*n as usize),
                    _ => None,
                });
                let end = args.get(2).and_then(|a| match a {
                    Operand::Var(vid) => match store.get(vid) {
                        Some(Value::I32(n)) => Some(*n as usize),
                        _ => None,
                    },
                    Operand::Const(Const::Int(n)) => Some(*n as usize),
                    _ => None,
                });
                if let (Some(s), Some(e)) = (start, end) {
                    if let Some(sb) = sb_store.get_mut(&aid) {
                        if s <= e && e <= sb.len() {
                            sb.drain(s..e);
                        }
                    }
                }
            }
            args.first()
                .and_then(|a| match a {
                    Operand::Var(vid) => store.get(vid).copied(),
                    _ => None,
                })
                .unwrap_or(Value::Unknown)
        }

        // ---- StringBuilder.insert ----
        "insert" => {
            if let Some(aid) = recv_aid {
                let offset = args.get(1).and_then(|a| match a {
                    Operand::Var(vid) => match store.get(vid) {
                        Some(Value::I32(n)) => Some(*n as usize),
                        _ => None,
                    },
                    Operand::Const(Const::Int(n)) => Some(*n as usize),
                    _ => None,
                });
                let ins = args.get(2).and_then(|a| str_of!(a));
                if let (Some(off), Some(s)) = (offset, ins) {
                    if let Some(sb) = sb_store.get_mut(&aid) {
                        if off <= sb.len() {
                            sb.insert_str(off, &s);
                        }
                    }
                } else {
                    // Unknown insert: content no longer known
                    if let Some(aid) = recv_aid {
                        sb_store.remove(&aid);
                    }
                }
            }
            args.first()
                .and_then(|a| match a {
                    Operand::Var(vid) => store.get(vid).copied(),
                    _ => None,
                })
                .unwrap_or(Value::Unknown)
        }

        // ---- String.length / StringBuilder.length ----
        "length" => {
            let content =
                recv_aid.and_then(|aid| str_store.get(&aid).or_else(|| sb_store.get(&aid)));
            match content {
                Some(s) => Value::I32(s.len() as i32),
                None => Value::Unknown,
            }
        }

        // ---- String.isEmpty ----
        "isEmpty" => {
            let content =
                recv_aid.and_then(|aid| str_store.get(&aid).or_else(|| sb_store.get(&aid)));
            match content {
                Some(s) => Value::I32(s.is_empty() as i32),
                None => Value::Unknown,
            }
        }

        // ---- String.charAt / StringBuilder.charAt ----
        "charAt" => {
            let content = recv_aid
                .and_then(|aid| str_store.get(&aid).or_else(|| sb_store.get(&aid)))
                .cloned();
            let idx_v = args.get(1).and_then(|a| match a {
                Operand::Var(vid) => store.get(vid).copied(),
                Operand::Const(Const::Int(n)) => Some(Value::I32(*n)),
                _ => None,
            });
            match (content, idx_v) {
                (Some(s), Some(Value::I32(i))) if i >= 0 && (i as usize) < s.len() => {
                    let ch = s.chars().nth(i as usize).unwrap_or('\0');
                    Value::I32(ch as i32)
                }
                (Some(_), Some(Value::I32(_))) => {
                    // Out-of-bounds charAt: StringIndexOutOfBoundsException.
                    // The concrete engine can't route it (no Obligation), so
                    // treat as Inconclusive (Unknown) for this path.
                    Value::Unknown
                }
                _ => Value::Unknown,
            }
        }

        // ---- String.equals / equalsIgnoreCase ----
        "equals" | "equalsIgnoreCase" => {
            let a = recv_str!();
            let b = args.get(1).and_then(|op| str_of!(op));
            match (a, b) {
                (Some(a), Some(b)) => {
                    let eq = if target.name == "equalsIgnoreCase" {
                        a.to_lowercase() == b.to_lowercase()
                    } else {
                        a == b
                    };
                    Value::I32(eq as i32)
                }
                _ => Value::Unknown,
            }
        }

        // ---- String.compareTo / compareToIgnoreCase ----
        "compareTo" | "compareToIgnoreCase" => {
            let a = recv_str!();
            let b = args.get(1).and_then(|op| str_of!(op));
            match (a, b) {
                (Some(a), Some(b)) => {
                    let ord = if target.name == "compareToIgnoreCase" {
                        a.to_lowercase().cmp(&b.to_lowercase())
                    } else {
                        a.cmp(&b)
                    };
                    Value::I32(ord as i32)
                }
                _ => Value::Unknown,
            }
        }

        // ---- String.startsWith ----
        "startsWith" => {
            let a = recv_str!();
            let b = args.get(1).and_then(|op| str_of!(op));
            match (a, b) {
                (Some(a), Some(b)) => Value::I32(a.starts_with(b.as_str()) as i32),
                _ => Value::Unknown,
            }
        }

        // ---- String.endsWith ----
        "endsWith" => {
            let a = recv_str!();
            let b = args.get(1).and_then(|op| str_of!(op));
            match (a, b) {
                (Some(a), Some(b)) => Value::I32(a.ends_with(b.as_str()) as i32),
                _ => Value::Unknown,
            }
        }

        // ---- String.contains ----
        "contains" => {
            let a = recv_str!();
            let b = args.get(1).and_then(|op| str_of!(op));
            match (a, b) {
                (Some(a), Some(b)) => Value::I32(a.contains(b.as_str()) as i32),
                _ => Value::Unknown,
            }
        }

        // ---- String.indexOf ----
        "indexOf" => {
            let haystack = recv_str!();
            match haystack {
                Some(h) => {
                    let result = match args.get(1) {
                        Some(Operand::Var(vid)) => match store.get(vid).copied() {
                            Some(Value::I32(c)) => {
                                // indexOf(int ch)
                                char::from_u32(c as u32)
                                    .and_then(|ch| h.find(ch))
                                    .map(|i| i as i32)
                                    .unwrap_or(-1)
                            }
                            Some(Value::Ref(aid)) => {
                                // indexOf(String)
                                match str_store.get(&aid) {
                                    Some(needle) => {
                                        h.find(needle.as_str()).map(|i| i as i32).unwrap_or(-1)
                                    }
                                    None => return Value::Unknown,
                                }
                            }
                            _ => return Value::Unknown,
                        },
                        Some(Operand::Const(Const::Int(c))) => char::from_u32(*c as u32)
                            .and_then(|ch| h.find(ch))
                            .map(|i| i as i32)
                            .unwrap_or(-1),
                        Some(Operand::Const(Const::Str(needle))) => {
                            h.find(needle.as_str()).map(|i| i as i32).unwrap_or(-1)
                        }
                        _ => return Value::Unknown,
                    };
                    Value::I32(result)
                }
                None => Value::Unknown,
            }
        }

        // ---- String.substring ----
        "substring" => {
            let s = recv_str!();
            match s {
                Some(s) => {
                    let start = match args.get(1) {
                        Some(Operand::Var(vid)) => match store.get(vid) {
                            Some(Value::I32(n)) => *n as usize,
                            _ => return Value::Unknown,
                        },
                        Some(Operand::Const(Const::Int(n))) => *n as usize,
                        _ => return Value::Unknown,
                    };
                    let end = match args.get(2) {
                        Some(Operand::Var(vid)) => match store.get(vid) {
                            Some(Value::I32(n)) => *n as usize,
                            _ => return Value::Unknown,
                        },
                        Some(Operand::Const(Const::Int(n))) => *n as usize,
                        None => s.len(),
                        _ => return Value::Unknown,
                    };
                    if start <= end && end <= s.len() {
                        alloc_str!(s[start..end].to_owned())
                    } else {
                        Value::Unknown // StringIndexOutOfBoundsException
                    }
                }
                None => Value::Unknown,
            }
        }

        // ---- String.concat ----
        "concat" => {
            let a = recv_str!();
            let b = args.get(1).and_then(|op| str_of!(op));
            match (a, b) {
                (Some(a), Some(b)) => alloc_str!(a + &b),
                _ => Value::Unknown,
            }
        }

        // ---- String.toUpperCase / toLowerCase ----
        "toUpperCase" | "toLowerCase" => match recv_str!() {
            Some(s) => {
                let r = if target.name == "toUpperCase" {
                    s.to_uppercase()
                } else {
                    s.to_lowercase()
                };
                alloc_str!(r)
            }
            None => Value::Unknown,
        },

        // ---- String.trim ----
        "trim" => match recv_str!() {
            Some(s) => alloc_str!(s.trim().to_owned()),
            None => Value::Unknown,
        },

        // ---- String.valueOf (static) ----
        "valueOf" => {
            let result = match args.first() {
                Some(Operand::Var(vid)) => match store.get(vid).copied() {
                    Some(Value::I32(n)) => Some(n.to_string()),
                    Some(Value::I64(n)) => Some(n.to_string()),
                    Some(Value::Ref(aid)) => str_store.get(&aid).cloned(),
                    _ => None,
                },
                Some(Operand::Const(Const::Int(n))) => Some(n.to_string()),
                Some(Operand::Const(Const::Str(s))) => Some(s.clone()),
                _ => None,
            };
            match result {
                Some(s) => alloc_str!(s),
                None => Value::Unknown,
            }
        }

        // ---- String.regionMatches ----
        "regionMatches" => {
            // Two forms:
            //   regionMatches(int toffset, String other, int ooffset, int len)
            //   regionMatches(boolean ignoreCase, int toffset, String other, int ooffset, int len)
            let recv = recv_str!();
            match recv {
                None => Value::Unknown,
                Some(this_str) => {
                    let get_int = |i: usize| -> Option<i32> {
                        match args.get(i)? {
                            Operand::Var(vid) => match store.get(vid)? {
                                Value::I32(n) => Some(*n),
                                _ => None,
                            },
                            Operand::Const(Const::Int(n)) => Some(*n),
                            _ => None,
                        }
                    };
                    let (ignore_case, toffset_i, other_i, ooffset_i, len_i) = if args.len() == 6 {
                        let ic = match args.get(1) {
                            Some(Operand::Var(vid)) => {
                                matches!(store.get(vid), Some(Value::I32(n)) if *n != 0)
                            }
                            Some(Operand::Const(Const::Int(n))) => *n != 0,
                            _ => return Value::Unknown,
                        };
                        (ic, 2usize, 3usize, 4usize, 5usize)
                    } else {
                        (false, 1usize, 2usize, 3usize, 4usize)
                    };
                    let toffset = match get_int(toffset_i) {
                        Some(n) if n >= 0 => n as usize,
                        Some(_) => return Value::I32(0), // negative offset → false
                        None => return Value::Unknown,
                    };
                    let other_str = match args.get(other_i).and_then(|a| str_of!(a)) {
                        Some(s) => s,
                        None => return Value::Unknown,
                    };
                    let ooffset = match get_int(ooffset_i) {
                        Some(n) if n >= 0 => n as usize,
                        Some(_) => return Value::I32(0),
                        None => return Value::Unknown,
                    };
                    let len = match get_int(len_i) {
                        Some(n) if n >= 0 => n as usize,
                        Some(_) => return Value::I32(0),
                        None => return Value::Unknown,
                    };
                    // Out-of-range → false (mirrors Java semantics)
                    if toffset + len > this_str.len() || ooffset + len > other_str.len() {
                        return Value::I32(0);
                    }
                    let ts = &this_str[toffset..toffset + len];
                    let os = &other_str[ooffset..ooffset + len];
                    let eq = if ignore_case {
                        ts.to_lowercase() == os.to_lowercase()
                    } else {
                        ts == os
                    };
                    Value::I32(eq as i32)
                }
            }
        }

        // ---- String.intern ----
        "intern" => {
            // intern() returns `this` for our purposes (content unchanged)
            args.first()
                .and_then(|a| match a {
                    Operand::Var(vid) => store.get(vid).copied(),
                    _ => None,
                })
                .unwrap_or(Value::Unknown)
        }

        _ => Value::Unknown,
    }
}

/// Run the body once against a fully-predetermined sequence of nondet
/// choices. Choices beyond what's provided fall back to `0`, which is
/// why the outer search widens the candidate list on the values it controls
/// rather than needing true backtracking here.
fn run_with_choices(prog: &Program, body: &Body, choices: &[i64], step_budget: u64) -> Outcome {
    let mut store: HashMap<VarId, Value> = HashMap::new();
    // Tracks the concrete class name of allocated objects, keyed by alloc_id.
    // Keying by alloc_id (rather than VarId) means aliasing through assignments
    // is handled automatically: all variables pointing to the same alloc share
    // the same type entry.
    let mut alloc_types: HashMap<u64, String> = HashMap::new();
    // Tracks the concrete length of NewArray-allocated arrays, keyed by alloc_id.
    let mut array_lengths: HashMap<u64, i64> = HashMap::new();
    // Tracks the string content of allocated String objects, keyed by
    // allocation ID so aliasing (s1 = s2) is handled correctly.
    let mut str_store: HashMap<u64, String> = HashMap::new();
    // Tracks the mutable content of StringBuilder / StringBuffer objects.
    let mut sb_store: HashMap<u64, String> = HashMap::new();
    // Allocation counter. 0 = null, 1 = constant non-null, ≥2 = fresh alloc.
    let mut alloc_id: u64 = 2;

    let mut choice_idx = 0usize;
    let mut trace = Vec::new();
    let mut steps = step_budget;

    let mut block = body.entry;
    let mut idx = 0usize;

    loop {
        if steps == 0 {
            return Outcome::Inconclusive;
        }
        steps -= 1;

        let b = body.block(block);
        if idx >= b.stmts.len() {
            match &b.term {
                Terminator::Goto(t) => {
                    block = *t;
                    idx = 0;
                }
                Terminator::Branch { cond, then_, else_ } => {
                    let taken = store
                        .get(match cond {
                            Operand::Var(v) => v,
                            _ => unreachable!("branch cond is always a temp"),
                        })
                        .copied()
                        .unwrap_or(Value::Unknown)
                        .nonzero();
                    block = if taken { *then_ } else { *else_ };
                    idx = 0;
                }
                Terminator::Switch {
                    value,
                    cases,
                    default,
                } => {
                    let v = match value {
                        Operand::Var(vid) => store.get(vid).copied().unwrap_or(Value::Unknown),
                        other => Value::I32(match other {
                            Operand::Const(Const::Int(n)) => *n,
                            _ => 0,
                        }),
                    }
                    .as_i64() as i32;
                    block = cases
                        .iter()
                        .find(|(k, _)| *k == v)
                        .map(|(_, t)| *t)
                        .unwrap_or(*default);
                    idx = 0;
                }
                Terminator::Return(_) => return Outcome::Clean,
                Terminator::Halt => return Outcome::Halted,
                Terminator::Throw(v) => {
                    let _ = v;
                    return Outcome::Inconclusive;
                }
                Terminator::Diverge(_) => return Outcome::Inconclusive,
            }
            continue;
        }

        match &b.stmts[idx] {
            Stmt::Assign(v, rv) => {
                let val = match rv {
                    Rvalue::Nondet(ty) => {
                        let raw = choices.get(choice_idx).copied().unwrap_or(0);
                        choice_idx += 1;
                        match ty {
                            Ty::Str => {
                                // Pick from the string pool using the raw choice
                                // as a modular index, allocate a fresh ref.
                                let sidx = str_idx(raw, STRING_CANDIDATES.len());
                                trace.push(raw);
                                let aid = alloc_id;
                                alloc_id += 1;
                                str_store.insert(aid, STRING_CANDIDATES[sidx].to_owned());
                                Value::Ref(aid)
                            }
                            Ty::Ref => {
                                // Non-string reference: allocate a fresh non-null ref.
                                let aid = alloc_id;
                                alloc_id += 1;
                                Value::Ref(aid)
                            }
                            Ty::Long => {
                                trace.push(raw);
                                Value::I64(raw)
                            }
                            _ => {
                                trace.push(raw);
                                Value::I32(raw as i32)
                            }
                        }
                    }
                    // Track the class of newly-allocated objects for InstanceOf
                    // and StringBuilder content.
                    Rvalue::New(cls) => {
                        let aid = alloc_id;
                        alloc_id += 1;
                        alloc_types.insert(aid, cls.clone());
                        // Pre-seed an empty string for StringBuilder/StringBuffer
                        // so that append() calls before any <init> see "".
                        if cls == "java/lang/StringBuilder" || cls == "java/lang/StringBuffer" {
                            sb_store.insert(aid, String::new());
                        }
                        Value::Ref(aid)
                    }
                    // Track array lengths at creation so ArrayLength can be
                    // evaluated concretely.
                    Rvalue::NewArray { len, .. } => {
                        let r = Run { store };
                        let len_val = r.eval(len);
                        store = r.store;
                        let aid = alloc_id;
                        alloc_id += 1;
                        if let Value::I32(n) = len_val {
                            array_lengths.insert(aid, n as i64);
                        }
                        Value::Ref(aid)
                    }
                    // Evaluate InstanceOf using the type hierarchy.
                    // Keying by alloc_id means aliases (v2 = v1) resolve correctly.
                    // Only trust is_subtype when the known class appears in the
                    // loaded hierarchy (prog.supers). JDK types not in the classpath
                    // are absent from prog.supers; for those we return Unknown rather
                    // than relying on is_subtype's open-world default of `true`.
                    Rvalue::InstanceOf { obj, class } => {
                        let r = Run { store };
                        let obj_val = r.eval(obj);
                        store = r.store;
                        match obj_val {
                            Value::Ref(0) => Value::I32(0), // null instanceof T = false
                            Value::Ref(aid) => match alloc_types.get(&aid) {
                                Some(known) if prog.supers.contains_key(known.as_str()) => {
                                    Value::I32(prog.is_subtype(known, class) as i32)
                                }
                                Some(_) => {
                                    // Class not in the loaded hierarchy (e.g. a JDK type):
                                    // return false (not a subtype). Under-approximation is
                                    // safe here — JvmReplay filters any spurious witness.
                                    Value::I32(0)
                                }
                                None => Value::Unknown,
                            },
                            _ => Value::Unknown,
                        }
                    }
                    // Resolve array length from creation-time tracking.
                    // Look up by alloc_id so aliased array references work.
                    Rvalue::ArrayLength(arr) => {
                        let aid = match arr {
                            Operand::Var(vid) => match store.get(vid) {
                                Some(Value::Ref(aid)) => Some(*aid),
                                _ => None,
                            },
                            _ => None,
                        };
                        match aid.and_then(|a| array_lengths.get(&a)) {
                            Some(&len) => Value::I32(len as i32),
                            None => Value::Unknown,
                        }
                    }
                    // String/StringBuilder method calls kept as Rvalue::Call
                    // by the lifter. Evaluate them against the tracked content.
                    Rvalue::Call { target, args, .. }
                        if models::STR_OWNERS.contains(&target.class.as_str()) =>
                    {
                        eval_str_call(
                            target,
                            args,
                            &store,
                            &mut str_store,
                            &mut sb_store,
                            &mut alloc_id,
                        )
                    }
                    other => {
                        let mut r = Run { store };
                        let val = r.eval_rvalue(other);
                        store = r.store;
                        val
                    }
                };
                store.insert(*v, val);
            }
            Stmt::Assume(op) => {
                let v = store
                    .get(match op {
                        Operand::Var(v) => v,
                        _ => unreachable!("assume operand is always a temp"),
                    })
                    .copied()
                    .unwrap_or(Value::Unknown);
                if !v.nonzero() {
                    return Outcome::Halted;
                }
            }
            Stmt::PutStatic(..) | Stmt::PutField { .. } | Stmt::ArrayStore { .. } => {}
            Stmt::Check(oid) => {
                let ob = body.obligation(*oid);
                let ok = match &ob.cond {
                    Operand::Const(Const::Int(v)) => *v != 0,
                    other => {
                        let v = match other {
                            Operand::Var(vid) => store.get(vid).copied().unwrap_or(Value::Unknown),
                            _ => Value::Unknown,
                        };
                        if v == Value::Unknown {
                            return Outcome::Inconclusive;
                        }
                        v.nonzero()
                    }
                };
                if !ok {
                    if let Some(class) = models::exception_class(ob.kind) {
                        if let Some(target) = route(prog, b, class) {
                            block = target;
                            idx = 0;
                            // Materialise the exception object in stack slot 0.
                            if let Some(slot) = body
                                .vars
                                .iter()
                                .enumerate()
                                .find(|(_, vi)| vi.kind == VarKind::Stack(0))
                                .map(|(i, _)| VarId(i as u32))
                            {
                                let aid = alloc_id;
                                alloc_id += 1;
                                store.insert(slot, Value::Ref(aid));
                            }
                            continue;
                        }
                    }
                    return Outcome::Violated {
                        oid: *oid,
                        witness: trace,
                    };
                }
            }
            Stmt::Nop => {}
        }
        idx += 1;
    }
}

/// Collect every integer constant that appears as an operand anywhere in the
/// body. These are the values most likely to be semantically relevant at
/// branch decisions, so adding them (and their immediate neighbours ±1) to
/// the candidate pool gives boundary-value coverage without a solver.
fn extract_constants(body: &Body) -> Vec<i32> {
    use std::collections::BTreeSet;
    let mut seen: BTreeSet<i32> = BTreeSet::new();
    let scan_op = |op: &Operand, s: &mut BTreeSet<i32>| {
        if let Operand::Const(Const::Int(v)) = op {
            s.insert(*v);
            s.insert(v.saturating_add(1));
            s.insert(v.saturating_sub(1));
        }
    };
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(_, rv) = stmt {
                match rv {
                    Rvalue::Use(o) | Rvalue::Neg(o) | Rvalue::ArrayLength(o) => {
                        scan_op(o, &mut seen)
                    }
                    Rvalue::Bin(_, a, b) => {
                        scan_op(a, &mut seen);
                        scan_op(b, &mut seen);
                    }
                    Rvalue::Cast(_, o) => scan_op(o, &mut seen),
                    Rvalue::Cmp(a, b) => {
                        scan_op(a, &mut seen);
                        scan_op(b, &mut seen);
                    }
                    Rvalue::NewArray { len, .. } => scan_op(len, &mut seen),
                    _ => {}
                }
            }
        }
        match &block.term {
            Terminator::Branch { cond, .. } => scan_op(cond, &mut seen),
            Terminator::Switch { value, .. } => scan_op(value, &mut seen),
            _ => {}
        }
    }
    seen.into_iter().collect()
}

fn search(prog: &Program, body: &Body, budget: u64) -> Vec<(ObligationId, Witness)> {
    let mut found = Vec::new();
    let mut runs_left = budget;

    let probe_steps = 200_000u64;
    let mut probe_choices: Vec<i64> = Vec::new();
    let slots = count_nondet_slots(prog, body, probe_steps, &mut probe_choices);

    if slots == 0 {
        if let Outcome::Violated { oid, witness } = run_with_choices(prog, body, &[], probe_steps) {
            found.push((
                oid,
                Witness {
                    nondet_sequence: witness,
                },
            ));
        }
        return found;
    }

    let capped = slots.min(4);
    let mut pool_set: std::collections::BTreeSet<i64> =
        INT_CANDIDATES.iter().map(|x| *x as i64).collect();
    for c in extract_constants(body) {
        pool_set.insert(c as i64);
    }
    // When the body has string-nondet slots, add the full range of
    // STRING_CANDIDATES indices (0..len-1) so every candidate string
    // is tried. These are small integers and won't inflate the pool much.
    let has_str_nondet = body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .any(|s| matches!(s, Stmt::Assign(_, Rvalue::Nondet(Ty::Str))));
    if has_str_nondet {
        for i in 0..STRING_CANDIDATES.len() as i64 {
            pool_set.insert(i);
        }
    }
    let pool: Vec<i64> = pool_set.into_iter().collect();
    let mut idxs = vec![0usize; capped];

    'outer: loop {
        if runs_left == 0 {
            break;
        }
        runs_left -= 1;

        let choices: Vec<i64> = idxs.iter().map(|i| pool[*i]).collect();
        if let Outcome::Violated { oid, witness } =
            run_with_choices(prog, body, &choices, probe_steps)
        {
            found.push((
                oid,
                Witness {
                    nondet_sequence: witness,
                },
            ));
        }

        let mut k = capped;
        loop {
            if k == 0 {
                break 'outer;
            }
            k -= 1;
            idxs[k] += 1;
            if idxs[k] < pool.len() {
                break;
            }
            idxs[k] = 0;
        }
    }

    found
}

/// Run once with all-zero choices to count how many nondet slots appear on
/// the taken path. Falls back to a static upper-bound count when the probe
/// finds no violation (so the slot count is not in the witness).
fn count_nondet_slots(prog: &Program, body: &Body, steps: u64, out: &mut Vec<i64>) -> usize {
    match run_with_choices(prog, body, &[], steps) {
        Outcome::Violated { witness, .. } => {
            let len = witness.len();
            *out = witness;
            len
        }
        _ => {
            // Static upper bound: count Nondet rvalues across all blocks.
            // Over-counting is fine — it just means a few extra odometer
            // positions that the interpreter reads as the default 0.
            let static_count: usize = body
                .blocks
                .iter()
                .flat_map(|b| &b.stmts)
                .filter(|s| matches!(s, Stmt::Assign(_, Rvalue::Nondet(_))))
                .count();
            static_count.max(3)
        }
    }
}

pub struct Concrete {
    done: bool,
    budget_runs: u64,
}

impl Concrete {
    pub fn new(budget_runs: u64) -> Self {
        Concrete {
            done: false,
            budget_runs,
        }
    }
}

impl Engine for Concrete {
    fn id(&self) -> EngineId {
        EngineId("concrete")
    }

    fn direction(&self) -> Direction {
        Direction::Under
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done {
            return Progress::Exhausted;
        }
        self.done = true;

        let Some(entry) = &prog.entry else {
            return Progress::Exhausted;
        };
        let Some(body) = prog.body(entry) else {
            return Progress::Exhausted;
        };

        info!(
            "concrete: starting bounded search (budget={} runs) on {entry:?}",
            self.budget_runs
        );
        let violations = search(prog, body, self.budget_runs);
        debug!(
            "concrete: search complete, found {} violation(s)",
            violations.len()
        );

        let mut advanced = false;
        for (oid, witness) in violations {
            let oref = ObligationRef {
                method: entry.clone(),
                id: oid,
            };
            debug!(
                "concrete: publishing violation at {oref:?}, witness={:?}",
                witness.nondet_sequence
            );
            let published = bb.publish(
                self.id(),
                self.direction(),
                Artifact::Status(
                    oref,
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

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}
