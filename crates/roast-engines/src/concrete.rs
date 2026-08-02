//! Concrete interpreter: runs the program once with default (all-zero) nondet
//! values. This catches trivial bugs quickly without a solver. Value search
//! (finding the right nondet inputs to trigger a violation) is delegated to
//! the SMT BMC engine.
//!
//! String tracking: `nondetString()` produces a `Nondet(Ty::Str)` rvalue in
//! the IR. The engine defaults to the empty string, allocates a fresh
//! reference ID, and records the content in `str_store`. String method calls
//! remain in the IR as `Rvalue::Call` (via `CallModel::StrCall`) so this
//! interpreter can evaluate them against the tracked content instead of
//! returning Unknown.

use std::collections::{HashMap, HashSet};

use log::{debug, info};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_ir::verdict::{NondetEntry, NondetValue, Witness};
use roast_ir::*;
use roast_models as models;

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

/// Outcome of running one concrete path to completion.
enum Outcome {
    /// Ran to a `Return` with nothing amiss.
    Clean,
    /// Ran to a `Return` carrying a value.
    ReturnedValue(Value),
    /// `Verifier.assume` failed: this path is uninteresting, not unsafe.
    Halted,
    /// A `Check` failed with nothing able to catch it.
    Violated {
        method: MethodKey,
        oid: ObligationId,
        witness: Vec<i64>,
        entries: Vec<NondetEntry>,
    },
    /// Ran out of budget or hit something we can't interpret.
    Inconclusive,
}

/// Result of inlining a method call.
enum InlineResult {
    Returned(Value),
    Halted,
    Violated {
        method: MethodKey,
        oid: ObligationId,
        witness: Vec<i64>,
        entries: Vec<NondetEntry>,
    },
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

/// Shared mutable state for a concrete execution — threaded through call
/// inlining so field reads/writes and allocations are visible across frames.
struct ConcreteState<'a> {
    prog: &'a Program,
    choices: &'a [i64],
    choice_idx: usize,
    trace: Vec<i64>,
    entries: Vec<NondetEntry>,
    steps: u64,
    alloc_id: u64,
    alloc_types: HashMap<u64, String>,
    array_lengths: HashMap<u64, i64>,
    str_store: HashMap<u64, String>,
    sb_store: HashMap<u64, String>,
    /// Instance fields: (alloc_id, field_name) -> Value.
    inst_fields: HashMap<(u64, String), Value>,
    /// Static fields: (class, field_name) -> Value.
    static_fields: HashMap<(String, String), Value>,
    /// Current call depth for bounding inlining.
    call_depth: u32,
    /// Classes whose `<clinit>` has already been executed.
    initialized_classes: HashSet<String>,
}

/// Maximum call inlining depth to prevent infinite recursion.
const MAX_CALL_DEPTH: u32 = 20;

impl<'a> ConcreteState<'a> {
    fn new(prog: &'a Program, choices: &'a [i64], step_budget: u64) -> Self {
        ConcreteState {
            prog,
            choices,
            choice_idx: 0,
            trace: Vec::new(),
            entries: Vec::new(),
            steps: step_budget,
            alloc_id: 2,
            alloc_types: HashMap::new(),
            array_lengths: HashMap::new(),
            str_store: HashMap::new(),
            sb_store: HashMap::new(),
            inst_fields: HashMap::new(),
            static_fields: HashMap::new(),
            call_depth: 0,
            initialized_classes: HashSet::new(),
        }
    }

    fn eval_op(&self, op: &Operand, store: &HashMap<VarId, Value>) -> Value {
        match op {
            Operand::Var(v) => store.get(v).copied().unwrap_or(Value::Unknown),
            Operand::Const(Const::Int(n)) => Value::I32(*n),
            Operand::Const(Const::Long(n)) => Value::I64(*n),
            Operand::Const(Const::Null) => Value::Ref(0),
            Operand::Const(_) => Value::Ref(1),
        }
    }

    /// Run `<clinit>` for `class` if it hasn't been run yet. This initialises
    /// static fields (enum constants, $assertionsDisabled, etc.) so that
    /// subsequent `GetStatic` reads return concrete values rather than Unknown.
    fn ensure_clinit(&mut self, class: &str) {
        if self.initialized_classes.contains(class) {
            return;
        }
        // Mark as initialized *before* running to prevent infinite recursion
        // (a <clinit> may reference its own class's statics).
        self.initialized_classes.insert(class.to_string());

        let clinit_key = MethodKey {
            class: class.to_string(),
            name: "<clinit>".to_string(),
            desc: "()V".to_string(),
        };
        if let Some(body) = self.prog.body(&clinit_key) {
            let body = body.clone();
            self.call_depth += 1;
            let _ = self.run_body(&body, HashMap::new());
            self.call_depth -= 1;
        }
    }

    /// Try to inline a user method call. Returns Some(return_value) on success.
    fn try_inline_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
        caller_store: &HashMap<VarId, Value>,
    ) -> Option<InlineResult> {
        if self.call_depth >= MAX_CALL_DEPTH {
            return None;
        }
        let body = self.prog.body(target)?;

        // Build callee's local store by mapping args to local slots.
        let mut callee_store: HashMap<VarId, Value> = HashMap::new();
        let mut slot = 0u16;
        for arg in args {
            let val = self.eval_op(arg, caller_store);
            if let Some((vid_idx, vinfo)) = body
                .vars
                .iter()
                .enumerate()
                .find(|(_, vi)| matches!(vi.kind, VarKind::Local(s) if s == slot))
            {
                callee_store.insert(VarId(vid_idx as u32), val);
                slot += if vinfo.ty.is_wide() { 2 } else { 1 };
            } else {
                slot += 1;
            }
        }

        self.call_depth += 1;
        let result = self.run_body(body, callee_store);
        self.call_depth -= 1;
        match result {
            Outcome::Clean => Some(InlineResult::Returned(Value::Unknown)),
            Outcome::ReturnedValue(v) => Some(InlineResult::Returned(v)),
            Outcome::Halted => Some(InlineResult::Halted),
            Outcome::Violated {
                method,
                oid,
                witness,
                entries,
            } => Some(InlineResult::Violated {
                method,
                oid,
                witness,
                entries,
            }),
            Outcome::Inconclusive => None,
        }
    }

    /// Execute a body to completion. The `store` is the callee's local variable
    /// map; heap state is shared through `self`.
    fn run_body(&mut self, body: &Body, mut store: HashMap<VarId, Value>) -> Outcome {
        let mut block = body.entry;
        let mut idx = 0usize;

        loop {
            if self.steps == 0 {
                return Outcome::Inconclusive;
            }
            self.steps -= 1;

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
                            Operand::Var(vid) => {
                                store.get(vid).copied().unwrap_or(Value::Unknown)
                            }
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
                    Terminator::Return(ret) => {
                        if let Some(op) = ret {
                            let v = self.eval_op(op, &store);
                            return Outcome::ReturnedValue(v);
                        }
                        return Outcome::Clean;
                    }
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
                            let raw =
                                self.choices.get(self.choice_idx).copied().unwrap_or(0);
                            self.choice_idx += 1;
                            let line: Option<u16> = None;
                            match ty {
                                Ty::Str => {
                                    self.trace.push(raw);
                                    let chosen = String::new();
                                    self.entries.push(NondetEntry {
                                        value: NondetValue::Str(chosen.clone()),
                                        nondet_method: "nondetString",
                                        line,
                                    });
                                    let aid = self.alloc_id;
                                    self.alloc_id += 1;
                                    self.str_store.insert(aid, chosen);
                                    Value::Ref(aid)
                                }
                                Ty::Ref => {
                                    let aid = self.alloc_id;
                                    self.alloc_id += 1;
                                    Value::Ref(aid)
                                }
                                Ty::Long => {
                                    self.trace.push(raw);
                                    self.entries.push(NondetEntry {
                                        value: NondetValue::Long(raw),
                                        nondet_method: "nondetLong",
                                        line,
                                    });
                                    Value::I64(raw)
                                }
                                _ => {
                                    self.trace.push(raw);
                                    self.entries.push(NondetEntry {
                                        value: NondetValue::Int(raw as i32),
                                        nondet_method: "nondetInt",
                                        line,
                                    });
                                    Value::I32(raw as i32)
                                }
                            }
                        }
                        Rvalue::New(cls) => {
                            let aid = self.alloc_id;
                            self.alloc_id += 1;
                            self.alloc_types.insert(aid, cls.clone());
                            if cls == "java/lang/StringBuilder"
                                || cls == "java/lang/StringBuffer"
                            {
                                self.sb_store.insert(aid, String::new());
                            }
                            Value::Ref(aid)
                        }
                        Rvalue::NewArray { len, .. } => {
                            let len_val = self.eval_op(len, &store);
                            let aid = self.alloc_id;
                            self.alloc_id += 1;
                            if let Value::I32(n) = len_val {
                                self.array_lengths.insert(aid, n as i64);
                            }
                            Value::Ref(aid)
                        }
                        Rvalue::InstanceOf { obj, class } => {
                            let obj_val = self.eval_op(obj, &store);
                            match obj_val {
                                Value::Ref(0) => Value::I32(0),
                                Value::Ref(aid) => match self.alloc_types.get(&aid) {
                                    Some(known)
                                        if self
                                            .prog
                                            .supers
                                            .contains_key(known.as_str()) =>
                                    {
                                        Value::I32(
                                            self.prog.is_subtype(known, class) as i32,
                                        )
                                    }
                                    Some(_) => Value::I32(0),
                                    None => Value::Unknown,
                                },
                                _ => Value::Unknown,
                            }
                        }
                        Rvalue::ArrayLength(arr) => {
                            let aid = match arr {
                                Operand::Var(vid) => match store.get(vid) {
                                    Some(Value::Ref(aid)) => Some(*aid),
                                    _ => None,
                                },
                                _ => None,
                            };
                            match aid.and_then(|a| self.array_lengths.get(&a)) {
                                Some(&len) => Value::I32(len as i32),
                                None => Value::Unknown,
                            }
                        }
                        Rvalue::Call { target, args, .. }
                            if models::STR_OWNERS.contains(&target.class.as_str()) =>
                        {
                            eval_str_call(
                                target,
                                args,
                                &store,
                                &mut self.str_store,
                                &mut self.sb_store,
                                &mut self.alloc_id,
                            )
                        }
                        // Inline user method calls when a body is available.
                        Rvalue::Call { target, args, .. } => {
                            match self.try_inline_call(target, args, &store) {
                                Some(InlineResult::Returned(rv)) => rv,
                                Some(InlineResult::Halted) => return Outcome::Halted,
                                Some(InlineResult::Violated {
                                    method,
                                    oid,
                                    witness,
                                    entries,
                                }) => {
                                    return Outcome::Violated {
                                        method,
                                        oid,
                                        witness,
                                        entries,
                                    }
                                }
                                None => {
                                    let mut r = Run { store };
                                    let val = r.eval_rvalue(rv);
                                    store = r.store;
                                    val
                                }
                            }
                        }
                        // Read instance field from heap.
                        Rvalue::GetField { obj, field } => {
                            let obj_val = self.eval_op(obj, &store);
                            match obj_val {
                                Value::Ref(aid) if aid != 0 => self
                                    .inst_fields
                                    .get(&(aid, field.name.clone()))
                                    .copied()
                                    .unwrap_or(Value::Unknown),
                                _ => Value::Unknown,
                            }
                        }
                        // Read static field.
                        Rvalue::GetStatic(fk) => {
                            // javac's $assertionsDisabled field: assume
                            // assertions are enabled (SV-COMP convention).
                            if fk.name == "$assertionsDisabled" {
                                Value::I32(0)
                            } else {
                                // Ensure <clinit> has run for this class.
                                self.ensure_clinit(&fk.class);
                                self.static_fields
                                    .get(&(fk.class.clone(), fk.name.clone()))
                                    .copied()
                                    .unwrap_or(Value::Unknown)
                            }
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
                // Write instance field to heap.
                Stmt::PutField { obj, field, val } => {
                    let obj_val = self.eval_op(obj, &store);
                    let v = self.eval_op(val, &store);
                    if let Value::Ref(aid) = obj_val {
                        if aid != 0 {
                            self.inst_fields.insert((aid, field.name.clone()), v);
                        }
                    }
                }
                // Write static field.
                Stmt::PutStatic(fk, val) => {
                    let v = self.eval_op(val, &store);
                    self.static_fields
                        .insert((fk.class.clone(), fk.name.clone()), v);
                }
                Stmt::ArrayStore { .. } => {}
                Stmt::Check(oid) => {
                    let ob = body.obligation(*oid);
                    let ok = match &ob.cond {
                        Operand::Const(Const::Int(v)) => *v != 0,
                        other => {
                            let v = match other {
                                Operand::Var(vid) => {
                                    store.get(vid).copied().unwrap_or(Value::Unknown)
                                }
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
                            if let Some(target) = route(self.prog, b, class) {
                                block = target;
                                idx = 0;
                                if let Some(slot) = body
                                    .vars
                                    .iter()
                                    .enumerate()
                                    .find(|(_, vi)| vi.kind == VarKind::Stack(0))
                                    .map(|(i, _)| VarId(i as u32))
                                {
                                    let aid = self.alloc_id;
                                    self.alloc_id += 1;
                                    store.insert(slot, Value::Ref(aid));
                                }
                                continue;
                            }
                        }
                        return Outcome::Violated {
                            method: body.key.clone(),
                            oid: *oid,
                            witness: std::mem::take(&mut self.trace),
                            entries: std::mem::take(&mut self.entries),
                        };
                    }
                }
                Stmt::Nop => {}
            }
            idx += 1;
        }
    }
}

/// Run the body once against a fully-predetermined sequence of nondet
/// choices. Choices beyond what's provided fall back to `0`.
fn run_with_choices(prog: &Program, body: &Body, choices: &[i64], step_budget: u64) -> Outcome {
    let mut state = ConcreteState::new(prog, choices, step_budget);
    state.run_body(body, HashMap::new())
}

/// Try multiple choice vectors: all-zero plus a set of boolean-biased
/// patterns. Enough to trigger bugs in programs like MinePump where
/// specific nondet boolean combinations reach assertion failures.
fn search(prog: &Program, body: &Body) -> Vec<(MethodKey, ObligationId, Witness)> {
    let step_budget = 200_000u64;
    let mut found = Vec::new();

    // Choice vectors to try. Each entry is used as a repeating pattern
    // for nondet values (0 = false for booleans, 1 = true).
    let patterns: &[&[i64]] = &[
        &[],                    // all-zero default
        &[1],                   // all-one (all booleans true)
        &[1, 0],               // alternating true/false
        &[0, 1],               // alternating false/true
        &[1, 1, 0],            // mostly true
        &[1, 0, 0],            // mostly false
        &[0, 0, 1],            // occasional true
        &[1, 1, 1, 0],         // three true, one false
        &[0, 1, 1, 0],         // false-true-true-false
        &[1, 0, 1, 0],         // alternating
        &[0, 0, 0, 1],         // mostly false
        &[1, 1, 0, 0],         // half and half
    ];

    for pattern in patterns {
        // Expand pattern to cover enough choices (up to 64 nondet calls).
        let choices: Vec<i64> = if pattern.is_empty() {
            vec![]
        } else {
            pattern.iter().copied().cycle().take(64).collect()
        };
        if let Outcome::Violated {
            method,
            oid,
            witness,
            entries,
        } = run_with_choices(prog, body, &choices, step_budget)
        {
            found.push((
                method,
                oid,
                Witness {
                    nondet_sequence: witness,
                    entries,
                },
            ));
            break; // One violation is enough
        }
    }
    found
}

pub struct Concrete {
    done: bool,
}

impl Concrete {
    pub fn new() -> Self {
        Concrete { done: false }
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

        info!("concrete: probing with default values on {entry:?}");
        let violations = search(prog, body);
        debug!(
            "concrete: search complete, found {} violation(s)",
            violations.len()
        );

        let mut advanced = false;
        for (method, oid, witness) in violations {
            let oref = ObligationRef {
                method,
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
