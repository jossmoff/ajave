//! Concrete string/StringBuilder/StringBuffer method evaluation.
//!
//! Extracted from `concrete.rs` for modularity. Evaluates String and
//! StringBuilder method calls against tracked string content.

use std::collections::HashMap;

use ajave_ir::*;

use crate::concrete::Value;

/// Look up the string content for an operand, consulting both the string store
/// (for String values) and the StringBuilder store.
fn get_str_content(
    op: &Operand,
    store: &HashMap<VarId, Value>,
    str_store: &HashMap<u64, String>,
    sb_store: &HashMap<u64, String>,
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
pub(crate) fn eval_str_call(
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
                let is_bool = target.desc.starts_with("(Z)");
                let is_char = target.desc.starts_with("(C)");
                let to_append: Option<String> = if let Some(arg) = args.get(1) {
                    match str_of!(arg) {
                        Some(s) => Some(s),
                        None => match arg {
                            Operand::Var(vid) => match store.get(vid).copied() {
                                Some(Value::I32(n)) if is_bool => {
                                    Some(if n != 0 { "true".into() } else { "false".into() })
                                }
                                Some(Value::I32(n)) if is_char => {
                                    Some(String::from(char::from_u32(n as u32).unwrap_or('?')))
                                }
                                Some(Value::I32(n)) => Some(n.to_string()),
                                Some(Value::I64(n)) => Some(n.to_string()),
                                _ => None,
                            },
                            Operand::Const(Const::Int(n)) => {
                                if is_bool {
                                    Some(if *n != 0 { "true".into() } else { "false".into() })
                                } else if is_char {
                                    Some(String::from(char::from_u32(*n as u32).unwrap_or('?')))
                                } else {
                                    Some(n.to_string())
                                }
                            }
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
            let is_bool = target.desc.starts_with("(Z)");
            let is_char = target.desc.starts_with("(C)");
            let result = match args.first() {
                Some(Operand::Var(vid)) => match store.get(vid).copied() {
                    Some(Value::I32(n)) if is_bool => {
                        Some(if n != 0 { "true".to_string() } else { "false".to_string() })
                    }
                    Some(Value::I32(n)) if is_char => {
                        Some(String::from(char::from_u32(n as u32).unwrap_or('?')))
                    }
                    Some(Value::I32(n)) => Some(n.to_string()),
                    Some(Value::I64(n)) => Some(n.to_string()),
                    Some(Value::Ref(aid)) => str_store.get(&aid).cloned(),
                    _ => None,
                },
                Some(Operand::Const(Const::Int(n))) => {
                    if is_bool {
                        Some(if *n != 0 { "true".to_string() } else { "false".to_string() })
                    } else if is_char {
                        Some(String::from(char::from_u32(*n as u32).unwrap_or('?')))
                    } else {
                        Some(n.to_string())
                    }
                }
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
