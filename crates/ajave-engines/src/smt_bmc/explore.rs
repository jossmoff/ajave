//! Block exploration: statement handling, terminator dispatch, branching, inlining.

use std::collections::HashSet;

use log::debug;
use ajave_core::smt::{SatResult, Term};
use ajave_ir::*;
use ajave_models;

use super::{ExploreCtx, SavedState, MAX_CALL_DEPTH, MAX_LOOP_UNROLL};

/// Whether a havoced method call could throw a RuntimeException.
/// Conservative: returns true for any call to a class whose methods are known
/// to throw checked or unchecked exceptions (String, parse methods, etc.).
/// Safe methods (Verifier, System.out, pure getters) return false.
/// Returns true if a modelled string call (StrCall) could throw a RuntimeException
/// (e.g. StringIndexOutOfBoundsException, NumberFormatException).
/// These calls are resolved by encode_str_call but their exception behavior
/// isn't modelled, so NRE discharge must be blocked.
fn str_call_can_throw(target: &MethodKey) -> bool {
    let name = target.name.as_str();
    matches!(name,
        "charAt" | "substring" | "codePointAt" | "codePointBefore"
        | "setCharAt" | "deleteCharAt" | "delete" | "insert"
        | "getChars" | "subSequence"
    )
}

/// Does a call to `target` risk throwing a `RuntimeException`?
///
/// Answering `false` is a **soundness commitment**: the BMC uses it to decide
/// that a havoced call cannot raise, which lets it claim `all_paths_complete`
/// and discharge NRE obligations as TRUE. A wrong `false` is therefore a wrong
/// TRUE (-16), not a precision loss.
///
/// Consequently every entry below is keyed on the full `(class, name, desc)`
/// signature and must be justified by the method's *contract*, not by observed
/// behaviour on any particular program. Three rules, learned from the audit in
/// issue #48 which found 22 wrongly-allowlisted methods:
///
/// 1. **Never allowlist a whole class.** `Math`, `Arrays` and `Collections`
///    each look total but contain throwing members (`addExact`, `copyOfRange`,
///    `max` on an empty collection).
/// 2. **Never ignore the descriptor.** `Integer.valueOf(int)` is total;
///    `Integer.valueOf(String)` throws `NumberFormatException`.
/// 3. **Never allowlist a partial function.** `List.get`, `Iterator.next` and
///    `Stack.pop` throw on out-of-range or empty receivers — that *is* their
///    specified contract.
///
/// A method absent from this list is treated as possibly-throwing, which costs
/// precision only. When in doubt, leave it out.
pub(crate) fn could_throw_runtime_exception(target: &MethodKey) -> bool {
    !is_total_jdk_method(target.class.as_str(), target.name.as_str(), target.desc.as_str())
}

/// `true` when the given signature cannot raise a `RuntimeException` for any
/// input, per its JDK contract.
pub(crate) fn is_total_jdk_method(class: &str, name: &str, desc: &str) -> bool {
    // Prefer the contract table: it is the single declaration of what an
    // external method does, and totality is just "no preconditions". The
    // hand-written arms below are the remainder not yet migrated.
    if let Some(c) = ajave_models::contract_of(class, name, desc) {
        return c.is_total();
    }

    // The SV-COMP nondet source. Exact match: a substring test would also
    // accept a user class such as `MyVerifierHelper`.
    if class == "org/sosy_lab/sv_benchmarks/Verifier" {
        return true;
    }

    match class {
        // `Object`'s own implementations are total. (Overrides are not: a
        // subclass `equals`/`toString` can throw, but those have bodies we
        // inline, so they never reach this check as havoced calls.)
        "java/lang/Object" => matches!(
            (name, desc),
            ("<init>", "()V")
                | ("getClass", "()Ljava/lang/Class;")
                | ("hashCode", "()I")
                | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
        ),

        // Only the no-argument queries. Anything taking a `String`/`CharSequence`
        // throws NPE on null (`concat`, `contains`, `startsWith`, `replace`),
        // anything taking an index throws (`charAt`, `substring`), the regex
        // methods throw `PatternSyntaxException`, and `format` throws
        // `IllegalFormatException`.
        "java/lang/String" => matches!(
            (name, desc),
            ("length", "()I")
                | ("isEmpty", "()Z")
                | ("hashCode", "()I")
                | ("toString", "()Ljava/lang/String;")
                | ("intern", "()Ljava/lang/String;")
                | ("trim", "()Ljava/lang/String;")
                | ("toCharArray", "()[C")
                | ("toUpperCase", "()Ljava/lang/String;")
                | ("toLowerCase", "()Ljava/lang/String;")
                // `equals` is null-tolerant by contract (returns false).
                | ("equals", "(Ljava/lang/Object;)Z")
        ),

        // Unboxing accessors are total. `valueOf` only for the *primitive*
        // overloads — the `String` ones throw `NumberFormatException`.
        "java/lang/Integer" => matches!(
            (name, desc),
            ("intValue", "()I") | ("longValue", "()J") | ("doubleValue", "()D")
                | ("floatValue", "()F") | ("shortValue", "()S") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(I)Ljava/lang/Integer;")
                | ("toString", "(I)Ljava/lang/String;")
                | ("compare", "(II)I")
        ),
        "java/lang/Long" => matches!(
            (name, desc),
            ("intValue", "()I") | ("longValue", "()J") | ("doubleValue", "()D")
                | ("floatValue", "()F") | ("shortValue", "()S") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(J)Ljava/lang/Long;")
                | ("toString", "(J)Ljava/lang/String;")
                | ("compare", "(JJ)I")
        ),
        "java/lang/Short" => matches!(
            (name, desc),
            ("shortValue", "()S") | ("intValue", "()I") | ("longValue", "()J")
                | ("doubleValue", "()D") | ("floatValue", "()F") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(S)Ljava/lang/Short;")
        ),
        "java/lang/Byte" => matches!(
            (name, desc),
            ("byteValue", "()B") | ("intValue", "()I") | ("longValue", "()J")
                | ("doubleValue", "()D") | ("floatValue", "()F") | ("shortValue", "()S")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(B)Ljava/lang/Byte;")
        ),
        // Float/Double parsing throws; the accessors and primitive boxing do not.
        "java/lang/Float" => matches!(
            (name, desc),
            ("floatValue", "()F") | ("doubleValue", "()D") | ("intValue", "()I")
                | ("longValue", "()J") | ("shortValue", "()S") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(F)Ljava/lang/Float;")
                | ("isNaN", "(F)Z") | ("isInfinite", "(F)Z")
        ),
        "java/lang/Double" => matches!(
            (name, desc),
            ("doubleValue", "()D") | ("floatValue", "()F") | ("intValue", "()I")
                | ("longValue", "()J") | ("shortValue", "()S") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(D)Ljava/lang/Double;")
                | ("isNaN", "(D)Z") | ("isInfinite", "(D)Z")
        ),
        // `parseBoolean`/`valueOf(String)` are null-tolerant by contract here:
        // they return false rather than throwing.
        "java/lang/Boolean" => matches!(
            (name, desc),
            ("booleanValue", "()Z") | ("hashCode", "()I")
                | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(Z)Ljava/lang/Boolean;")
                | ("parseBoolean", "(Ljava/lang/String;)Z")
        ),
        "java/lang/Character" => matches!(
            (name, desc),
            ("charValue", "()C") | ("hashCode", "()I")
                | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(C)Ljava/lang/Character;")
                // Classification predicates are total over the whole char range.
                | ("isDigit", "(C)Z") | ("isLetter", "(C)Z")
                | ("isLetterOrDigit", "(C)Z") | ("isWhitespace", "(C)Z")
                | ("isUpperCase", "(C)Z") | ("isLowerCase", "(C)Z")
                | ("isAlphabetic", "(I)Z") | ("isSpaceChar", "(C)Z")
                | ("toUpperCase", "(C)C") | ("toLowerCase", "(C)C")
        ),

        // Explicitly enumerated: the `*Exact` family throws `ArithmeticException`
        // on overflow, and `floorDiv`/`floorMod`/`ceilDiv` throw on a zero
        // divisor. The listed methods saturate to NaN/Infinity instead.
        "java/lang/Math" | "java/lang/StrictMath" => matches!(
            name,
            "abs" | "min" | "max" | "sqrt" | "cbrt" | "sin" | "cos" | "tan"
                | "asin" | "acos" | "atan" | "atan2" | "exp" | "expm1"
                | "log" | "log10" | "log1p" | "pow" | "floor" | "ceil"
                | "rint" | "round" | "signum" | "hypot" | "random"
                | "toRadians" | "toDegrees" | "ulp" | "nextUp" | "nextDown"
                | "nextAfter" | "copySign" | "IEEEremainder" | "sinh" | "cosh"
                | "tanh" | "fma" | "scalb" | "getExponent"
        ),

        // `arraycopy` throws `IndexOutOfBounds`/`ArrayStore`/NPE and `exit` can
        // raise `SecurityException`, so neither is listed.
        "java/lang/System" => matches!(
            (name, desc),
            ("currentTimeMillis", "()J") | ("nanoTime", "()J")
                | ("identityHashCode", "(Ljava/lang/Object;)I")
                | ("lineSeparator", "()Ljava/lang/String;")
        ),

        // The no-arg constructor and the primitive/String appends. The
        // capacity constructor throws `NegativeArraySizeException`, and the
        // `(char[], int, int)` append throws `IndexOutOfBoundsException`.
        "java/lang/StringBuilder" | "java/lang/StringBuffer" => {
            matches!((name, desc), ("<init>", "()V"))
                || matches!((name, desc),
                    ("length", "()I") | ("toString", "()Ljava/lang/String;"))
                || (name == "append"
                    && matches!(desc,
                        "(Ljava/lang/String;)Ljava/lang/StringBuilder;"
                        | "(Ljava/lang/String;)Ljava/lang/StringBuffer;"
                        | "(I)Ljava/lang/StringBuilder;" | "(I)Ljava/lang/StringBuffer;"
                        | "(J)Ljava/lang/StringBuilder;" | "(J)Ljava/lang/StringBuffer;"
                        | "(C)Ljava/lang/StringBuilder;" | "(C)Ljava/lang/StringBuffer;"
                        | "(Z)Ljava/lang/StringBuilder;" | "(Z)Ljava/lang/StringBuffer;"
                        | "(D)Ljava/lang/StringBuilder;" | "(D)Ljava/lang/StringBuffer;"
                        | "(F)Ljava/lang/StringBuilder;" | "(F)Ljava/lang/StringBuffer;"
                        | "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"
                        | "(Ljava/lang/Object;)Ljava/lang/StringBuffer;"))
        }

        // `print`/`println` swallow IOException and render null as "null".
        // `format`/`printf` throw `IllegalFormatException`, and `print(char[])`
        // throws NPE on a null array, so neither is listed.
        "java/io/PrintStream" | "java/io/PrintWriter" => {
            (matches!(name, "print" | "println")
                && matches!(desc,
                    "()V" | "(Ljava/lang/String;)V" | "(I)V" | "(J)V" | "(C)V"
                    | "(Z)V" | "(D)V" | "(F)V" | "(Ljava/lang/Object;)V"))
                || matches!((name, desc), ("flush", "()V"))
        }

        // `compareTo` can raise `ClassCastException` across enum types, so it
        // is excluded; the rest are total.
        "java/lang/Enum" => matches!(
            (name, desc),
            ("ordinal", "()I") | ("name", "()Ljava/lang/String;")
                | ("toString", "()Ljava/lang/String;") | ("hashCode", "()I")
                | ("equals", "(Ljava/lang/Object;)Z")
        ),

        // Only the total queries on hash-based collections. `get`, `next`,
        // `pop`, `peek` and the index-taking `add`/`remove` overloads are all
        // partial. Sorted collections are excluded entirely: `TreeMap`/`TreeSet`
        // throw NPE on a null key and `ClassCastException` on incomparable ones.
        "java/util/ArrayList" | "java/util/LinkedList" | "java/util/HashSet"
        | "java/util/HashMap" | "java/util/LinkedHashMap" | "java/util/LinkedHashSet" => {
            matches!((name, desc), ("<init>", "()V"))
                || matches!((name, desc), ("size", "()I") | ("isEmpty", "()Z") | ("clear", "()V"))
        }

        // `hasNext` is total; `next` throws `NoSuchElementException` when
        // exhausted and `remove` throws `IllegalStateException`.
        "java/util/Iterator" => matches!((name, desc), ("hasNext", "()Z")),

        _ => false,
    }
}

impl<'a> ExploreCtx<'a> {
    /// Set str_vars for `var_id` and all other vars that share the same SMT term.
    fn propagate_str_to_aliases(&mut self, var_id: VarId, str_term: Term) {
        self.str_vars.insert(var_id, str_term);
        if let Some(&recv_term) = self.vars.get(&var_id) {
            let aliases: Vec<VarId> = self.vars.iter()
                .filter(|(vid, &t)| **vid != var_id && t == recv_term)
                .map(|(vid, _)| *vid)
                .collect();
            for alias in aliases {
                self.str_vars.insert(alias, str_term);
            }
        }
    }

    /// Run <clinit> for a class if it hasn't been run yet and has a body.
    pub(super) fn ensure_clinit(&mut self, class: &str) {
        if self.clinit_done.contains(class) {
            return;
        }
        self.clinit_done.insert(class.to_string());
        let clinit_key = MethodKey {
            class: class.to_string(),
            name: "<clinit>".to_string(),
            desc: "()V".to_string(),
        };
        if let Some(clinit) = self.prog.body(&clinit_key) {
            if self.call_depth >= MAX_CALL_DEPTH || self.budget_exhausted() {
                // Skipping a static initialiser leaves its writes unmodelled.
                self.completeness.all_paths_complete = false;
                return;
            }
            debug!("smt-bmc: running <clinit> for {class}");
            let saved_body = self.body;
            let saved_vars = self.vars.clone();
            let saved_str_vars = self.str_vars.clone();
            let saved_tainted = self.tainted.clone();
            let saved_float_tainted = self.float_tainted.clone();
            let saved_path_tainted = self.path_tainted;
            let saved_pc_len = self.path_constraints.len();

            self.body = clinit;
            self.call_depth += 1;
            self.vars.clear();
            self.str_vars.clear();
            self.tainted.clear();
            self.float_tainted.clear();

            self.explore_block(clinit.entry, 0);

            self.call_depth -= 1;
            self.body = saved_body;
            self.vars = saved_vars;
            self.str_vars = saved_str_vars;
            self.tainted = saved_tainted;
            self.float_tainted = saved_float_tainted;
            self.path_tainted = saved_path_tainted;
            self.path_constraints.truncate(saved_pc_len);
        }
    }

    /// Try to inline a method call.
    pub(super) fn try_inline_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
        dest_var: VarId,
        is_virtual: bool,
    ) -> bool {
        if self.call_depth >= MAX_CALL_DEPTH || self.budget_exhausted() {
            if self.call_depth >= MAX_CALL_DEPTH {
                self.completeness.has_depth_limited_havoc = true;
            }
            return false;
        }

        let targets = if is_virtual {
            // If the receiver (args[0]) has a known concrete class from `new`,
            // restrict dispatch to only that type's implementation.
            let receiver_class = args.first()
                .and_then(|a| if let Operand::Var(v) = a { self.concrete_classes.get(v).cloned() } else { None });

            if let Some(recv_cls) = receiver_class {
                // Precise devirtualization: only consider the concrete type's method.
                let precise_key = MethodKey {
                    class: recv_cls.clone(),
                    name: target.name.clone(),
                    desc: target.desc.clone(),
                };
                if self.prog.body(&precise_key).is_some() {
                    vec![precise_key]
                } else {
                    // Walk up hierarchy to find the inherited method.
                    let mut cls = recv_cls;
                    let mut found = None;
                    while let Some(sup) = self.prog.supers.get(&cls) {
                        let key = MethodKey {
                            class: sup.clone(),
                            name: target.name.clone(),
                            desc: target.desc.clone(),
                        };
                        if self.prog.body(&key).is_some() {
                            found = Some(key);
                            break;
                        }
                        cls = sup.clone();
                    }
                    match found {
                        Some(k) => vec![k],
                        None => {
                            let t = self.prog.devirtualise(target);
                            if t.is_empty() { return false; }
                            t
                        }
                    }
                }
            } else {
                let t = self.prog.devirtualise(target);
                if t.is_empty() { return false; }
                t
            }
        } else {
            vec![target.clone()]
        };

        if targets.iter().any(|t| self.prog.body(t).is_none()) {
            return false;
        }

        let arg_terms: Vec<Term> = args.iter().map(|a| self.encode_operand(a)).collect();
        let arg_widths: Vec<u32> = args.iter().map(|a| self.width_of_operand(a)).collect();
        let arg_str_terms: Vec<Option<Term>> =
            args.iter().map(|a| self.encode_str_operand(a)).collect();
        let arg_tainted: Vec<bool> = args.iter().map(|a| self.operand_tainted(a)).collect();

        let mut ret_tainted = false;
        for resolved in &targets {
            if self.budget_exhausted() { break; }
            let callee = self.prog.body(resolved).unwrap();

            let saved_body = self.body;
            let saved_vars = self.vars.clone();
            let saved_str_vars = self.str_vars.clone();
            let saved_var_widths = self.var_widths.clone();
            let saved_tainted = self.tainted.clone();
            let saved_float_tainted = self.float_tainted.clone();
            let saved_path_tainted = self.path_tainted;
            let saved_pc_len = self.path_constraints.len();

            self.body = callee;
            self.call_depth += 1;
            self.vars.clear();
            self.str_vars.clear();
            self.var_widths.clear();
            self.tainted.clear();
            self.float_tainted.clear();

            let mut slot = 0u16;
            for (i, arg_t) in arg_terms.iter().enumerate() {
                if let Some((vid_idx, vinfo)) = callee
                    .vars.iter().enumerate()
                    .find(|(_, vi)| matches!(vi.kind, VarKind::Local(s) if s == slot))
                {
                    let vid = VarId(vid_idx as u32);
                    self.vars.insert(vid, *arg_t);
                    self.var_widths.insert(vid, arg_widths[i]);
                    if let Some(st) = arg_str_terms[i] {
                        self.str_vars.insert(vid, st);
                    }
                    if arg_tainted[i] {
                        self.tainted.insert(vid);
                    }
                    slot += if vinfo.ty.is_wide() { 2 } else { 1 };
                } else {
                    slot += 1;
                }
            }

            self.inline_return = None;
            self.inline_return_str = None;
            self.inline_return_tainted = false;
            self.inline_throw = None;
            self.explore_block(callee.entry, 0);

            let callee_threw = self.inline_throw.take();
            let callee_return_tainted = self.inline_return_tainted;
            let callee_path_tainted = self.path_tainted;

            self.call_depth -= 1;
            self.body = saved_body;
            self.vars = saved_vars;
            self.str_vars = saved_str_vars;
            self.var_widths = saved_var_widths.clone();
            self.tainted = saved_tainted;
            self.float_tainted = saved_float_tainted;
            self.path_tainted = saved_path_tainted || callee_path_tainted;
            self.path_constraints.truncate(saved_pc_len);

            // If the callee threw an unhandled exception, propagate it.
            // Set inline_throw so the caller's explore_block_until dispatches it.
            if let Some(thrown) = callee_threw {
                self.inline_throw = Some(thrown);
                for resolved in &targets {
                    self.inlined_methods.insert(resolved.clone());
                }
                return true;
            }

            ret_tainted = ret_tainted || callee_return_tainted;
        }

        let ret_w = Self::ret_width_from_desc(&target.desc);
        let ret_t = self.inline_return.unwrap_or_else(|| {
            ret_tainted = true;
            self.solver.fresh_bv(&format!("ret_{}", target.name), ret_w)
        });
        self.vars.insert(dest_var, ret_t);
        self.var_widths.insert(dest_var, ret_w);
        if let Some(st) = self.inline_return_str {
            self.str_vars.insert(dest_var, st);
        } else if Self::returns_string(&target.desc) {
            // Inlined method didn't produce a string term (e.g., returned
            // through an unexplored path). Create a fresh string to maintain
            // the constraint chain for downstream string operations.
            let st = self.solver.fresh_str(&format!("ret_s_{}", target.name));
            self.str_vars.insert(dest_var, st);
        }
        if ret_tainted {
            self.tainted.insert(dest_var);
        }

        for resolved in &targets {
            self.inlined_methods.insert(resolved.clone());
        }

        true
    }

    fn forward_reachable(&self, start: BlockId, limit: usize) -> HashSet<u32> {
        let mut reached = HashSet::new();
        let mut worklist = vec![start];
        while let Some(bid) = worklist.pop() {
            if !reached.insert(bid.0) || reached.len() >= limit {
                continue;
            }
            let succs = self.block_successors(bid);
            for s in succs {
                if s.0 > bid.0 {
                    worklist.push(s);
                }
            }
        }
        reached
    }

    fn block_successors(&self, bid: BlockId) -> Vec<BlockId> {
        match &self.body.block(bid).term {
            Terminator::Goto(t) => vec![*t],
            Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
            Terminator::Switch { cases, default, .. } => {
                let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
                v.push(*default);
                v
            }
            _ => vec![],
        }
    }

    pub(super) fn find_join(&self, then_: BlockId, else_: BlockId) -> Option<BlockId> {
        self.find_join_multi(&[then_, else_])
    }

    fn find_join_multi(&self, targets: &[BlockId]) -> Option<BlockId> {
        if targets.is_empty() { return None; }
        // Compute forward reachable sets for each target.
        let reach_sets: Vec<HashSet<u32>> = targets
            .iter()
            .map(|t| self.forward_reachable(*t, 50))
            .collect();
        // If any target is reachable from another target, the branches are
        // not independent and diamond merge would produce incorrect results.
        // Fall back to path forking in that case.
        for (i, t) in targets.iter().enumerate() {
            for (j, r) in reach_sets.iter().enumerate() {
                if i != j && r.contains(&t.0) {
                    return None;
                }
            }
        }
        let mut common = reach_sets[0].clone();
        for r in &reach_sets[1..] {
            common = common.intersection(r).copied().collect();
        }
        let target_set: HashSet<u32> = targets.iter().map(|t| t.0).collect();
        let mut candidates: Vec<u32> = common.into_iter()
            .filter(|b| !target_set.contains(b))
            .collect();
        candidates.sort();
        candidates.first().map(|&b| BlockId(b))
    }

    // ── Statement handlers ──────────────────────────────────────────────

    /// Process a slice of statements. Returns false if exploration should stop.
    fn handle_stmts(&mut self, stmts: &[Stmt]) -> bool {
        for stmt in stmts {
            if self.budget_exhausted() {
                return false;
            }
            match stmt {
                // Sequential exploration: monitor operations constrain nothing.
                // A concurrency engine reads them; the BMC does not.
                Stmt::MonitorEnter(_) | Stmt::MonitorExit(_) => {}
                Stmt::Assign(v, rv) => {
                    if !self.handle_assign(*v, rv) {
                        // Inline succeeded — but if it threw an unhandled
                        // exception, stop processing this block.
                        if self.inline_throw.is_some() {
                            return false;
                        }
                        continue;
                    }
                }
                Stmt::Assume(op) => {
                    if !self.handle_assume(op) { return false; }
                }
                Stmt::Check(oid) => self.handle_check(*oid),
                Stmt::PutStatic(fk, val) => self.handle_put_static(fk, val),
                Stmt::PutField { field, val, obj } => self.handle_put_field(field, val, obj),
                Stmt::ArrayStore { arr, idx, val } => {
                    let ref_term = self.encode_operand(arr);
                    let idx_term = self.encode_operand(idx);
                    let val_term = self.encode_operand(val);
                    self.array_store_update(ref_term, idx_term, val_term);
                }
                Stmt::Nop => {}
            }
        }
        true
    }

    fn handle_assign(&mut self, v: VarId, rv: &Rvalue) -> bool {
        let is_tainted = self.rvalue_tainted(rv);
        let (t, str_term) = match rv {
            Rvalue::Call { target, args, .. }
                if ajave_models::STR_OWNERS.contains(&target.class.as_str()) =>
            {
                // Handle StringBuilder/StringBuffer <init> as a side effect:
                // register str_vars on the receiver with the initial content.
                if target.name == "<init>" {
                    if let Some(recv) = args.first() {
                        if let Operand::Var(recv_v) = recv {
                            let init_str = if target.desc.starts_with("(Ljava/lang/String;)") {
                                // <init>(String) — use the string argument
                                args.get(1).and_then(|a| self.encode_str_operand(a))
                                    .unwrap_or_else(|| self.solver.str_const(""))
                            } else {
                                // <init>() — empty string
                                self.solver.str_const("")
                            };
                            debug!("str <init> propagating to v{} (class={})", recv_v.0, target.class);
                            self.propagate_str_to_aliases(*recv_v, init_str);
                            // Propagate constant string value through <init>(String)
                            if target.desc.starts_with("(Ljava/lang/String;)") {
                                if let Some(Operand::Const(Const::Str(s))) = args.get(1) {
                                    self.str_consts.insert(*recv_v, s.clone());
                                } else if let Some(Operand::Var(src)) = args.get(1) {
                                    if let Some(s) = self.str_consts.get(src).cloned() {
                                        self.str_consts.insert(*recv_v, s);
                                    }
                                }
                            }
                        }
                    }
                    (self.encode_rvalue(rv), None)
                } else if matches!(target.name.as_str(),
                    "append" | "setLength" | "deleteCharAt" | "delete" | "insert" | "reverse"
                ) {
                    // Mutating method — update str_vars for receiver and all aliases
                    if str_call_can_throw(target) {
                        self.completeness.has_potentially_throwing_havoc = true;
                    }
                    match self.encode_str_call(target, args) {
                        Some((bv, st)) => {
                            if let Some(st) = st {
                                if let Some(Operand::Var(recv_v)) = args.first() {
                                    self.propagate_str_to_aliases(*recv_v, st);
                                }
                            }
                            (bv, st)
                        }
                        None => (self.encode_rvalue(rv), None),
                    }
                } else {
                    if str_call_can_throw(target) {
                        self.completeness.has_potentially_throwing_havoc = true;
                    }
                    match self.encode_str_call(target, args) {
                        Some((bv, st)) => (bv, st),
                        None => (self.encode_rvalue(rv), None),
                    }
                }
            }
            Rvalue::Call { target, args, is_virtual } => {
                if let Some((bv, st)) = self.encode_wrapper_str_call(target, args) {
                    // Modelled call — check if the original method could throw
                    // a RuntimeException. The model resolves the return value
                    // but doesn't capture exception behavior.
                    if could_throw_runtime_exception(target) {
                        self.completeness.has_potentially_throwing_havoc = true;
                    }
                    (bv, st)
                } else if self.math_call_modelled(target) {
                    // Modelling the *value* is not licence to assume totality.
                    // `addExact` and friends are modelled as plain arithmetic,
                    // which drops the `ArithmeticException` they exist to
                    // raise; `floorDiv`/`floorMod` likewise drop the
                    // zero-divisor check. Consult the allowlist exactly as the
                    // wrapper-string and havoc paths do.
                    if could_throw_runtime_exception(target) {
                        self.completeness.has_potentially_throwing_havoc = true;
                    }
                    (self.encode_math_call(target, args), None)
                } else if self.try_inline_call(target, args, v, *is_virtual) {
                    // Inlined — callee body is analyzed directly, so its
                    // exception behavior is fully captured. No havoc flag.
                    return false;
                } else {
                    // Call was not resolved — havoced.
                    self.completeness.all_calls_resolved = false;
                    // If this block has exception edges, the havoced call
                    // could throw to a handler containing an assertion.
                    if let Some(bid) = self.current_block {
                        if !self.body.block(bid).exceptional.is_empty() {
                            self.completeness.has_unresolved_in_try = true;
                        }
                    }
                    // Check if this call could throw a RuntimeException
                    // (for NRE soundness).
                    if could_throw_runtime_exception(target) {
                        self.completeness.has_potentially_throwing_havoc = true;
                    }
                    let bv = self.encode_rvalue(rv);
                    // If the return type is String, create a fresh string
                    // term so downstream string operations (contains, equals,
                    // etc.) can be constrained by Z3's string solver.
                    let st = if Self::returns_string(&target.desc) {
                        Some(self.solver.fresh_str(&format!("hvc_{}", target.name)))
                    } else {
                        None
                    };
                    (bv, st)
                }
            }
            Rvalue::Use(op) => {
                let st = self.encode_str_operand(op);
                (self.encode_rvalue(rv), st)
            }
            Rvalue::Nondet(Ty::Str, _) => {
                let bv = self.encode_rvalue(rv);
                let st = self.nondet_terms.last().and_then(|(_, _, _, _, s)| *s);
                (bv, st)
            }
            Rvalue::Havoc(Ty::Str) => {
                let bv = self.encode_rvalue(rv);
                let st = Some(self.solver.fresh_str("hvs"));
                (bv, st)
            }
            Rvalue::GetStatic(fk) => {
                let k = Self::field_key_raw(fk);
                let st = self.static_str.get(&k).copied().or_else(|| {
                    // Non-program String static: create a fresh string term
                    // so downstream operations can be constrained.
                    if fk.desc == "Ljava/lang/String;" && !self.is_program_class(&fk.class) {
                        Some(self.solver.fresh_str(&format!("sf_{}_{}", fk.class.replace('/', "_"), fk.name)))
                    } else {
                        None
                    }
                });
                (self.encode_rvalue(rv), st)
            }
            Rvalue::GetField { field, obj } => {
                let k = self.field_key_resolved(field);
                let bv = self.encode_rvalue(rv);
                let st = if self.field_str_arrays.contains_key(&k) {
                    let obj_term = self.encode_operand(obj);
                    let str_arr = self.get_field_str_array(&k);
                    Some(self.solver.array_select(str_arr, obj_term))
                } else if field.desc == "Ljava/lang/String;" {
                    // String field not yet tracked — create a fresh string
                    // so downstream operations maintain the constraint chain.
                    let obj_term = self.encode_operand(obj);
                    let str_arr = self.get_field_str_array(&k);
                    Some(self.solver.array_select(str_arr, obj_term))
                } else {
                    None
                };
                (bv, st)
            }
            _ => (self.encode_rvalue(rv), None),
        };
        self.vars.insert(v, t);
        // Attach any FP term the encoder produced for this assignment, and
        // otherwise clear the destination's float view. Leaving a stale entry
        // behind would let a reused JVM local be read as a float it no longer
        // holds — the same slot-reuse hazard that produced wrong answers in
        // the interval domain.
        match self.pending_fp.take() {
            Some(fp) => { self.fp_vars.insert(v, fp); }
            None => {
                if let Rvalue::Use(Operand::Var(src)) = rv {
                    // A copy carries the float view along with the bits.
                    match self.fp_vars.get(src).copied() {
                        Some(fp) => { self.fp_vars.insert(v, fp); }
                        None => { self.fp_vars.remove(&v); }
                    }
                } else {
                    self.fp_vars.remove(&v);
                }
            }
        }
        self.var_widths.insert(v, self.rvalue_result_width(rv));
        // Track concrete class from `new` for exception dispatch / instanceof.
        match rv {
            Rvalue::New(class) => { self.concrete_classes.insert(v, class.clone()); }
            Rvalue::Use(Operand::Var(src)) => {
                // Copy propagation: if src has a concrete class, propagate it.
                if let Some(c) = self.concrete_classes.get(src).cloned() {
                    self.concrete_classes.insert(v, c);
                } else {
                    self.concrete_classes.remove(&v);
                }
            }
            _ => { self.concrete_classes.remove(&v); }
        }
        if let Some(st) = str_term {
            self.str_vars.insert(v, st);
        } else {
            self.str_vars.remove(&v);
        }
        // Propagate constant string values
        match rv {
            Rvalue::Use(Operand::Const(Const::Str(s))) => {
                self.str_consts.insert(v, s.clone());
            }
            Rvalue::Use(Operand::Var(src)) => {
                if let Some(s) = self.str_consts.get(src).cloned() {
                    self.str_consts.insert(v, s);
                } else {
                    self.str_consts.remove(&v);
                }
            }
            _ => { self.str_consts.remove(&v); }
        }
        if is_tainted {
            self.tainted.insert(v);
        } else {
            self.tainted.remove(&v);
        }
        if self.rvalue_float_tainted(rv) {
            self.float_tainted.insert(v);
        } else {
            self.float_tainted.remove(&v);
        }
        true
    }

    fn handle_assume(&mut self, op: &Operand) -> bool {
        let tainted = self.operand_tainted(op);
        if tainted { self.path_tainted = true; }
        if !tainted {
            let t = self.encode_operand(op);
            let c = self.nonzero_constraint(t);
            self.path_constraints.push(c);
            let res = self.check_sat_with_path();
            if res == SatResult::Unsat { return false; }
        }
        true
    }

    fn handle_check(&mut self, oid: ObligationId) {
        let ob_cond = self.body.obligation(oid).cond.clone();
        let ob_kind = self.body.obligation(oid).kind;
        let is_tainted = self.operand_tainted(&ob_cond);
        let cond = self.encode_operand(&ob_cond);
        let violation_cond = self.zero_constraint(cond);
        let (res, witness) = self.check_sat_with_path_and_witness(violation_cond);
        log::debug!("smt-bmc: check {:?} in {} kind={:?} tainted={} path_tainted={} res={:?} pc_len={}",
            oid, self.body.key, ob_kind, is_tainted, self.path_tainted, res, self.path_constraints.len());
        if res == SatResult::Sat && !is_tainted {
            // Record violations even when path_tainted — the JVM replay
            // certifier will filter out spurious witnesses from imprecise
            // float/string modeling. This lets us falsify programs where the
            // violation is real but the path went through havoced operations.
            if let Some(w) = witness {
                // ...except when the witness could not possibly reproduce it.
                //
                // A tainted path means the model rests on a value we
                // approximated — a havoced call, imprecise float or string
                // modelling. An *empty* nondet sequence means the program is
                // deterministic and a witness has nothing to set. Together they
                // make the violation unreplayable by construction: replay just
                // re-runs the same deterministic program, and if the violation
                // were real the concrete engine, which executes it exactly,
                // would already have found it.
                //
                // Publishing anyway costs a JVM replay and, worse, occupies the
                // obligation so an over-approximating engine that could have
                // proved it safe never gets to. `Math.asin` is the clearest
                // case: SMT-LIB has no fp.asin, so the call is havoced, the
                // havoced value satisfies any comparison, and the witness is
                // empty. See benchmarks/ajave/jvm-floats/NaNComparisonIsAlwaysFalse.
                //
                // Suppressing costs precision, never correctness: an
                // under-approximating engine that declines to publish simply
                // leaves the obligation open.
                let unreplayable = self.path_tainted && w.nondet_sequence.is_empty();
                if unreplayable {
                    log::debug!(
                        "smt-bmc: withholding {:?} in {} — tainted path with an \
                         empty witness cannot replay",
                        oid,
                        self.body.key
                    );
                } else {
                    self.violations.push((self.body.key.clone(), oid, w));
                }
            }
        }
        if res != SatResult::Unsat && (is_tainted || self.path_tainted || res == SatResult::Unknown) {
            self.skipped_obligations.insert(oid);
        }
        if self.path_tainted {
            self.completeness.has_tainted_paths = true;
        }
    }

    fn handle_put_static(&mut self, fk: &FieldKey, val: &Operand) {
        self.ensure_clinit(&fk.class);
        let k = Self::field_key_raw(fk);
        let t = self.encode_operand(val);
        self.statics.insert(k.clone(), t);
        if self.operand_tainted(val) {
            self.static_tainted.insert(k.clone());
        } else {
            self.static_tainted.remove(&k);
        }
        if let Some(st) = match val {
            Operand::Var(v) => self.str_vars.get(v).copied(),
            Operand::Const(Const::Str(s)) => Some(self.solver.str_const(s)),
            _ => None,
        } {
            self.static_str.insert(k, st);
        } else {
            self.static_str.remove(&k);
        }
    }

    fn handle_put_field(&mut self, field: &FieldKey, val: &Operand, obj: &Operand) {
        let k = self.field_key_resolved(field);
        let obj_term = self.encode_operand(obj);
        let val_term = self.encode_operand(val);
        let w = Self::field_elem_width(&field.desc);
        let arr = self.get_field_array(&k, w);
        let new_arr = self.solver.array_store(arr, obj_term, val_term);
        self.field_arrays.insert(k.clone(), new_arr);
        if self.operand_tainted(val) {
            self.field_tainted.insert(k.clone());
        } else {
            self.field_tainted.remove(&k);
        }
        // Track string terms through instance fields (per-object via string arrays)
        if let Some(st) = match val {
            Operand::Var(v) => self.str_vars.get(v).copied(),
            Operand::Const(Const::Str(s)) => Some(self.solver.str_const(s)),
            _ => None,
        } {
            let str_arr = self.get_field_str_array(&k);
            let new_str_arr = self.solver.array_store(str_arr, obj_term, st);
            self.field_str_arrays.insert(k, new_str_arr);
        }
    }

    // ── Terminator handlers ─────────────────────────────────────────────

    /// Handle a non-assertion throw by dispatching to the first matching
    /// exception handler on the current block. If no handler matches (or the
    /// thrown type is unknown), mark exploration incomplete.
    fn handle_throw(&mut self, block_id: BlockId, thrown_op: &Operand, stop_at: Option<BlockId>) {
        let exceptional = self.body.block(block_id).exceptional.clone();

        // Determine concrete thrown class from variable tracking.
        let thrown_class = match thrown_op {
            Operand::Var(v) => self.concrete_classes.get(v).cloned(),
            _ => None,
        };

        let Some(thrown_class) = thrown_class else {
            // Can't determine type — mark incomplete.
            self.completeness.all_paths_complete = false;
            return;
        };

        // Encode the thrown reference so we can bind it to the handler variable.
        let thrown_term = self.encode_operand(thrown_op);

        if !exceptional.is_empty() {
            // Find Stack(0) variable — the handler entry expects the exception there.
            let stack0_vid = self.body.vars.iter().enumerate()
                .find(|(_, vi)| matches!(vi.kind, VarKind::Stack(0)))
                .map(|(i, _)| VarId(i as u32));

            // First matching handler wins (JVM exception table order).
            for edge in &exceptional {
                let handler_class = match &edge.class {
                    Some(c) => c.clone(),
                    None => {
                        // catch-all (finally) — always matches.
                        if let Some(sv) = stack0_vid {
                            self.vars.insert(sv, thrown_term);
                        }
                        self.explore_block_until(edge.target, 0, stop_at);
                        return;
                    }
                };
                if self.prog.is_subtype(&thrown_class, &handler_class) || thrown_class == handler_class {
                    debug!("smt-bmc: exception dispatch: throw {} caught by handler for {} at bb{}",
                           thrown_class, handler_class, edge.target.0);
                    if let Some(sv) = stack0_vid {
                        self.vars.insert(sv, thrown_term);
                    }
                    self.explore_block_until(edge.target, 0, stop_at);
                    return;
                }
            }
        }

        // No local handler matched. If we're inside an inlined callee,
        // propagate the exception to the caller via inline_throw.
        if self.call_depth > 0 {
            debug!("smt-bmc: exception propagating from callee: throw {}", thrown_class);
            self.inline_throw = Some((thrown_term, thrown_class));
        } else {
            self.completeness.all_paths_complete = false;
        }
    }

    /// Dispatch an exception (from cross-method propagation) to this block's handlers.
    fn dispatch_exception(
        &mut self,
        block_id: BlockId,
        thrown_term: Term,
        thrown_class: &str,
        stop_at: Option<BlockId>,
    ) {
        let exceptional = self.body.block(block_id).exceptional.clone();

        if !exceptional.is_empty() {
            let stack0_vid = self.body.vars.iter().enumerate()
                .find(|(_, vi)| matches!(vi.kind, VarKind::Stack(0)))
                .map(|(i, _)| VarId(i as u32));

            for edge in &exceptional {
                let handler_class = match &edge.class {
                    Some(c) => c.clone(),
                    None => {
                        if let Some(sv) = stack0_vid {
                            self.vars.insert(sv, thrown_term);
                        }
                        self.explore_block_until(edge.target, 0, stop_at);
                        return;
                    }
                };
                if self.prog.is_subtype(thrown_class, &handler_class) || thrown_class == handler_class {
                    debug!("smt-bmc: cross-method exception dispatch: {} caught by handler for {} at bb{}",
                           thrown_class, handler_class, edge.target.0);
                    if let Some(sv) = stack0_vid {
                        self.vars.insert(sv, thrown_term);
                    }
                    self.explore_block_until(edge.target, 0, stop_at);
                    return;
                }
            }
        }

        // Still no handler — propagate further up if inside another inline.
        if self.call_depth > 0 {
            self.inline_throw = Some((thrown_term, thrown_class.to_string()));
        } else {
            self.completeness.all_paths_complete = false;
        }
    }

    fn handle_goto(&mut self, block_id: BlockId, target: BlockId, stop_at: Option<BlockId>) {
        if target.0 <= block_id.0 {
            let loop_key = (self.body.key.to_string(), target.0);
            let count = self.loop_visits.entry(loop_key).or_insert(0);
            *count += 1;
            if *count > MAX_LOOP_UNROLL {
                self.completeness.all_paths_complete = false;
            } else {
                self.explore_block_until(target, 0, stop_at);
            }
        } else {
            self.explore_block_until(target, 0, stop_at);
        }
    }

    fn handle_branch(
        &mut self,
        block_id: BlockId,
        cond: Operand,
        then_: BlockId,
        else_: BlockId,
        stop_at: Option<BlockId>,
    ) {
        let cond_tainted = self.operand_tainted(&cond);
        let ct = self.encode_operand(&cond);
        let zero = self.solver.bv_const(0, 32);
        let cond_bool = self.solver.bveq(ct, zero);
        let cond_nz = self.solver.not(cond_bool);

        if let Some(join) = self.find_join(then_, else_) {
            self.handle_branch_diamond(cond_tainted, cond_nz, cond_bool, then_, else_, join, stop_at);
        } else {
            self.handle_branch_fork(block_id, cond_tainted, cond_nz, cond_bool, then_, else_, stop_at);
        }
    }

    fn handle_branch_diamond(
        &mut self,
        cond_tainted: bool,
        cond_nz: Term,
        cond_bool: Term,
        then_: BlockId,
        else_: BlockId,
        join: BlockId,
        stop_at: Option<BlockId>,
    ) {
        let saved = self.save_state();
        if cond_tainted { self.path_tainted = true; }
        if !cond_tainted { self.path_constraints.push(cond_nz); }
        self.explore_block_until(then_, 0, Some(join));
        let then_state = self.save_state();
        self.restore_state(saved);

        let saved = self.save_state();
        if cond_tainted { self.path_tainted = true; }
        if !cond_tainted { self.path_constraints.push(cond_bool); }
        self.explore_block_until(else_, 0, Some(join));
        let else_state = self.save_state();
        self.restore_state(saved);

        self.collect_nondets_binary(&then_state, &else_state);
        self.merge_states_ite(cond_nz, &then_state, &else_state);
        self.explore_block_until(join, 0, stop_at);
    }

    fn handle_branch_fork(
        &mut self,
        block_id: BlockId,
        cond_tainted: bool,
        cond_nz: Term,
        cond_bool: Term,
        then_: BlockId,
        else_: BlockId,
        stop_at: Option<BlockId>,
    ) {
        self.fork_count += 1;
        log::trace!("smt-bmc: fork at bb{} in {} then=bb{} else=bb{} stop_at={:?}",
            block_id.0, self.body.key, then_.0, else_.0, stop_at.map(|b| b.0));

        let saved = self.save_state();
        let ir_before = self.inline_return;
        let irs_before = self.inline_return_str;
        let irt_before = self.inline_return_tainted;

        let mut then_explored = false;
        if cond_tainted { self.path_tainted = true; }
        if !cond_tainted {
            self.path_constraints.push(cond_nz);
            let feas = self.check_sat_with_path();
            log::trace!("smt-bmc: fork-then bb{} in {} feas={:?} tainted={}",
                then_.0, self.body.key, feas, cond_tainted);
            // `Unknown` means the solver could not decide whether this branch
            // is reachable. Exploring it anyway is right -- refusing would miss
            // bugs -- but the subtree it opens cannot support a claim of having
            // covered everything, because we do not know the constraint we
            // explored under is satisfiable.
            //
            // This is how `Pan_exceptionprone` became a wrong TRUE. A freshly
            // allocated array's `!= null` came back Unknown, so BMC explored
            // the impossible `== null` branch, every constraint below it was
            // contradictory, both branches of the loop test came back Unsat,
            // nothing was explored -- and `all_paths_complete` was still true,
            // so 62 obligations including an unconditional out-of-bounds read
            // were discharged as exhaustively proven.
            if feas == SatResult::Unknown {
                self.completeness.all_paths_complete = false;
            }
            if feas != SatResult::Unsat {
                self.explore_block_until(then_, 0, stop_at);
                then_explored = true;
            }
        } else {
            self.explore_block_until(then_, 0, stop_at);
            then_explored = true;
        }
        let then_state = self.save_state();
        let then_ir = self.inline_return;
        let then_irs = self.inline_return_str;
        let then_irt = self.inline_return_tainted;
        self.restore_state(saved.clone());

        let mut else_explored = false;
        self.inline_return = ir_before;
        self.inline_return_str = irs_before;
        self.inline_return_tainted = irt_before;
        // Running out of budget mid-fork leaves one side of the branch
        // unexplored, which is exactly the thing a completeness claim must not
        // paper over.
        if self.budget_exhausted() {
            log::trace!("smt-bmc: fork-else bb{} in {} SKIPPED: budget exhausted",
                else_.0, self.body.key);
            self.completeness.all_paths_complete = false;
        }
        if !self.budget_exhausted() {
            if cond_tainted { self.path_tainted = true; }
            if !cond_tainted {
                self.path_constraints.push(cond_bool);
                let feas = self.check_sat_with_path();
                log::trace!("smt-bmc: fork-else bb{} in {} feas={:?}",
                    else_.0, self.body.key, feas);
                if feas == SatResult::Unknown {
                    self.completeness.all_paths_complete = false;
                }
                if feas != SatResult::Unsat {
                    self.explore_block_until(else_, 0, stop_at);
                    else_explored = true;
                }
            } else {
                self.explore_block_until(else_, 0, stop_at);
                else_explored = true;
            }
        }
        let else_state = self.save_state();
        let else_ir = self.inline_return;
        let else_irs = self.inline_return_str;
        let else_irt = self.inline_return_tainted;

        // Deliberately *not* clearing completeness when neither side is
        // reachable. Both branches Unsat means the path condition that got here
        // is contradictory, so no execution follows it and pruning is exactly
        // right -- an infeasible path costs nothing to skip.
        //
        // The case that looked like it needed guarding here, a subtree silently
        // lost because an earlier feasibility answer was wrong, is caught at
        // its source instead: an undecided branch now clears completeness where
        // the `Unknown` occurs. Measured on the smoke set, guarding here as
        // well costs 5 correct answers and 10 points and prevents nothing.
        if then_explored || else_explored {
            self.restore_state(saved);
            let base_len = self.nondet_terms.len();
            if then_explored {
                for nd in &then_state.nondet_terms[base_len..] {
                    self.nondet_terms.push(nd.clone());
                }
            }
            if else_explored {
                for nd in &else_state.nondet_terms[base_len..] {
                    self.nondet_terms.push(nd.clone());
                }
            }
            self.merge_states_ite(cond_nz, &then_state, &else_state);
        } else {
            self.restore_state(saved);
        }

        match (then_explored, else_explored, then_ir, else_ir) {
            (true, true, Some(t), Some(e)) if t != e => {
                self.inline_return = Some(self.solver.ite(cond_nz, t, e));
                self.inline_return_str = match (then_irs, else_irs) {
                    (Some(ts), Some(es)) if ts != es => Some(self.solver.ite(cond_nz, ts, es)),
                    (Some(ts), _) => Some(ts),
                    (_, Some(es)) => Some(es),
                    _ => irs_before,
                };
                self.inline_return_tainted = then_irt || else_irt;
            }
            (true, true, Some(t), Some(_)) => {
                self.inline_return = Some(t);
                self.inline_return_str = then_irs.or(else_irs).or(irs_before);
                self.inline_return_tainted = then_irt || else_irt;
            }
            (true, false, _, _) => {
                self.inline_return = then_ir.or(ir_before);
                self.inline_return_str = then_irs.or(irs_before);
                self.inline_return_tainted = then_irt;
            }
            (false, true, _, _) => {
                self.inline_return = else_ir.or(ir_before);
                self.inline_return_str = else_irs.or(irs_before);
                self.inline_return_tainted = else_irt;
            }
            _ => {
                self.inline_return = ir_before;
                self.inline_return_str = irs_before;
                self.inline_return_tainted = irt_before;
            }
        }
    }

    fn handle_switch(
        &mut self,
        value: Operand,
        cases: Vec<(i32, BlockId)>,
        default: BlockId,
        stop_at: Option<BlockId>,
    ) {
        let value_tainted = self.operand_tainted(&value);
        let vt = self.encode_operand(&value);

        let mut all_targets: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
        all_targets.push(default);

        if let Some(join) = self.find_join_multi(&all_targets) {
            self.handle_switch_diamond(value_tainted, vt, &cases, default, join, stop_at);
        } else {
            self.handle_switch_fork(value_tainted, vt, &cases, default, stop_at);
        }
    }

    fn handle_switch_diamond(
        &mut self,
        value_tainted: bool,
        vt: Term,
        cases: &[(i32, BlockId)],
        default: BlockId,
        join: BlockId,
        stop_at: Option<BlockId>,
    ) {
        let case_conds: Vec<(i32, BlockId, Term)> = cases
            .iter()
            .map(|(cv, t)| {
                let c = self.solver.bv_const(*cv as i64, 32);
                let eq = self.solver.bveq(vt, c);
                (*cv, *t, eq)
            })
            .collect();

        let mut case_saved: Vec<(Term, SavedState)> = Vec::new();
        for &(_, target, cond_eq) in &case_conds {
            if self.budget_exhausted() { break; }
            let saved = self.save_state();
            if value_tainted { self.path_tainted = true; }
            self.path_constraints.push(cond_eq);
            self.explore_block_until(target, 0, Some(join));
            case_saved.push((cond_eq, self.save_state()));
            self.restore_state(saved);
        }

        if self.budget_exhausted() { return; }

        let saved = self.save_state();
        if value_tainted { self.path_tainted = true; }
        for &(_, _, cond_eq) in &case_conds {
            let neq = self.solver.not(cond_eq);
            self.path_constraints.push(neq);
        }
        self.explore_block_until(default, 0, Some(join));
        let mut merged = self.save_state();
        self.restore_state(saved);

        let state_refs: Vec<&SavedState> = case_saved.iter().map(|(_, s)| s).collect();
        self.collect_nondets_dedup(&state_refs);
        self.collect_nondets_dedup(&[&merged]);

        for (cond_eq, cs) in case_saved.iter().rev() {
            self.merge_saved_into(&mut merged, *cond_eq, cs);
        }
        self.apply_merged_state(merged);
        self.explore_block_until(join, 0, stop_at);
    }

    fn handle_switch_fork(
        &mut self,
        value_tainted: bool,
        vt: Term,
        cases: &[(i32, BlockId)],
        default: BlockId,
        stop_at: Option<BlockId>,
    ) {
        let saved = self.save_state();
        let ir_before = self.inline_return;
        let irs_before = self.inline_return_str;
        let irt_before = self.inline_return_tainted;
        let mut case_saved: Vec<(Term, SavedState, Option<Term>, Option<Term>, bool)> = Vec::new();

        for &(case_val, target) in cases {
            if self.budget_exhausted() { break; }
            self.fork_count += 1;
            self.inline_return = ir_before;
            self.inline_return_str = irs_before;
            self.inline_return_tainted = irt_before;
            if value_tainted { self.path_tainted = true; }
            let cv = self.solver.bv_const(case_val as i64, 32);
            let eq = self.solver.bveq(vt, cv);
            self.path_constraints.push(eq);
            self.explore_block_until(target, 0, stop_at);
            let cs = self.save_state();
            let c_ir = self.inline_return;
            let c_irs = self.inline_return_str;
            let c_irt = self.inline_return_tainted;
            case_saved.push((eq, cs, c_ir, c_irs, c_irt));
            self.restore_state(saved.clone());
        }

        self.inline_return = ir_before;
        self.inline_return_str = irs_before;
        self.inline_return_tainted = irt_before;
        if !self.budget_exhausted() {
            if value_tainted { self.path_tainted = true; }
            for &(case_val, _) in cases {
                let cv = self.solver.bv_const(case_val as i64, 32);
                let eq = self.solver.bveq(vt, cv);
                let neq = self.solver.not(eq);
                self.path_constraints.push(neq);
            }
            self.explore_block_until(default, 0, stop_at);
        }
        let mut merged = self.save_state();
        let mut merged_ir = self.inline_return;
        let mut merged_irs = self.inline_return_str;
        let mut any_irt = self.inline_return_tainted;
        self.restore_state(saved);

        let state_refs: Vec<&SavedState> = case_saved.iter().map(|(_, s, _, _, _)| s).collect();
        self.collect_nondets_dedup(&state_refs);
        self.collect_nondets_dedup(&[&merged]);

        for (eq, cs, c_ir, c_irs, c_irt) in case_saved.iter().rev() {
            self.merge_saved_into(&mut merged, *eq, cs);
            any_irt = any_irt || *c_irt;
            match (*c_ir, merged_ir) {
                (Some(c), Some(m)) if c != m => {
                    merged_ir = Some(self.solver.ite(*eq, c, m));
                }
                (Some(c), None) => { merged_ir = Some(c); }
                _ => {}
            }
            match (*c_irs, merged_irs) {
                (Some(c), Some(m)) if c != m => {
                    merged_irs = Some(self.solver.ite(*eq, c, m));
                }
                (Some(c), None) => { merged_irs = Some(c); }
                _ => {}
            }
        }

        self.apply_merged_state(merged);
        self.inline_return = merged_ir.or(ir_before);
        self.inline_return_str = merged_irs.or(irs_before);
        self.inline_return_tainted = any_irt;
    }

    // ── Main exploration entry points ───────────────────────────────────

    pub(super) fn explore_block(&mut self, block_id: BlockId, stmt_idx: usize) {
        self.explore_block_until(block_id, stmt_idx, None);
    }

    fn explore_block_until(&mut self, block_id: BlockId, stmt_idx: usize, stop_at: Option<BlockId>) {
        if stop_at == Some(block_id) {
            return;
        }
        self.block_visits += 1;
        if self.depth > self.max_depth || self.budget_exhausted() {
            // Depth limit also truncates, so mark it either way.
            self.completeness.all_paths_complete = false;
            return;
        }

        let stmts = self.body.block(block_id).stmts[stmt_idx..].to_vec();
        let term = self.body.block(block_id).term.clone();

        self.current_block = Some(block_id);
        // Apply AI interval hints for this block (prunes infeasible regions).
        self.apply_ai_hints(block_id);
        if !self.handle_stmts(&stmts) {
            // If a callee threw an unhandled exception, dispatch to this
            // block's exception handlers (cross-method propagation).
            if let Some((thrown_term, thrown_class)) = self.inline_throw.take() {
                self.dispatch_exception(block_id, thrown_term, &thrown_class, stop_at);
            }
            return;
        }

        if self.budget_exhausted() {
            return;
        }

        self.depth += 1;
        match &term {
            Terminator::Goto(t) => self.handle_goto(block_id, *t, stop_at),
            Terminator::Branch { cond, then_, else_ } => {
                self.handle_branch(block_id, cond.clone(), *then_, *else_, stop_at);
            }
            Terminator::Switch { value, cases, default } => {
                self.handle_switch(value.clone(), cases.clone(), *default, stop_at);
            }
            Terminator::Return(Some(val)) => {
                if self.call_depth > 0 {
                    self.inline_return = Some(self.encode_operand(val));
                    self.inline_return_str = self.encode_str_operand(val)
                        .or(self.inline_return_str);
                    self.inline_return_tainted = self.inline_return_tainted
                        || self.operand_tainted(val) || self.path_tainted;
                }
            }
            Terminator::Return(None) | Terminator::Halt => {}
            Terminator::Throw(thrown_op) => {
                // Assertion throws (preceded by `check Assertion` in the same block)
                // are fully handled — the check already fired.
                let is_assert_throw = stmts.iter().any(|s| matches!(s, Stmt::Check(oid) if self.body.obligation(*oid).kind == ObligationKind::Assertion));
                if is_assert_throw {
                    // Already checked; nothing more to do.
                } else {
                    self.handle_throw(block_id, thrown_op, stop_at);
                }
            }
            Terminator::Diverge(_) => {
                self.completeness.all_paths_complete = false;
            }
        }
        self.depth -= 1;
    }
}

#[cfg(test)]
mod jdk_allowlist_tests {
    use super::is_total_jdk_method;

    /// Signatures verified on a real JVM to throw a `RuntimeException`.
    /// `tools/validate_jdk_allowlist.py` reproduces the evidence; this test
    /// asserts the allowlist agrees. Issue #48 found 22 of these wrongly
    /// allowlisted, each a reachable wrong TRUE (-16).
    const MUST_THROW: &[(&str, &str, &str)] = &[
        // Partial functions: throw on empty/out-of-range receivers.
        ("java/util/ArrayList", "get", "(I)Ljava/lang/Object;"),
        ("java/util/ArrayList", "add", "(ILjava/lang/Object;)V"),
        ("java/util/Iterator", "next", "()Ljava/lang/Object;"),
        ("java/util/Stack", "pop", "()Ljava/lang/Object;"),
        ("java/util/Stack", "peek", "()Ljava/lang/Object;"),
        ("java/util/ArrayDeque", "pop", "()Ljava/lang/Object;"),
        // Bounds / store checks.
        ("java/lang/System", "arraycopy", "(Ljava/lang/Object;ILjava/lang/Object;II)V"),
        ("java/lang/String", "charAt", "(I)C"),
        ("java/lang/String", "substring", "(I)Ljava/lang/String;"),
        // ArithmeticException on overflow or zero divisor.
        ("java/lang/Math", "addExact", "(II)I"),
        ("java/lang/Math", "multiplyExact", "(II)I"),
        ("java/lang/Math", "toIntExact", "(J)I"),
        ("java/lang/Math", "floorDiv", "(II)I"),
        ("java/lang/Math", "floorMod", "(II)I"),
        // NumberFormatException — note these differ from the primitive
        // overloads only by descriptor, which is why the check is descriptor-keyed.
        ("java/lang/Integer", "valueOf", "(Ljava/lang/String;)Ljava/lang/Integer;"),
        ("java/lang/Integer", "parseInt", "(Ljava/lang/String;)I"),
        ("java/lang/Double", "parseDouble", "(Ljava/lang/String;)D"),
        // IllegalFormatException.
        ("java/lang/String", "format", "(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;"),
        ("java/io/PrintStream", "format", "(Ljava/lang/String;[Ljava/lang/Object;)Ljava/io/PrintStream;"),
        // NPE on null arguments.
        ("java/lang/String", "concat", "(Ljava/lang/String;)Ljava/lang/String;"),
        ("java/lang/String", "contains", "(Ljava/lang/CharSequence;)Z"),
        ("java/util/TreeMap", "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"),
        // NegativeArraySizeException — again distinguished only by descriptor.
        ("java/lang/StringBuilder", "<init>", "(I)V"),
        // Blanket class allowlists used to let these through.
        ("java/util/Arrays", "copyOfRange", "([III)[I"),
        ("java/util/Collections", "max", "(Ljava/util/Collection;)Ljava/lang/Object;"),
        ("java/util/Collections", "nCopies", "(ILjava/lang/Object;)Ljava/util/List;"),
        ("java/util/Scanner", "hasNext", "()Z"),
        // Regex methods throw PatternSyntaxException.
        ("java/lang/String", "matches", "(Ljava/lang/String;)Z"),
        ("java/lang/String", "split", "(Ljava/lang/String;)[Ljava/lang/String;"),
        ("java/lang/String", "replaceAll",
         "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;"),
    ];

    /// Signatures verified total on a real JVM under adversarial arguments.
    const MUST_NOT_THROW: &[(&str, &str, &str)] = &[
        ("java/lang/Object", "hashCode", "()I"),
        ("java/lang/String", "length", "()I"),
        ("java/lang/String", "trim", "()Ljava/lang/String;"),
        ("java/lang/String", "equals", "(Ljava/lang/Object;)Z"),
        ("java/lang/String", "toCharArray", "()[C"),
        ("java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;"),
        ("java/lang/Integer", "intValue", "()I"),
        ("java/lang/Boolean", "parseBoolean", "(Ljava/lang/String;)Z"),
        ("java/lang/Math", "abs", "(I)I"),
        ("java/lang/Math", "sqrt", "(D)D"),
        ("java/lang/Math", "max", "(II)I"),
        ("java/lang/System", "currentTimeMillis", "()J"),
        ("java/lang/StringBuilder", "<init>", "()V"),
        ("java/lang/StringBuilder", "length", "()I"),
        ("java/util/ArrayList", "size", "()I"),
        ("java/util/Iterator", "hasNext", "()Z"),
        ("java/lang/Character", "isDigit", "(C)Z"),
        ("org/sosy_lab/sv_benchmarks/Verifier", "nondetInt", "()I"),
    ];

    #[test]
    fn throwing_signatures_are_not_allowlisted() {
        for &(class, name, desc) in MUST_THROW {
            assert!(
                !is_total_jdk_method(class, name, desc),
                "{class}.{name}{desc} throws a RuntimeException but is allowlisted \
                 as total — that is a reachable wrong TRUE"
            );
        }
    }

    #[test]
    fn total_signatures_are_allowlisted() {
        for &(class, name, desc) in MUST_NOT_THROW {
            assert!(
                is_total_jdk_method(class, name, desc),
                "{class}.{name}{desc} is total but is not allowlisted \
                 — costs precision"
            );
        }
    }

    /// A user class whose name merely contains "Verifier" must not inherit the
    /// nondet source's exemption. This was a substring match before issue #48.
    #[test]
    fn verifier_match_is_exact() {
        assert!(!is_total_jdk_method("MyVerifierHelper", "doWork", "()V"));
        assert!(!is_total_jdk_method("com/example/Verifier", "doWork", "()V"));
        assert!(is_total_jdk_method(
            "org/sosy_lab/sv_benchmarks/Verifier",
            "nondetInt",
            "()I"
        ));
    }
}
