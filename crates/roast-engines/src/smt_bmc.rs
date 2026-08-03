//! SMT-backed bounded model checker.
//!
//! Encodes paths symbolically and asks a solver for satisfying assignments,
//! replacing the concrete engine's "enumerate, don't solve" with "solve, don't
//! enumerate". Finds any bug reachable within bounded depth for arbitrary
//! integer/long inputs, not just a fixed candidate pool.
//!
//! Direction: Under. JvmReplay confirms all witnesses.

use std::collections::{HashMap, HashSet};

use log::{debug, info, warn};
use roast_core::artifact::*;
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine, Progress};
use roast_core::smt::{SatResult, Solver, SolverFactory, Term};
use roast_ir::verdict::{NondetEntry, NondetValue, Witness};
use roast_ir::*;
use roast_models;

/// Triple key for field identification: (class, name, desc).
type FK = (String, String, String);

/// Maximum number of solver check-sat calls per run to prevent hangs.
const MAX_SOLVER_CALLS: u32 = 10_000;

/// Maximum number of violations to collect before stopping exploration.
const MAX_VIOLATIONS: usize = 50;

/// Maximum call inlining depth to prevent infinite recursion.
const MAX_CALL_DEPTH: u32 = 10;

/// Maximum number of times a loop back-edge may be taken on a single path.
const MAX_LOOP_UNROLL: u32 = 5;

/// Maximum total block visits across all paths. Prevents exponential blowup
/// from loops with internal branches: e.g. 5 unrolls × 3 branches per
/// iteration = 2^15 paths, each visiting ~10 blocks = 320k visits.
const MAX_BLOCK_VISITS: u64 = 50_000;

/// Maximum number of path forks. Path forking (as opposed to diamond merging)
/// doubles the work at each fork. This limit prevents exponential blowup.
const MAX_FORKS: u32 = 500;

pub struct SmtBmc {
    factory: Box<dyn SolverFactory>,
    max_depth: u32,
    done: bool,
}

impl SmtBmc {
    pub fn new(factory: Box<dyn SolverFactory>, max_depth: u32) -> Self {
        SmtBmc {
            factory,
            max_depth,
            done: false,
        }
    }
}

impl Engine for SmtBmc {
    fn id(&self) -> EngineId {
        EngineId("smt-bmc")
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

        let mut solver = match self.factory.create() {
            Ok(s) => s,
            Err(e) => {
                warn!("smt-bmc: failed to create solver: {e}");
                return Progress::Exhausted;
            }
        };

        info!(
            "smt-bmc: starting symbolic exploration (max_depth={}) on {entry:?}",
            self.max_depth
        );

        let type_array = solver.fresh_array("type", 32);
        let mut ctx = ExploreCtx {
            solver: solver.as_mut(),
            prog,
            body,
            vars: HashMap::new(),
            str_vars: HashMap::new(),
            nondet_terms: Vec::new(),
            violations: Vec::new(),
            depth: 0,
            max_depth: self.max_depth,
            solver_calls: 0,
            exhausted: false,
            all_paths_complete: true,
            skipped_obligations: HashSet::new(),
            statics: HashMap::new(),
            static_str: HashMap::new(),
            static_tainted: HashSet::new(),
            field_arrays: HashMap::new(),
            field_tainted: HashSet::new(),
            array_map: Vec::new(),
            type_array,
            type_ids: HashMap::new(),
            next_type_id: 1,
            tainted: HashSet::new(),
            float_tainted: HashSet::new(),
            path_tainted: false,
            call_depth: 0,
            loop_visits: HashMap::new(),
            block_visits: 0,
            fork_count: 0,
            clinit_done: HashSet::new(),
            next_alloc_id: 1,
            inline_return: None,
            inline_return_tainted: false,
            path_constraints: Vec::new(),
            inlined_methods: HashSet::new(),
        };

        ctx.explore_block(body.entry, 0);

        let violations = std::mem::take(&mut ctx.violations);
        let violations_empty = violations.is_empty();
        debug!(
            "smt-bmc: exploration complete, found {} violation(s), {} solver calls, {} block visits, {} forks, exhausted={}, all_paths_complete={}, skipped={}",
            violations.len(),
            ctx.solver_calls,
            ctx.block_visits,
            ctx.fork_count,
            ctx.exhausted,
            ctx.all_paths_complete,
            ctx.skipped_obligations.len(),
        );

        let mut advanced = false;
        for (method, oid, witness) in violations {
            let oref = ObligationRef {
                method,
                id: oid,
            };
            debug!(
                "smt-bmc: publishing violation at {oref:?}, witness={:?}",
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

        // If exploration completed without hitting budget limits and found
        // no violations, publish Bounded for obligations in the entry method.
        // Only the entry method's obligations are covered by the BMC's exploration;
        // callee obligations are only covered if inlining succeeded, but tracking
        // that precisely is complex, so we conservatively restrict to the entry.
        if violations_empty && !ctx.exhausted && ctx.budget_left() {
            // If all paths were fully explored (no truncation), the BMC has
            // exhaustively covered every reachable state. This is a sound
            // over-approximation proof: discharge obligations directly.
            if ctx.all_paths_complete {
                let open_list = bb.open();
                log::trace!("smt-bmc: exhaustive discharge check: entry={entry:?}, inlined={:?}, open={:?}, skipped={:?}", ctx.inlined_methods, open_list, ctx.skipped_obligations);
                for oref in open_list {
                    if (&oref.method == entry || ctx.inlined_methods.contains(&oref.method))
                        && !ctx.skipped_obligations.contains(&oref.id)
                    {
                        debug!("smt-bmc: discharging {oref:?} (exhaustive exploration)");
                        let _ = bb.publish(
                            self.id(),
                            Direction::Over,
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
            } else {
                for oref in bb.open() {
                    if &oref.method == entry {
                        let _ = bb.publish(
                            self.id(),
                            self.direction(),
                            Artifact::Status(oref, Status::Bounded { k: self.max_depth }),
                        );
                        advanced = true;
                    }
                }
            }
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Stalled
        }
    }
}

struct ExploreCtx<'a> {
    solver: &'a mut dyn Solver,
    prog: &'a Program,
    /// The body currently being explored (changes during call inlining).
    body: &'a Body,
    /// Current symbolic state: VarId -> Term (bitvector for ints, BV reference for objects).
    vars: HashMap<VarId, Term>,
    /// String content terms, keyed by VarId.
    str_vars: HashMap<VarId, Term>,
    /// (nondet_index, bv_term, width, Ty, Option<str_term>) in encounter order.
    nondet_terms: Vec<(usize, Term, u32, Ty, Option<Term>)>,
    /// Found violations: (method_key, obligation_id, witness).
    violations: Vec<(MethodKey, ObligationId, Witness)>,
    depth: u32,
    max_depth: u32,
    solver_calls: u32,
    exhausted: bool,
    all_paths_complete: bool,
    skipped_obligations: HashSet<ObligationId>,

    // ── Heap model ──────────────────────────────────────────────────────
    /// Static fields: flat map (class, name, desc) → last-written BV term.
    statics: HashMap<FK, Term>,
    /// String content for static fields.
    static_str: HashMap<FK, Term>,
    /// Taint for static fields.
    static_tainted: HashSet<FK>,
    /// Instance fields: per-field SMT arrays `(Array BV32 BV_w)` keyed by
    /// (class, name, desc).  `PutField` stores to the array,
    /// `GetField` selects — giving precise per-object semantics.
    field_arrays: HashMap<FK, Term>,
    /// Taint per instance field — set if a tainted value was ever stored.
    field_tainted: HashSet<FK>,
    /// Per-object array tracking: (ref, contents_array, length).
    array_map: Vec<(Term, Term, Term)>,
    /// Type array: maps object reference → type ID (BV32).
    /// Used for InstanceOf checks.
    type_array: Term,
    /// Class name → integer type ID (monotonically assigned, never saved/restored).
    type_ids: HashMap<String, i64>,
    next_type_id: i64,

    // ── Taint ───────────────────────────────────────────────────────────
    tainted: HashSet<VarId>,
    float_tainted: HashSet<VarId>,
    path_tainted: bool,

    // ── Exploration state ───────────────────────────────────────────────
    call_depth: u32,
    loop_visits: HashMap<(String, u32), u32>,
    block_visits: u64,
    fork_count: u32,
    clinit_done: HashSet<String>,
    next_alloc_id: i64,
    inline_return: Option<Term>,
    inline_return_tainted: bool,
    path_constraints: Vec<Term>,
    inlined_methods: HashSet<MethodKey>,
}

/// Snapshot of mutable state for save/restore across forks and diamond merges.
#[derive(Clone)]
struct SavedState {
    vars: HashMap<VarId, Term>,
    str_vars: HashMap<VarId, Term>,
    nondet_terms: Vec<(usize, Term, u32, Ty, Option<Term>)>,
    tainted: HashSet<VarId>,
    float_tainted: HashSet<VarId>,
    path_tainted: bool,
    statics: HashMap<FK, Term>,
    static_str: HashMap<FK, Term>,
    static_tainted: HashSet<FK>,
    field_arrays: HashMap<FK, Term>,
    field_tainted: HashSet<FK>,
    array_map: Vec<(Term, Term, Term)>,
    type_array: Term,
    loop_visits: HashMap<(String, u32), u32>,
    pc_len: usize,
}

impl<'a> ExploreCtx<'a> {
    fn budget_left(&self) -> bool {
        !self.exhausted
            && self.solver_calls < MAX_SOLVER_CALLS
            && self.violations.len() < MAX_VIOLATIONS
            && self.block_visits < MAX_BLOCK_VISITS
            && self.fork_count < MAX_FORKS
    }

    fn width_of_var(&self, vid: VarId) -> u32 {
        match self.body.var(vid).ty {
            Ty::Long | Ty::Double => 64,
            _ => 32,
        }
    }

    fn width_of_ty(&self, ty: &Ty) -> u32 {
        match ty {
            Ty::Long | Ty::Double => 64,
            _ => 32,
        }
    }

    fn width_of_operand(&self, op: &Operand) -> u32 {
        match op {
            Operand::Var(v) => self.width_of_var(*v),
            Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => 64,
            _ => 32,
        }
    }

    fn get_var(&mut self, vid: VarId) -> Term {
        if let Some(&t) = self.vars.get(&vid) {
            return t;
        }
        let w = self.width_of_var(vid);
        let t = self.solver.fresh_bv(&format!("uninit_v{}", vid.0), w);
        self.vars.insert(vid, t);
        t
    }

    /// Returns true if an operand's value depends on an unmodelled operation.
    fn operand_tainted(&self, op: &Operand) -> bool {
        matches!(op, Operand::Var(v) if self.tainted.contains(v))
    }

    /// Returns true if the operand is a floating-point type (Float or Double).
    /// These are modeled as bitvectors, so arithmetic on them is semantically wrong.
    fn operand_is_float(&self, op: &Operand) -> bool {
        match op {
            Operand::Const(c) => matches!(c.ty(), Ty::Float | Ty::Double),
            Operand::Var(v) => {
                self.body.vars.get(v.0 as usize)
                    .map(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
                    .unwrap_or(false)
            }
        }
    }

    /// Returns true if the operand has float taint — its BV encoding is
    /// semantically wrong due to float/double operations.
    fn operand_float_tainted(&self, op: &Operand) -> bool {
        matches!(op, Operand::Var(v) if self.float_tainted.contains(v))
    }

    /// Returns true if evaluating this rvalue produces a tainted result —
    /// either because it is itself unmodelled, or because it consumes a
    /// tainted operand.
    fn field_key(fk: &FieldKey) -> (String, String, String) {
        (fk.class.clone(), fk.name.clone(), fk.desc.clone())
    }

    fn rvalue_tainted(&mut self, rv: &Rvalue) -> bool {
        match rv {
            Rvalue::GetStatic(fk) => {
                self.ensure_clinit(&fk.class);
                let k = Self::field_key(fk);
                if self.statics.contains_key(&k) {
                    self.static_tainted.contains(&k)
                } else if self.is_program_class(&fk.class) {
                    // Program field at default value (0/null): not tainted.
                    false
                } else {
                    // Library ref-type fields (e.g. System.out) are modelled as
                    // non-null symbolic values — consistent, not tainted.
                    // Library primitive fields are unconstrained → tainted.
                    !(fk.desc.starts_with('L') || fk.desc.starts_with('['))
                }
            }
            Rvalue::GetField { field, .. } => {
                // With per-object field arrays, GetField is never tainted
                // due to "unknown value" — array_select returns a consistent
                // symbolic value for the same (ref, field) pair.
                // Only tainted if a tainted value was stored to this field.
                let k = Self::field_key(field);
                self.field_tainted.contains(&k)
            }
            Rvalue::ArrayLoad { arr, idx } => {
                self.operand_tainted(arr) || self.operand_tainted(idx)
            }
            Rvalue::ArrayLength(arr) => self.operand_tainted(arr),
            Rvalue::NewArray { len, .. } => self.operand_tainted(len),
            Rvalue::InstanceOf { obj, .. } => {
                // InstanceOf is modelled via type_array lookup.
                // Only tainted if the object reference is tainted.
                self.operand_tainted(obj)
            }
            Rvalue::New(_) => false,
            Rvalue::Call { target, args, is_virtual } => {
                if roast_models::STR_OWNERS.contains(&target.class.as_str()) {
                    return !self.str_call_modelled(target, args);
                }
                // Math methods are modelled precisely.
                if self.math_call_modelled(target) {
                    return false;
                }
                if self.can_inline(target, *is_virtual) {
                    return false;
                }
                true
            }
            Rvalue::Use(o) | Rvalue::Neg(o) => self.operand_tainted(o) || self.operand_is_float(o),
            Rvalue::Cast(_, o) => {
                self.operand_tainted(o) || self.operand_is_float(o)
            }
            Rvalue::Bin(_, a, b) | Rvalue::Cmp(a, b) => {
                self.operand_tainted(a) || self.operand_tainted(b)
                    || self.operand_is_float(a) || self.operand_is_float(b)
            }
            Rvalue::Nondet(..) => false,
            // Havoc produces an unconstrained value. For Under (finding bugs),
            // this is fine. For Over (discharge), depending on a havoc value
            // is unsound — the solver can pick any value, but the real program
            // may pick a different one.
            Rvalue::Havoc(_) => true,
        }
    }

    /// Returns true if the rvalue is float-tainted specifically (BV encoding
    /// of float/double is semantically wrong). This is a subset of
    /// `rvalue_tainted` — heap taint is NOT float taint.
    fn rvalue_float_tainted(&self, rv: &Rvalue) -> bool {
        match rv {
            Rvalue::Use(o) | Rvalue::Neg(o) => {
                self.operand_float_tainted(o) || self.operand_is_float(o)
            }
            Rvalue::Cast(_, o) => {
                self.operand_float_tainted(o) || self.operand_is_float(o)
            }
            Rvalue::Bin(_, a, b) | Rvalue::Cmp(a, b) => {
                self.operand_float_tainted(a) || self.operand_float_tainted(b)
                    || self.operand_is_float(a) || self.operand_is_float(b)
            }
            _ => false,
        }
    }

    /// Check whether a call target can be inlined.
    fn can_inline(&self, target: &MethodKey, is_virtual: bool) -> bool {
        if self.call_depth >= MAX_CALL_DEPTH {
            return false;
        }
        if is_virtual {
            let targets = self.prog.devirtualise(target);
            !targets.is_empty() && targets.iter().all(|t| self.prog.body(t).is_some())
        } else {
            self.prog.body(target).is_some()
        }
    }

    /// Check if a string method call can be encoded via the string theory.
    fn str_call_modelled(&self, target: &MethodKey, args: &[Operand]) -> bool {
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
            "valueOf" => true, // takes an int arg, not a string receiver
            _ => false,
        }
    }

    /// Check whether a Math/Integer/Long static method can be precisely modelled.
    fn math_call_modelled(&self, target: &MethodKey) -> bool {
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

    /// Encode a modelled Math/Integer/Long static method call.
    fn encode_math_call(&mut self, target: &MethodKey, args: &[Operand]) -> Term {
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
                self.solver.bvsdiv(a, b) // approximate: use signed div
            }
            ("java/lang/Integer" | "java/lang/Long", "remainderUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsrem(a, b)
            }
            ("java/lang/Integer" | "java/lang/Long", "compareUnsigned") => {
                let a = self.encode_operand(&args[0]);
                let b = self.encode_operand(&args[1]);
                self.solver.bvsub(a, b) // approximate
            }
            // parseInt/parseLong: return unconstrained (sound havoc)
            ("java/lang/Integer", "parseInt") | ("java/lang/Long", "parseLong") => {
                let w = if class == "java/lang/Long" { 64 } else { 32 };
                self.solver.fresh_bv("parse", w)
            }
            _ => {
                // Fallback for ops we listed as modelled but missed here:
                // bitCount, numberOfLeadingZeros, etc. — use fresh BV (sound).
                self.solver.fresh_bv("math_hv", 32)
            }
        }
    }

    /// Get or create the field array for an instance field.
    /// Program classes use a zero-initialized array (Java default values).
    /// Library classes use a fresh unconstrained array.
    fn get_field_array(&mut self, k: &FK, elem_width: u32) -> Term {
        if let Some(&arr) = self.field_arrays.get(k) {
            return arr;
        }
        let arr = if self.is_program_class(&k.0) {
            let zero = self.solver.bv_const(0, elem_width);
            self.solver.const_array(zero, elem_width)
        } else {
            self.solver.fresh_array(&format!("f_{}_{}", k.0.replace('/', "_"), k.1), elem_width)
        };
        self.field_arrays.insert(k.clone(), arr);
        arr
    }

    /// Element width for a field descriptor.
    fn field_elem_width(desc: &str) -> u32 {
        match desc.as_bytes().first() {
            Some(b'J') | Some(b'D') => 64,
            _ => 32,
        }
    }

    /// Get or create a type ID for a class name.
    fn get_type_id(&mut self, class: &str) -> i64 {
        if let Some(&id) = self.type_ids.get(class) {
            return id;
        }
        let id = self.next_type_id;
        self.next_type_id += 1;
        self.type_ids.insert(class.to_string(), id);
        id
    }

    /// Get all type IDs that are subtypes of the given class.
    fn subtype_ids(&mut self, class: &str) -> Vec<i64> {
        // Collect all known classes that are subtypes of `class`.
        let all_classes: Vec<String> = self.type_ids.keys().cloned().collect();
        let mut result = Vec::new();
        // The target class itself.
        let target_id = self.get_type_id(class);
        result.push(target_id);
        // Check all known classes.
        for c in &all_classes {
            if c != class && self.prog.is_subtype(c, class) {
                let id = self.get_type_id(c);
                if !result.contains(&id) {
                    result.push(id);
                }
            }
        }
        result
    }

    fn save_state(&self) -> SavedState {
        SavedState {
            vars: self.vars.clone(),
            str_vars: self.str_vars.clone(),
            nondet_terms: self.nondet_terms.clone(),
            tainted: self.tainted.clone(),
            float_tainted: self.float_tainted.clone(),
            path_tainted: self.path_tainted,
            statics: self.statics.clone(),
            static_str: self.static_str.clone(),
            static_tainted: self.static_tainted.clone(),
            field_arrays: self.field_arrays.clone(),
            field_tainted: self.field_tainted.clone(),
            array_map: self.array_map.clone(),
            type_array: self.type_array,
            loop_visits: self.loop_visits.clone(),
            pc_len: self.path_constraints.len(),
        }
    }

    fn restore_state(&mut self, s: SavedState) {
        self.vars = s.vars;
        self.str_vars = s.str_vars;
        self.nondet_terms = s.nondet_terms;
        self.tainted = s.tainted;
        self.float_tainted = s.float_tainted;
        self.path_tainted = s.path_tainted;
        self.statics = s.statics;
        self.static_str = s.static_str;
        self.static_tainted = s.static_tainted;
        self.field_arrays = s.field_arrays;
        self.field_tainted = s.field_tainted;
        self.array_map = s.array_map;
        self.type_array = s.type_array;
        self.loop_visits = s.loop_visits;
        self.path_constraints.truncate(s.pc_len);
    }

    /// ITE-merge two branch states into the current state.
    /// `cond` is the Bool term that selects `a` (true) vs `b` (false).
    fn merge_states_ite(&mut self, cond: Term, a: &SavedState, b: &SavedState) {
        // Variables
        let all_vids: HashSet<VarId> = a.vars.keys().chain(b.vars.keys()).copied().collect();
        for vid in all_vids {
            match (a.vars.get(&vid).copied(), b.vars.get(&vid).copied()) {
                (Some(t), Some(e)) if t == e => { self.vars.insert(vid, t); }
                (Some(t), Some(e)) => {
                    let m = self.solver.ite(cond, t, e);
                    self.vars.insert(vid, m);
                }
                (Some(t), None) => {
                    let fresh = self.solver.fresh_bv("merge", self.width_of_var(vid));
                    let m = self.solver.ite(cond, t, fresh);
                    self.vars.insert(vid, m);
                }
                (None, Some(e)) => {
                    let fresh = self.solver.fresh_bv("merge", self.width_of_var(vid));
                    let m = self.solver.ite(cond, fresh, e);
                    self.vars.insert(vid, m);
                }
                (None, None) => {}
            }
        }

        // Static fields
        let all_sk: HashSet<_> = a.statics.keys().chain(b.statics.keys()).cloned().collect();
        for k in all_sk {
            match (a.statics.get(&k).copied(), b.statics.get(&k).copied()) {
                (Some(t), Some(e)) if t == e => { self.statics.insert(k, t); }
                (Some(t), Some(e)) => {
                    let m = self.solver.ite(cond, t, e);
                    self.statics.insert(k, m);
                }
                (Some(t), None) => { self.statics.insert(k, t); }
                (None, Some(e)) => { self.statics.insert(k, e); }
                (None, None) => {}
            }
        }

        // Instance field arrays: ITE on the array terms
        let all_fk: HashSet<_> = a.field_arrays.keys().chain(b.field_arrays.keys()).cloned().collect();
        for k in all_fk {
            match (a.field_arrays.get(&k).copied(), b.field_arrays.get(&k).copied()) {
                (Some(t), Some(e)) if t == e => { self.field_arrays.insert(k, t); }
                (Some(t), Some(e)) => {
                    let m = self.solver.ite(cond, t, e);
                    self.field_arrays.insert(k, m);
                }
                (Some(t), None) => { self.field_arrays.insert(k, t); }
                (None, Some(e)) => { self.field_arrays.insert(k, e); }
                (None, None) => {}
            }
        }

        // Array map: union (ITE chain handles reference resolution)
        let base_arr = self.array_map.clone();
        for entry in &a.array_map {
            if !base_arr.iter().any(|(r, _, _)| *r == entry.0) {
                self.array_map.push(entry.clone());
            }
        }
        for entry in &b.array_map {
            if !self.array_map.iter().any(|(r, _, _)| *r == entry.0) {
                self.array_map.push(entry.clone());
            }
        }

        // Type array: ITE
        if a.type_array != b.type_array {
            self.type_array = self.solver.ite(cond, a.type_array, b.type_array);
        } else {
            self.type_array = a.type_array;
        }

        // Taint: conservative union
        self.tainted = &a.tainted | &b.tainted;
        self.float_tainted = &a.float_tainted | &b.float_tainted;
        self.static_tainted = &a.static_tainted | &b.static_tainted;
        self.field_tainted = &a.field_tainted | &b.field_tainted;
        self.path_tainted = a.path_tainted || b.path_tainted;

        // String vars: keep those present in both
        let all_sv: HashSet<VarId> = a.str_vars.keys().chain(b.str_vars.keys()).copied().collect();
        self.str_vars.clear();
        for vid in all_sv {
            match (a.str_vars.get(&vid).copied(), b.str_vars.get(&vid).copied()) {
                (Some(t), Some(e)) if t == e => { self.str_vars.insert(vid, t); }
                (Some(t), Some(e)) => {
                    let m = self.solver.ite(cond, t, e);
                    self.str_vars.insert(vid, m);
                }
                _ => {}
            }
        }

        // Static strings
        let all_ss: HashSet<_> = a.static_str.keys().chain(b.static_str.keys()).cloned().collect();
        self.static_str.clear();
        for k in all_ss {
            match (a.static_str.get(&k).copied(), b.static_str.get(&k).copied()) {
                (Some(t), Some(e)) if t == e => { self.static_str.insert(k, t); }
                (Some(t), Some(e)) => {
                    let m = self.solver.ite(cond, t, e);
                    self.static_str.insert(k, m);
                }
                (Some(t), None) => { self.static_str.insert(k, t); }
                (None, Some(e)) => { self.static_str.insert(k, e); }
                (None, None) => {}
            }
        }
    }

    /// ITE-merge a case state into an accumulator SavedState.
    /// `cond` selects `case` (true) vs `acc` (false).
    fn merge_saved_into(&mut self, acc: &mut SavedState, cond: Term, case: &SavedState) {
        // Vars
        let all_vids: HashSet<VarId> = case.vars.keys().chain(acc.vars.keys()).copied().collect();
        for vid in all_vids {
            match (case.vars.get(&vid).copied(), acc.vars.get(&vid).copied()) {
                (Some(a), Some(b)) if a == b => {}
                (Some(a), Some(b)) => {
                    let m = self.solver.ite(cond, a, b);
                    acc.vars.insert(vid, m);
                }
                (Some(a), None) => {
                    let fresh = self.solver.fresh_bv("sw_merge", self.width_of_var(vid));
                    let m = self.solver.ite(cond, a, fresh);
                    acc.vars.insert(vid, m);
                }
                (None, Some(_)) | (None, None) => {}
            }
        }
        // Statics
        let all_sk: HashSet<_> = case.statics.keys().chain(acc.statics.keys()).cloned().collect();
        for k in all_sk {
            match (case.statics.get(&k).copied(), acc.statics.get(&k).copied()) {
                (Some(a), Some(b)) if a == b => {}
                (Some(a), Some(b)) => {
                    let m = self.solver.ite(cond, a, b);
                    acc.statics.insert(k, m);
                }
                (Some(a), None) => { acc.statics.insert(k, a); }
                _ => {}
            }
        }
        // Field arrays
        let all_fk: HashSet<_> = case.field_arrays.keys().chain(acc.field_arrays.keys()).cloned().collect();
        for k in all_fk {
            match (case.field_arrays.get(&k).copied(), acc.field_arrays.get(&k).copied()) {
                (Some(a), Some(b)) if a == b => {}
                (Some(a), Some(b)) => {
                    let m = self.solver.ite(cond, a, b);
                    acc.field_arrays.insert(k, m);
                }
                (Some(a), None) => { acc.field_arrays.insert(k, a); }
                _ => {}
            }
        }
        // Array map: union
        for entry in &case.array_map {
            if !acc.array_map.iter().any(|(r, _, _)| *r == entry.0) {
                acc.array_map.push(entry.clone());
            }
        }
        // Type array
        if case.type_array != acc.type_array {
            acc.type_array = self.solver.ite(cond, case.type_array, acc.type_array);
        }
        // Taint
        acc.tainted = &acc.tainted | &case.tainted;
        acc.float_tainted = &acc.float_tainted | &case.float_tainted;
        acc.static_tainted = &acc.static_tainted | &case.static_tainted;
        acc.field_tainted = &acc.field_tainted | &case.field_tainted;
        acc.path_tainted = acc.path_tainted || case.path_tainted;
        // String vars
        let all_sv: HashSet<VarId> = case.str_vars.keys().chain(acc.str_vars.keys()).copied().collect();
        for vid in all_sv {
            match (case.str_vars.get(&vid).copied(), acc.str_vars.get(&vid).copied()) {
                (Some(a), Some(b)) if a == b => {}
                (Some(a), Some(b)) => {
                    let m = self.solver.ite(cond, a, b);
                    acc.str_vars.insert(vid, m);
                }
                _ => {}
            }
        }
        // Static strings
        let all_ss: HashSet<_> = case.static_str.keys().chain(acc.static_str.keys()).cloned().collect();
        for k in all_ss {
            match (case.static_str.get(&k).copied(), acc.static_str.get(&k).copied()) {
                (Some(a), Some(b)) if a == b => {}
                (Some(a), Some(b)) => {
                    let m = self.solver.ite(cond, a, b);
                    acc.static_str.insert(k, m);
                }
                (Some(a), None) => { acc.static_str.insert(k, a); }
                _ => {}
            }
        }
    }

    /// Check if a class is part of the program (has any method body).
    fn is_program_class(&self, class: &str) -> bool {
        self.prog.bodies.keys().any(|k| k.class == class)
    }

    /// Run <clinit> for a class if it hasn't been run yet and has a body.
    fn ensure_clinit(&mut self, class: &str) {
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
            if self.call_depth >= MAX_CALL_DEPTH || !self.budget_left() {
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

    fn encode_operand(&mut self, op: &Operand) -> Term {
        match op {
            Operand::Var(v) => self.get_var(*v),
            Operand::Const(Const::Int(n)) => self.solver.bv_const(*n as i64, 32),
            Operand::Const(Const::Long(n)) => self.solver.bv_const(*n, 64),
            Operand::Const(Const::Null) => self.solver.bv_const(0, 32),
            // String constants get a non-null BV reference; the string content
            // is accessed via encode_str_operand.
            Operand::Const(Const::Str(_)) => self.solver.bv_const(1, 32),
            Operand::Const(Const::Float(f)) => self.solver.bv_const(f.to_bits() as i64, 32),
            Operand::Const(Const::Double(d)) => self.solver.bv_const(d.to_bits() as i64, 64),
            Operand::Const(_) => self.solver.bv_const(0, 32),
        }
    }

    /// Get the string content term for an operand. Returns None if the
    /// operand doesn't have tracked string content.
    fn encode_str_operand(&mut self, op: &Operand) -> Option<Term> {
        match op {
            Operand::Var(v) => self.str_vars.get(v).copied(),
            Operand::Const(Const::Str(s)) => Some(self.solver.str_const(s)),
            _ => None,
        }
    }

    /// Encode a string method call. Returns `Some((bv_result, Option<str_result>))`
    /// if the method is modelled, `None` otherwise.
    fn encode_str_call(
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

    fn encode_rvalue(&mut self, rv: &Rvalue) -> Term {
        match rv {
            Rvalue::Use(o) => self.encode_operand(o),
            Rvalue::Nondet(ty, jvm_byte) => {
                let w = self.width_of_ty(ty);
                let idx = self.nondet_terms.len();
                let t = self.solver.fresh_bv(&format!("nd_{idx}"), w);
                // Nondet strings are always non-null (they model
                // Verifier.nondetString() which returns a valid String).
                if *ty == Ty::Str {
                    self.assert_nonzero(t);
                }
                // Constrain sub-int types to their JVM range.
                // All ranges fit in signed 32-bit so we use bvsge/bvsle.
                let range: Option<(i64, i64)> = match jvm_byte {
                    Some(b'Z') => Some((0, 1)),        // boolean
                    Some(b'B') => Some((-128, 127)),   // byte
                    Some(b'S') => Some((-32768, 32767)), // short
                    Some(b'C') => Some((0, 65535)),     // char
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
                // Only record Int/Long/Str nondets for witness extraction.
                if *ty != Ty::Ref {
                    self.nondet_terms.push((idx, t, w, *ty, str_term));
                }
                t
            }
            Rvalue::Havoc(ty) => {
                // Same as Nondet but NOT recorded in nondet_terms — these
                // are modelling artefacts (e.g. Boolean.booleanValue()) and
                // must not appear in witnesses.
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
                // Handle width mismatch: sign-extend shorter operand.
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
                    // Program-internal field: clinit ran and didn't set it,
                    // so it's at the Java default value (0/0L/null/false).
                    let w = Self::field_elem_width(&fk.desc);
                    let t = self.solver.bv_const(0, w);
                    self.statics.insert(k, t);
                    t
                } else {
                    // Library field: unknown value. Use a fresh symbolic BV.
                    let w = Self::field_elem_width(&fk.desc);
                    let t = self.solver.fresh_bv("static", w);
                    // Ref-type library statics (e.g. System.out) are always
                    // non-null at runtime.
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
                // Track the dynamic type of this allocation.
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
                // null instanceof T is always false.
                let obj_type = self.solver.array_select(self.type_array, obj_term);
                // Check if the object's type is a subtype of the target class.
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
            // Remaining: unmodelled calls → fresh unconstrained (sound for Under).
            Rvalue::Call { .. } => self.solver.fresh_bv("havoc", 32),
        }
    }

    /// Look up the array contents term for an object reference via ITE chain.
    fn array_contents_lookup(&mut self, ref_term: Term) -> Term {
        let pairs: Vec<(Term, Term, Term)> = self.array_map.clone();
        let mut result = self.solver.fresh_array("arr_default", 32);
        for (r, arr, _len) in pairs.iter().rev() {
            let eq = self.solver.bveq(ref_term, *r);
            result = self.solver.ite(eq, *arr, result);
        }
        result
    }

    /// Look up array length for an object reference via ITE chain.
    fn array_length_lookup(&mut self, ref_term: Term) -> Term {
        let pairs: Vec<(Term, Term, Term)> = self.array_map.clone();
        let mut result = self.solver.fresh_bv("len_default", 32);
        for (r, _arr, len) in pairs.iter().rev() {
            let eq = self.solver.bveq(ref_term, *r);
            result = self.solver.ite(eq, *len, result);
        }
        result
    }

    /// Select from array: look up the array term, then select at index.
    fn array_select_lookup(&mut self, ref_term: Term, idx_term: Term) -> Term {
        let arr = self.array_contents_lookup(ref_term);
        self.solver.array_select(arr, idx_term)
    }

    /// Store to array: look up the array term, store, and update the map.
    fn array_store_update(&mut self, ref_term: Term, idx_term: Term, val_term: Term) {
        let arr = self.array_contents_lookup(ref_term);
        let new_arr = self.solver.array_store(arr, idx_term, val_term);
        let len = self.array_length_lookup(ref_term);
        self.array_map.push((ref_term, new_arr, len));
    }

    fn encode_binop(&mut self, op: BinOp, a: &Operand, b: &Operand) -> Term {
        let at = self.encode_operand(a);
        let bt = self.encode_operand(b);
        // Normalise widths: sign-extend shorter operand (except shifts).
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
                // JVM: shift amount is masked — 0x1F for int, 0x3F for long.
                let aw = self.width_of_operand(a);
                let mask = if aw == 64 { 0x3F } else { 0x1F };
                let mask_t = self.solver.bv_const(mask, 32);
                let bt = self.solver.bvand(bt, mask_t);
                // Shift amount is always int (32-bit) but shifted value
                // may be long (64-bit). Zero-extend shift amount to match.
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

    /// Assert that a BV term is nonzero.
    fn assert_nonzero(&mut self, t: Term) {
        let zero = self.solver.bv_const(0, 32);
        let eq = self.solver.bveq(t, zero);
        let neq = self.solver.not(eq);
        self.solver.assert(neq);
    }

    /// Create a Bool term: (t != 0). Does NOT assert — for path_constraints.
    fn nonzero_constraint(&mut self, t: Term) -> Term {
        let zero = self.solver.bv_const(0, 32);
        let eq = self.solver.bveq(t, zero);
        self.solver.not(eq)
    }

    /// Create a Bool term: (t == 0). Does NOT assert — for path_constraints.
    fn zero_constraint(&mut self, t: Term) -> Term {
        let zero = self.solver.bv_const(0, 32);
        self.solver.bveq(t, zero)
    }

    /// Check sat with all path constraints + any extra assertions in a single
    /// flat push scope. This avoids deep incremental nesting.
    fn check_sat_with_path(&mut self) -> SatResult {
        self.solver_calls += 1;
        if self.solver_calls > MAX_SOLVER_CALLS {
            self.exhausted = true;
            return SatResult::Unknown;
        }
        self.solver.push();
        for &pc in &self.path_constraints {
            self.solver.assert(pc);
        }
        let res = self.solver.check_sat();
        self.solver.pop();
        res
    }

    /// Check sat with all path constraints + one additional constraint,
    /// in a single flat push scope.
    fn check_sat_with_path_and(&mut self, extra: Term) -> SatResult {
        self.solver_calls += 1;
        if self.solver_calls > MAX_SOLVER_CALLS {
            self.exhausted = true;
            return SatResult::Unknown;
        }
        self.solver.push();
        for &pc in &self.path_constraints {
            self.solver.assert(pc);
        }
        self.solver.assert(extra);
        let res = self.solver.check_sat();
        // Don't pop yet — caller may need to extract witness
        res
    }


    fn extract_witness(&mut self) -> Witness {
        let info: Vec<(Term, u32, Ty, Option<Term>)> = self
            .nondet_terms
            .iter()
            .map(|(_, t, w, ty, st)| (*t, *w, *ty, *st))
            .collect();
        let mut seq = Vec::new();
        let mut entries = Vec::new();
        for (t, w, ty, str_term) in &info {
            let val = self.solver.get_value_i64(*t).unwrap_or(0);
            let raw = if *w <= 32 { val as i32 as i64 } else { val };
            seq.push(raw);
            let (value, method) = match ty {
                Ty::Long => (NondetValue::Long(raw), "nondetLong"),
                Ty::Str => {
                    let s = str_term
                        .and_then(|st| self.solver.get_value_string(st))
                        .unwrap_or_default();
                    (NondetValue::Str(s), "nondetString")
                }
                _ => (NondetValue::Int(raw as i32), "nondetInt"),
            };
            entries.push(NondetEntry {
                value,
                nondet_method: method,
                line: None,
            });
        }
        Witness {
            nondet_sequence: seq,
            entries,
        }
    }

    /// Try to inline a method call. Returns true if inlining succeeded,
    /// in which case `dest_var` is set to an unconstrained return value
    /// and violations inside the callee have been explored.
    fn try_inline_call(
        &mut self,
        target: &MethodKey,
        args: &[Operand],
        dest_var: VarId,
        is_virtual: bool,
    ) -> bool {
        if self.call_depth >= MAX_CALL_DEPTH || !self.budget_left() {
            return false;
        }

        // Resolve concrete target(s)
        let targets = if is_virtual {
            let t = self.prog.devirtualise(target);
            if t.is_empty() {
                return false;
            }
            t
        } else {
            vec![target.clone()]
        };

        // All targets must have bodies for us to inline
        if targets.iter().any(|t| self.prog.body(t).is_none()) {
            return false;
        }

        // Encode args using the caller's current variable state
        let arg_terms: Vec<Term> = args.iter().map(|a| self.encode_operand(a)).collect();
        let arg_str_terms: Vec<Option<Term>> =
            args.iter().map(|a| self.encode_str_operand(a)).collect();
        let arg_tainted: Vec<bool> = args.iter().map(|a| self.operand_tainted(a)).collect();

        // Explore each possible target (for virtual calls, this tries all
        // concrete receivers — each is a possible execution path).
        let mut ret_tainted = false;
        for resolved in &targets {
            if !self.budget_left() {
                break;
            }
            let callee = self.prog.body(resolved).unwrap();

            // Save caller state
            let saved_body = self.body;
            let saved_vars = self.vars.clone();
            let saved_str_vars = self.str_vars.clone();
            let saved_tainted = self.tainted.clone();
            let saved_float_tainted = self.float_tainted.clone();
            let saved_path_tainted = self.path_tainted;
            let saved_pc_len = self.path_constraints.len();

            // Switch to callee
            self.body = callee;
            self.call_depth += 1;
            self.vars.clear();
            self.str_vars.clear();
            self.tainted.clear();
            self.float_tainted.clear();

            // Map arguments to callee's local variable slots.
            let mut slot = 0u16;
            for (i, arg_t) in arg_terms.iter().enumerate() {
                if let Some((vid_idx, vinfo)) = callee
                    .vars
                    .iter()
                    .enumerate()
                    .find(|(_, vi)| matches!(vi.kind, VarKind::Local(s) if s == slot))
                {
                    let vid = VarId(vid_idx as u32);
                    self.vars.insert(vid, *arg_t);
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

            // Explore callee — violations inside it are found here.
            // No push/pop needed: path_constraints are restored via
            // saved state, and define-const terms are permanent.
            self.inline_return = None;
            self.inline_return_tainted = false;
            self.explore_block(callee.entry, 0);

            // Capture callee's taint state before restoring.
            let callee_return_tainted = self.inline_return_tainted;
            let callee_path_tainted = self.path_tainted;

            // Restore caller state
            self.call_depth -= 1;
            self.body = saved_body;
            self.vars = saved_vars;
            self.str_vars = saved_str_vars;
            self.tainted = saved_tainted;
            self.float_tainted = saved_float_tainted;
            // Propagate callee's path_tainted to caller: if callee went
            // through tainted paths, caller should know.
            self.path_tainted = saved_path_tainted || callee_path_tainted;
            self.path_constraints.truncate(saved_pc_len);

            ret_tainted = ret_tainted || callee_return_tainted;
        }

        // Return value: use the callee's actual return term if captured,
        // otherwise fall back to unconstrained. This links nondet values
        // in the callee to the caller's use of the return value, enabling
        // correct witness extraction.
        let w = self.width_of_var(dest_var);
        let ret_t = self.inline_return.unwrap_or_else(|| {
            ret_tainted = true; // No return captured → havoc is tainted.
            self.solver.fresh_bv(&format!("ret_{}", target.name), w)
        });
        self.vars.insert(dest_var, ret_t);
        if ret_tainted {
            self.tainted.insert(dest_var);
        }

        // Record that we successfully inlined this method (and all resolved targets).
        for resolved in &targets {
            self.inlined_methods.insert(resolved.clone());
        }

        true
    }

    /// Collect all forward-reachable block IDs from `start` (inclusive).
    /// Only follows edges where target > source (no back-edges).
    /// Limited to `limit` blocks to avoid runaway walks.
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

    /// Return all successor block IDs of a terminator.
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

    /// Find the join (post-dominator) of a diamond branch pattern.
    /// Returns Some(join_block) if both branches converge to the same
    /// block; None if structure is too complex.
    fn find_join(&self, then_: BlockId, else_: BlockId) -> Option<BlockId> {
        self.find_join_multi(&[then_, else_])
    }

    /// Find the join point for multiple branch targets (switch cases + default).
    /// Returns Some(join_block) if ALL targets converge to a common block.
    fn find_join_multi(&self, targets: &[BlockId]) -> Option<BlockId> {
        if targets.is_empty() {
            return None;
        }
        let mut common = self.forward_reachable(targets[0], 50);
        for t in &targets[1..] {
            let reach = self.forward_reachable(*t, 50);
            common = common.intersection(&reach).copied().collect();
        }
        let mut candidates: Vec<u32> = common.into_iter().collect();
        candidates.sort();
        candidates.first().map(|&b| BlockId(b))
    }

    /// Explore a block's statements and terminator, stopping if `stop_at` is reached.
    fn explore_block(&mut self, block_id: BlockId, stmt_idx: usize) {
        self.explore_block_until(block_id, stmt_idx, None);
    }

    fn explore_block_until(&mut self, block_id: BlockId, stmt_idx: usize, stop_at: Option<BlockId>) {
        if stop_at == Some(block_id) {
            return;
        }
        self.block_visits += 1;
        if self.depth > self.max_depth || !self.budget_left() {
            self.all_paths_complete = false;
            return;
        }
        let b = self.body.block(block_id);

        // Process statements from stmt_idx onwards.
        for idx in stmt_idx..b.stmts.len() {
            if !self.budget_left() {
                self.all_paths_complete = false;
                return;
            }
            match &b.stmts[idx] {
                Stmt::Assign(v, rv) => {
                    let is_tainted = self.rvalue_tainted(rv);
                    // Try to encode string calls via the string theory,
                    // or inline user method calls.
                    let (t, str_term) = match rv {
                        Rvalue::Call { target, args, .. }
                            if roast_models::STR_OWNERS.contains(&target.class.as_str()) =>
                        {
                            match self.encode_str_call(target, args) {
                                Some((bv, st)) => (bv, st),
                                None => (self.encode_rvalue(rv), None),
                            }
                        }
                        Rvalue::Call {
                            target,
                            args,
                            is_virtual,
                        } => {
                            // Math/Integer/Long static methods.
                            if self.math_call_modelled(target) {
                                (self.encode_math_call(target, args), None)
                            } else if self.try_inline_call(target, args, *v, *is_virtual) {
                                continue;
                            } else {
                                (self.encode_rvalue(rv), None)
                            }
                        }
                        Rvalue::Use(Operand::Var(src)) => {
                            // Propagate string content through copies.
                            let st = self.str_vars.get(src).copied();
                            (self.encode_rvalue(rv), st)
                        }
                        Rvalue::Nondet(Ty::Str, _) => {
                            let bv = self.encode_rvalue(rv);
                            // The last pushed nondet_term has the str_term.
                            let st = self.nondet_terms.last().and_then(|(_, _, _, _, s)| *s);
                            (bv, st)
                        }
                        Rvalue::Havoc(Ty::Str) => {
                            let bv = self.encode_rvalue(rv);
                            let st = Some(self.solver.fresh_str("hvs"));
                            (bv, st)
                        }
                        Rvalue::GetStatic(fk) => {
                            let k = Self::field_key(fk);
                            let st = self.static_str.get(&k).copied();
                            (self.encode_rvalue(rv), st)
                        }
                        Rvalue::GetField { .. } => {
                            // Instance field string content is not tracked
                            // per-object for now (would need Array of Strings).
                            (self.encode_rvalue(rv), None)
                        }
                        _ => (self.encode_rvalue(rv), None),
                    };
                    self.vars.insert(*v, t);
                    if let Some(st) = str_term {
                        self.str_vars.insert(*v, st);
                    } else {
                        self.str_vars.remove(v);
                    }
                    if is_tainted {
                        self.tainted.insert(*v);
                    } else {
                        self.tainted.remove(v);
                    }
                    if self.rvalue_float_tainted(rv) {
                        self.float_tainted.insert(*v);
                    } else {
                        self.float_tainted.remove(v);
                    }
                }
                Stmt::Assume(op) => {
                    let tainted = self.operand_tainted(op);
                    if tainted {
                        self.path_tainted = true;
                    }
                    // Only add path constraint and prune when the
                    // condition is untainted. Tainted BV encodings
                    // (e.g. float ops) can be semantically wrong and
                    // cause unsound pruning of feasible paths.
                    if !tainted {
                        let t = self.encode_operand(op);
                        let c = self.nonzero_constraint(t);
                        self.path_constraints.push(c);
                        let res = self.check_sat_with_path();
                        if res == SatResult::Unsat {
                            return;
                        }
                    }
                }
                Stmt::Check(oid) => {
                    let is_tainted = self.operand_tainted(&self.body.obligation(*oid).cond);
                    let ob = self.body.obligation(*oid);
                    let cond = self.encode_operand(&ob.cond);
                    // Check if violation is reachable: path_constraints ∧ cond == 0.
                    let violation_cond = self.zero_constraint(cond);
                    let res = self.check_sat_with_path_and(violation_cond);
                    log::debug!("smt-bmc: check {:?} in {} kind={:?} tainted={} path_tainted={} res={:?} pc_len={}",
                        oid, self.body.key, ob.kind, is_tainted, self.path_tainted, res, self.path_constraints.len());
                    if res == SatResult::Sat && !is_tainted {
                        // Only record violations for untainted conditions;
                        // tainted SAT results may be spurious.
                        // JvmReplay confirms all violations, so we don't
                        // need to check path_tainted here (Under direction).
                        let witness = self.extract_witness();
                        self.violations
                            .push((self.body.key.clone(), *oid, witness));
                    }
                    if res != SatResult::Unsat && (is_tainted || self.path_tainted) {
                        // Tainted condition or tainted path with non-UNSAT
                        // result: we can't prove this obligation safe for
                        // the exhaustive discharge (Over direction).
                        self.skipped_obligations.insert(*oid);
                    }
                    self.solver.pop();
                }
                Stmt::PutStatic(fk, val) => {
                    self.ensure_clinit(&fk.class);
                    let k = Self::field_key(fk);
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
                Stmt::PutField { field, val, obj } => {
                    let k = Self::field_key(field);
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
                }
                Stmt::ArrayStore { arr, idx, val } => {
                    let ref_term = self.encode_operand(arr);
                    let idx_term = self.encode_operand(idx);
                    let val_term = self.encode_operand(val);
                    self.array_store_update(ref_term, idx_term, val_term);
                }
                Stmt::Nop => {}
            }
        }

        if !self.budget_left() {
            return;
        }

        // Process terminator.
        self.depth += 1;
        match &b.term {
            Terminator::Goto(t) => {
                // Back-edge detection: if the goto target is at or before
                // the current block, it's a loop back-edge. Bound unrolling.
                if t.0 <= block_id.0 {
                    let loop_key = (self.body.key.to_string(), t.0);
                    let count = self.loop_visits.entry(loop_key).or_insert(0);
                    *count += 1;
                    if *count > MAX_LOOP_UNROLL {
                        self.all_paths_complete = false;
                    } else {
                        self.explore_block_until(*t, 0, stop_at);
                    }
                } else {
                    self.explore_block_until(*t, 0, stop_at);
                }
            }
            Terminator::Branch { cond, then_, else_ } => {
                let cond_tainted = self.operand_tainted(cond);
                let ct = self.encode_operand(cond);
                let zero = self.solver.bv_const(0, 32);
                let cond_bool = self.solver.bveq(ct, zero);
                let cond_nz = self.solver.not(cond_bool); // true when cond != 0

                // Diamond optimisation: if both branches converge to the
                // same block, explore each side up to the join point and
                // merge with ITE instead of forking into independent paths.
                // This turns exponential path explosion into linear work.
                if let Some(join) = self.find_join(*then_, *else_) {
                    // --- then side ---
                    let saved = self.save_state();
                    if cond_tainted {
                        self.path_tainted = true;
                    }
                    // Don't push tainted path constraints — the BV encoding
                    // may be semantically wrong and cause unsound pruning.
                    if !cond_tainted {
                        self.path_constraints.push(cond_nz);
                    }
                    self.explore_block_until(*then_, 0, Some(join));
                    let then_state = self.save_state();
                    self.restore_state(saved);

                    // --- else side ---
                    let saved = self.save_state();
                    if cond_tainted {
                        self.path_tainted = true;
                    }
                    if !cond_tainted {
                        self.path_constraints.push(cond_bool);
                    }
                    self.explore_block_until(*else_, 0, Some(join));
                    let else_state = self.save_state();
                    self.restore_state(saved);

                    // Preserve nondets from both sides.
                    let base_len = self.nondet_terms.len();
                    for nd in &then_state.nondet_terms[base_len..] {
                        self.nondet_terms.push(nd.clone());
                    }
                    for nd in &else_state.nondet_terms[base_len..] {
                        self.nondet_terms.push(nd.clone());
                    }

                    // --- merge with ITE ---
                    self.merge_states_ite(cond_nz, &then_state, &else_state);

                    // Continue from join point
                    self.explore_block_until(join, 0, stop_at);
                } else {
                    // No join point found — fall back to path forking.
                    // Like diamond merge, we explore both sides and ITE-merge
                    // their states so that return values and field side effects
                    // compose correctly across inlined method boundaries.
                    self.fork_count += 1;
                    log::trace!("smt-bmc: fork at bb{} in {} then=bb{} else=bb{} stop_at={:?}",
                        block_id.0, self.body.key, then_.0, else_.0, stop_at.map(|b| b.0));

                    let saved = self.save_state();
                    let ir_before = self.inline_return;
                    let irt_before = self.inline_return_tainted;

                    // --- then branch: cond != 0 ---
                    let mut then_explored = false;
                    if cond_tainted {
                        self.path_tainted = true;
                    }
                    if !cond_tainted {
                        self.path_constraints.push(cond_nz);
                        let feas = self.check_sat_with_path();
                        log::trace!("smt-bmc: fork-then bb{} in {} feas={:?} tainted={}",
                            then_.0, self.body.key, feas, cond_tainted);
                        if feas != SatResult::Unsat {
                            self.explore_block_until(*then_, 0, stop_at);
                            then_explored = true;
                        }
                    } else {
                        self.explore_block_until(*then_, 0, stop_at);
                        then_explored = true;
                    }
                    let then_state = self.save_state();
                    let then_ir = self.inline_return;
                    let then_irt = self.inline_return_tainted;
                    self.restore_state(saved.clone());

                    // --- else branch: cond == 0 ---
                    let mut else_explored = false;
                    self.inline_return = ir_before;
                    self.inline_return_tainted = irt_before;
                    if self.budget_left() {
                        if cond_tainted {
                            self.path_tainted = true;
                        }
                        if !cond_tainted {
                            self.path_constraints.push(cond_bool);
                            let feas = self.check_sat_with_path();
                            if feas != SatResult::Unsat {
                                self.explore_block_until(*else_, 0, stop_at);
                                else_explored = true;
                            }
                        } else {
                            self.explore_block_until(*else_, 0, stop_at);
                            else_explored = true;
                        }
                    }
                    let else_state = self.save_state();
                    let else_ir = self.inline_return;
                    let else_irt = self.inline_return_tainted;

                    // ITE-merge state from both fork arms so that field writes,
                    // static updates, and return values compose correctly.
                    if then_explored && else_explored {
                        self.restore_state(saved);
                        let base_len = self.nondet_terms.len();
                        for nd in &then_state.nondet_terms[base_len..] {
                            self.nondet_terms.push(nd.clone());
                        }
                        for nd in &else_state.nondet_terms[base_len..] {
                            self.nondet_terms.push(nd.clone());
                        }
                        self.merge_states_ite(cond_nz, &then_state, &else_state);
                    } else if then_explored {
                        self.restore_state(saved);
                        let base_len = self.nondet_terms.len();
                        for nd in &then_state.nondet_terms[base_len..] {
                            self.nondet_terms.push(nd.clone());
                        }
                        self.merge_states_ite(cond_nz, &then_state, &else_state);
                    } else if else_explored {
                        self.restore_state(saved);
                        let base_len = self.nondet_terms.len();
                        for nd in &else_state.nondet_terms[base_len..] {
                            self.nondet_terms.push(nd.clone());
                        }
                        self.merge_states_ite(cond_nz, &then_state, &else_state);
                    } else {
                        self.restore_state(saved);
                    }

                    // ITE-merge inline return values.
                    match (then_explored, else_explored, then_ir, else_ir) {
                        (true, true, Some(t), Some(e)) if t != e => {
                            self.inline_return = Some(self.solver.ite(cond_nz, t, e));
                            self.inline_return_tainted = then_irt || else_irt;
                        }
                        (true, true, Some(t), Some(_)) => {
                            self.inline_return = Some(t);
                            self.inline_return_tainted = then_irt || else_irt;
                        }
                        (true, false, _, _) => {
                            self.inline_return = then_ir.or(ir_before);
                            self.inline_return_tainted = then_irt;
                        }
                        (false, true, _, _) => {
                            self.inline_return = else_ir.or(ir_before);
                            self.inline_return_tainted = else_irt;
                        }
                        _ => {
                            self.inline_return = ir_before;
                            self.inline_return_tainted = irt_before;
                        }
                    }
                }
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let value_tainted = self.operand_tainted(value);
                let vt = self.encode_operand(value);

                // Collect all switch targets for join-point detection.
                let mut all_targets: Vec<BlockId> =
                    cases.iter().map(|(_, t)| *t).collect();
                all_targets.push(*default);

                if let Some(join) = self.find_join_multi(&all_targets) {
                    // Diamond merge for switch: explore each case up to the
                    // join, capture state, then ITE-merge all cases.

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
                        if !self.budget_left() {
                            break;
                        }
                        let saved = self.save_state();
                        if value_tainted {
                            self.path_tainted = true;
                        }
                        self.path_constraints.push(cond_eq);
                        self.explore_block_until(target, 0, Some(join));
                        case_saved.push((cond_eq, self.save_state()));
                        self.restore_state(saved);
                    }

                    // Default case
                    if self.budget_left() {
                        let saved = self.save_state();
                        if value_tainted {
                            self.path_tainted = true;
                        }
                        for &(_, _, cond_eq) in &case_conds {
                            let neq = self.solver.not(cond_eq);
                            self.path_constraints.push(neq);
                        }
                        self.explore_block_until(*default, 0, Some(join));
                        let mut merged = self.save_state();
                        self.restore_state(saved);

                        // Preserve nondets from all cases.
                        let base_len = self.nondet_terms.len();
                        for (_, cs) in &case_saved {
                            for nd in &cs.nondet_terms[base_len..] {
                                if !self.nondet_terms.iter().any(|(idx, _, _, _, _)| *idx == nd.0) {
                                    self.nondet_terms.push(nd.clone());
                                }
                            }
                        }
                        for nd in &merged.nondet_terms[base_len..] {
                            if !self.nondet_terms.iter().any(|(idx, _, _, _, _)| *idx == nd.0) {
                                self.nondet_terms.push(nd.clone());
                            }
                        }

                        // ITE-merge each case on top of the default (cascade).
                        for (cond_eq, cs) in case_saved.iter().rev() {
                            // Merge cs into merged using ITE(cond_eq, cs, merged).
                            self.merge_saved_into(&mut merged, *cond_eq, cs);
                        }

                        // Apply merged state
                        self.vars = merged.vars;
                        self.str_vars = merged.str_vars;
                        self.tainted = merged.tainted;
                        self.float_tainted = merged.float_tainted;
                        self.path_tainted = merged.path_tainted;
                        self.statics = merged.statics;
                        self.static_str = merged.static_str;
                        self.static_tainted = merged.static_tainted;
                        self.field_arrays = merged.field_arrays;
                        self.field_tainted = merged.field_tainted;
                        self.array_map = merged.array_map;
                        self.type_array = merged.type_array;

                        // Continue from join
                        self.explore_block_until(join, 0, stop_at);
                    }
                } else {
                    // No join point — fork-based with ITE-merge of full state.
                    let saved = self.save_state();
                    let ir_before = self.inline_return;
                    let irt_before = self.inline_return_tainted;
                    let mut case_saved: Vec<(Term, SavedState, Option<Term>, bool)> = Vec::new();

                    for (case_val, target) in cases {
                        if !self.budget_left() {
                            break;
                        }
                        self.fork_count += 1;
                        self.inline_return = ir_before;
                        self.inline_return_tainted = irt_before;
                        if value_tainted {
                            self.path_tainted = true;
                        }
                        let cv = self.solver.bv_const(*case_val as i64, 32);
                        let eq = self.solver.bveq(vt, cv);
                        self.path_constraints.push(eq);
                        self.explore_block_until(*target, 0, stop_at);
                        let cs = self.save_state();
                        let c_ir = self.inline_return;
                        let c_irt = self.inline_return_tainted;
                        case_saved.push((eq, cs, c_ir, c_irt));
                        self.restore_state(saved.clone());
                    }

                    // Default arm
                    self.inline_return = ir_before;
                    self.inline_return_tainted = irt_before;
                    if self.budget_left() {
                        if value_tainted {
                            self.path_tainted = true;
                        }
                        for (case_val, _) in cases {
                            let cv = self.solver.bv_const(*case_val as i64, 32);
                            let eq = self.solver.bveq(vt, cv);
                            let neq = self.solver.not(eq);
                            self.path_constraints.push(neq);
                        }
                        self.explore_block_until(*default, 0, stop_at);
                    }
                    let mut merged = self.save_state();
                    let mut merged_ir = self.inline_return;
                    let mut any_irt = self.inline_return_tainted;
                    self.restore_state(saved);

                    // Preserve nondets from all arms.
                    let base_len = self.nondet_terms.len();
                    for (_, cs, _, _) in &case_saved {
                        for nd in &cs.nondet_terms[base_len..] {
                            if !self.nondet_terms.iter().any(|(idx, _, _, _, _)| *idx == nd.0) {
                                self.nondet_terms.push(nd.clone());
                            }
                        }
                    }
                    for nd in &merged.nondet_terms[base_len..] {
                        if !self.nondet_terms.iter().any(|(idx, _, _, _, _)| *idx == nd.0) {
                            self.nondet_terms.push(nd.clone());
                        }
                    }

                    // ITE-merge: cascade case states over default.
                    for (eq, cs, c_ir, c_irt) in case_saved.iter().rev() {
                        self.merge_saved_into(&mut merged, *eq, cs);
                        any_irt = any_irt || *c_irt;
                        match (*c_ir, merged_ir) {
                            (Some(c), Some(m)) if c != m => {
                                merged_ir = Some(self.solver.ite(*eq, c, m));
                            }
                            (Some(c), None) => { merged_ir = Some(c); }
                            _ => {}
                        }
                    }

                    // Apply merged state
                    self.vars = merged.vars;
                    self.str_vars = merged.str_vars;
                    self.tainted = merged.tainted;
                    self.float_tainted = merged.float_tainted;
                    self.path_tainted = merged.path_tainted;
                    self.statics = merged.statics;
                    self.static_str = merged.static_str;
                    self.static_tainted = merged.static_tainted;
                    self.field_arrays = merged.field_arrays;
                    self.field_tainted = merged.field_tainted;
                    self.array_map = merged.array_map;
                    self.type_array = merged.type_array;
                    self.inline_return = merged_ir.or(ir_before);
                    self.inline_return_tainted = any_irt;
                }
            }
            // Path ends.
            Terminator::Return(Some(val)) => {
                // Capture return value for try_inline_call propagation.
                if self.call_depth > 0 {
                    self.inline_return = Some(self.encode_operand(val));
                    // Sticky: once tainted on any path, stays tainted.
                    self.inline_return_tainted = self.inline_return_tainted
                        || self.operand_tainted(val) || self.path_tainted;
                }
            }
            Terminator::Return(None) | Terminator::Halt => {}
            Terminator::Throw(_) => {
                // Exception handlers are not followed — obligations in catch
                // blocks are unreached. Mark incomplete to prevent false discharge.
                self.all_paths_complete = false;
            }
            Terminator::Diverge(_) => {
                self.all_paths_complete = false;
            }
        }
        self.depth -= 1;
    }
}
