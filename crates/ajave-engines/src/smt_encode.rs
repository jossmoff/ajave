//! SSA-based SMT encoder for method bodies.
//!
//! Encodes a `Body` as a single formula over bitvectors: every path through
//! the CFG is one disjunct, and reaching definitions are joined at merge
//! points with `ite`.
//!
//! # Completeness is part of the result
//!
//! An `Encoding` is only a faithful description of the body when
//! [`Encoding::complete`] is true. The encoder walks each block once, so it
//! describes **one pass** through any loop, and it does not model exceptional
//! edges or unlifted instructions. A caller that wants to conclude "no
//! violation is possible" — as opposed to "no violation on the paths I
//! encoded" — must check the flag.
//!
//! This is not a hypothetical. Both defects below produced a claimed proof for
//! a program that violates its assertion, and both are pinned by tests in
//! `kinduction.rs` (#76):
//!
//! * **Back-edges.** A back-edge targets a block that has already been
//!   processed, so it is dropped. The formula covers one iteration, on which
//!   a property that first fails on the second iteration still holds.
//! * **Merge points.** Reaching definitions used to be threaded through a
//!   single map that each block overwrote in turn, so a join read whatever
//!   the last-processed predecessor assigned rather than an `ite` over both.
//!   The violating branch was absent from the formula entirely. That one is
//!   *fixed* here rather than reported; the traversal below merges properly.
//!
//! Reads of the heap are fresh unconstrained values. That is sound in the
//! direction that matters — an arbitrary value covers whatever the real heap
//! holds — but it means no property that depends on a stored value is
//! provable. Writes are correspondingly dropped.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ajave_core::smt::{Solver, Term};
use ajave_ir::*;

/// Reaching definitions at a program point, keyed by variable.
type VarMap = BTreeMap<VarId, Term>;

/// An allocation site: the index of a `NewArray` in encoding order.
type Site = u32;

/// Which array allocation a reference-typed variable holds, when the encoder
/// can tell. `None` covers both "not an array" and "could be more than one".
type PtsMap = BTreeMap<VarId, Site>;

/// A symbolic heap, split by field and by allocation site.
///
/// This is Burstall–Bornat field splitting: one SMT array per *field*, indexed
/// by the object reference, rather than one array for all of memory. Two
/// objects are separated for free because their references are distinct terms,
/// so no alias analysis is needed to keep `p.f` and `q.g` apart, and the
/// solver still decides `p.f` against `q.f` on the references themselves.
///
/// Java arrays cannot be handled that way: the natural index is the pair
/// (reference, element index) and `Solver::fresh_array` fixes the index width
/// at 32 bits, so the pair does not fit. They are split by allocation site
/// instead, which needs the points-to map above. A store through a reference
/// whose site is unknown havocs every array — sound, and the reason a
/// completeness flag is not needed for it.
#[derive(Clone, Default)]
struct Heap {
    /// Element contents per allocation site, `(Array BV32 BV_w)`.
    arrays: BTreeMap<Site, Term>,
    /// `arraylength` per allocation site.
    lengths: BTreeMap<Site, Term>,
    /// One map per instance field, indexed by object reference.
    fields: BTreeMap<FieldKey, Term>,
    /// Static fields are single cells, not maps.
    statics: BTreeMap<FieldKey, Term>,
}

/// Everything that flows along a control-flow edge.
#[derive(Clone, Default)]
struct State {
    vars: VarMap,
    pts: PtsMap,
    heap: Heap,
}

/// Result of encoding one method body.
pub struct Encoding {
    /// For each obligation the encoder reached: the term that is true iff the
    /// obligation's safety condition is violated on some encoded path.
    ///
    /// An obligation that is in the body but missing here was **not encoded**
    /// — it sits behind an edge this encoder does not follow. Absence is not
    /// evidence of safety.
    pub violation_terms: HashMap<ObligationId, Term>,

    /// Disjunction of the path conditions of all returning blocks.
    pub reach_term: Term,

    /// Whether the encoding covers every execution of the body.
    ///
    /// False when the CFG has a back-edge (only one iteration is encoded),
    /// when a reachable block ends in `Diverge` (an instruction the lifter
    /// could not model), or when a reachable block has exceptional successors
    /// (handler code is not encoded). A `false` here forbids concluding
    /// safety from an UNSAT violation term.
    pub complete: bool,
}

/// Where allocation addresses start.
///
/// Not 1: `Const::Str` encodes as the literal 1, and an allocation sharing
/// that value would alias every string constant in the body. Not 0 either,
/// which is null. The exact value is arbitrary above those two.
const FIRST_ADDR: i64 = 0x1000;

/// Width of a type in bits for bitvector encoding.
fn width_of(ty: &Ty) -> u32 {
    match ty {
        Ty::Long | Ty::Double => 64,
        _ => 32,
    }
}

/// Width of a field from its JVM descriptor (e.g. "J" → 64, "I" → 32).
fn field_width(desc: &str) -> u32 {
    match desc.as_bytes().first() {
        Some(b'J') | Some(b'D') => 64,
        _ => 32,
    }
}

/// Width of a method's return type from its JVM descriptor (e.g. "(I)J" → 64).
fn return_width(desc: &str) -> u32 {
    let after_paren = desc.split(')').nth(1).unwrap_or("V");
    match after_paren.as_bytes().first() {
        Some(b'J') | Some(b'D') => 64,
        _ => 32,
    }
}

/// Successors of a block along normal (non-exceptional) control flow.
fn successors(block: &Block) -> Vec<BlockId> {
    match &block.term {
        Terminator::Goto(t) => vec![*t],
        Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
        Terminator::Switch { cases, default, .. } => {
            let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
            v.push(*default);
            v
        }
        Terminator::Return(_) | Terminator::Halt
        | Terminator::Throw(_) | Terminator::Diverge(_) => vec![],
    }
}

/// Reverse post-order over forward edges, plus the set of back-edges found.
///
/// An edge to a block that is grey — on the current DFS stack — closes a
/// cycle. Processing the returned order guarantees every *forward* predecessor
/// of a block is encoded before the block itself, which is what makes the
/// merge at a join point well defined.
fn rpo_and_back_edges(body: &Body) -> (Vec<BlockId>, BTreeSet<(BlockId, BlockId)>) {
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        White,
        Grey,
        Black,
    }
    let n = body.blocks.len();
    let mut colour = vec![Colour::White; n];
    let mut post = Vec::with_capacity(n);
    let mut back = BTreeSet::new();

    // Explicit stack: bytecode from a deeply nested method can otherwise
    // overflow a recursive DFS.
    let mut stack: Vec<(BlockId, usize)> = vec![(body.entry, 0)];
    if let Some(c) = colour.get_mut(body.entry.0 as usize) {
        *c = Colour::Grey;
    }
    while let Some((bid, next)) = stack.pop() {
        let idx = bid.0 as usize;
        let Some(block) = body.blocks.get(idx) else { continue };
        let succs = successors(block);
        if next < succs.len() {
            stack.push((bid, next + 1));
            let s = succs[next];
            match colour.get(s.0 as usize) {
                Some(Colour::White) => {
                    colour[s.0 as usize] = Colour::Grey;
                    stack.push((s, 0));
                }
                Some(Colour::Grey) => {
                    back.insert((bid, s));
                }
                _ => {}
            }
        } else {
            colour[idx] = Colour::Black;
            post.push(bid);
        }
    }
    post.reverse();
    (post, back)
}

/// What a region walk produced.
struct RegionOut {
    /// Edges leaving the region: (from, to, path condition, state).
    exits: Vec<(BlockId, BlockId, Term, State)>,
    /// Path conditions of blocks that returned inside the region.
    returns: Vec<Term>,
    violations: HashMap<ObligationId, Term>,
    complete: bool,
}

/// Encode the blocks of `members`, entering at `entry` in `in_state`.
///
/// A successor outside `members`, **or equal to `entry`**, is an exit rather
/// than an internal edge. Making the entry an exit is what lets a loop body be
/// encoded as a transition: the back-edge to the header leaves the region and
/// its state becomes the next iteration's input, instead of being dropped the
/// way a whole-body walk drops it.
///
/// The region must be acyclic once those edges are removed. An internal cycle
/// — a nested loop — clears `complete`.
fn walk_region(
    env: &mut Env,
    body: &Body,
    members: &BTreeSet<BlockId>,
    entry: BlockId,
    in_state: State,
    in_pc: Term,
) -> RegionOut {
    // DFS post-order over internal edges only, plus internal-cycle detection.
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        White,
        Grey,
        Black,
    }
    let internal = |from: BlockId, to: BlockId| members.contains(&to) && to != entry;
    let mut colour: BTreeMap<BlockId, Colour> =
        members.iter().map(|b| (*b, Colour::White)).collect();
    let mut post = Vec::new();
    let mut complete = true;
    let mut stack = vec![(entry, 0usize)];
    colour.insert(entry, Colour::Grey);
    while let Some((bid, next)) = stack.pop() {
        let Some(block) = body.blocks.get(bid.0 as usize) else { continue };
        let succs: Vec<BlockId> = successors(block)
            .into_iter()
            .filter(|t| internal(bid, *t))
            .collect();
        if next < succs.len() {
            stack.push((bid, next + 1));
            let t = succs[next];
            match colour.get(&t).copied() {
                Some(Colour::White) => {
                    colour.insert(t, Colour::Grey);
                    stack.push((t, 0));
                }
                // A cycle that does not go through the region entry: a nested
                // loop. One pass through it is not the whole story.
                Some(Colour::Grey) => complete = false,
                _ => {}
            }
        } else {
            colour.insert(bid, Colour::Black);
            post.push(bid);
        }
    }
    post.reverse();

    let mut incoming: BTreeMap<BlockId, Vec<(Term, State)>> = BTreeMap::new();
    incoming.insert(entry, vec![(in_pc, in_state)]);
    let mut out = RegionOut {
        exits: Vec::new(),
        returns: Vec::new(),
        violations: HashMap::new(),
        complete,
    };

    for bid in post {
        let Some(edges) = incoming.remove(&bid) else { continue };
        let Some(block) = body.blocks.get(bid.0 as usize) else { continue };
        let (mut pc, state) = env.merge(edges);
        env.vars = state.vars;
        env.pts = state.pts;
        env.heap = state.heap;

        // Handler code is not encoded, so a block that can transfer into one
        // has successors this formula does not describe.
        if !block.exceptional.is_empty() {
            out.complete = false;
        }

        for stmt in &block.stmts {
            match stmt {
                // A monitor imposes no constraint on a sequential encoding.
                Stmt::MonitorEnter(_) | Stmt::MonitorExit(_) => {}
                Stmt::Assign(vid, rv) => {
                    let (t, site) = env.encode_rvalue(rv);
                    env.vars.insert(*vid, t);
                    match site {
                        Some(s) => env.pts.insert(*vid, s),
                        // Overwriting a reference must clear its old site, or
                        // a later store would update the array it used to
                        // point at.
                        None => env.pts.remove(vid),
                    };
                }
                Stmt::Assume(op) => {
                    let t = env.encode_operand(op);
                    let zero = env.solver.bv_const(0, 32);
                    let is_zero = env.solver.bveq(t, zero);
                    let nz = env.solver.not(is_zero);
                    pc = env.solver.and(pc, nz);
                }
                Stmt::Check(oid) => {
                    let ob = body.obligation(*oid);
                    let cond = env.encode_operand(&ob.cond);
                    let zero = env.solver.bv_const(0, 32);
                    let is_zero = env.solver.bveq(cond, zero);
                    let violation = env.solver.and(pc, is_zero);
                    out.violations.insert(*oid, violation);
                }
                Stmt::ArrayStore { arr, idx, val } => {
                    let v = env.encode_operand(val);
                    let i = env.encode_operand(idx);
                    match env.site_of(arr) {
                        Some(site) => {
                            let map = env.array_map(site, 32);
                            let updated = env.solver.array_store(map, i, v);
                            env.heap.arrays.insert(site, updated);
                        }
                        // The store may land in any array, so no array's
                        // contents survive it.
                        None => env.havoc_arrays(),
                    }
                }
                Stmt::PutField { obj, field, val } => {
                    let w = field_width(&field.desc);
                    let map = env.field_map(field, w);
                    let r = env.encode_operand(obj);
                    let v = env.encode_operand(val);
                    let updated = env.solver.array_store(map, r, v);
                    env.heap.fields.insert(field.clone(), updated);
                }
                Stmt::PutStatic(fk, val) => {
                    let v = env.encode_operand(val);
                    env.heap.statics.insert(fk.clone(), v);
                }
                Stmt::Nop => {}
            }
        }

        let snapshot = |env: &Env| State {
            vars: env.vars.clone(),
            pts: env.pts.clone(),
            heap: env.heap.clone(),
        };
        let mut send = |env: &mut Env,
                        incoming: &mut BTreeMap<BlockId, Vec<(Term, State)>>,
                        out: &mut RegionOut,
                        target: BlockId,
                        edge_pc: Term| {
            if internal(bid, target) {
                incoming
                    .entry(target)
                    .or_default()
                    .push((edge_pc, snapshot(env)));
            } else {
                out.exits.push((bid, target, edge_pc, snapshot(env)));
            }
        };

        match &block.term {
            Terminator::Goto(target) => send(env, &mut incoming, &mut out, *target, pc),
            Terminator::Branch { cond, then_, else_ } => {
                let ct = env.encode_operand(cond);
                let zero = env.solver.bv_const(0, 32);
                let is_zero = env.solver.bveq(ct, zero);
                let is_nz = env.solver.not(is_zero);
                let then_pc = env.solver.and(pc, is_nz);
                let else_pc = env.solver.and(pc, is_zero);
                send(env, &mut incoming, &mut out, *then_, then_pc);
                send(env, &mut incoming, &mut out, *else_, else_pc);
            }
            Terminator::Switch { value, cases, default } => {
                let vt = env.encode_operand(value);
                let mut default_pc = pc;
                for (val, target) in cases {
                    let cv = env.solver.bv_const(*val as i64, 32);
                    let eq = env.solver.bveq(vt, cv);
                    let case_pc = env.solver.and(pc, eq);
                    send(env, &mut incoming, &mut out, *target, case_pc);
                    let neq = env.solver.not(eq);
                    default_pc = env.solver.and(default_pc, neq);
                }
                send(env, &mut incoming, &mut out, *default, default_pc);
            }
            Terminator::Return(_) | Terminator::Halt => out.returns.push(pc),
            // An instruction the lifter could not model. Whatever happens
            // after it is not in this formula.
            Terminator::Diverge(_) => out.complete = false,
            Terminator::Throw(_) => {}
        }
    }
    out
}

/// A fresh, wholly unconstrained state over a body's locals.
fn fresh_state(env: &mut Env, body: &Body, tag: &str) -> State {
    let mut st = State::default();
    for (i, vi) in body.vars.iter().enumerate() {
        let w = width_of(&vi.ty);
        let t = env.fresh(&format!("{tag}v{i}"), w);
        st.vars.insert(VarId(i as u32), t);
    }
    st
}

/// Encode a method body as an SMT formula.
///
/// `frame` prefixes every SSA name, so several encodings can share one solver
/// context without their variables colliding.
pub fn encode_body(solver: &mut dyn Solver, body: &Body, frame: &str) -> Encoding {
    let mut env = Env::new(solver, frame);
    let init = fresh_state(&mut env, body, "");
    let members: BTreeSet<BlockId> = body.blocks.iter().map(|b| b.id).collect();
    let tt = env.solver.bool_const(true);

    // The whole body is one region entered at its entry block. Every edge is
    // internal except those back to the entry, so a back-edge elsewhere shows
    // up as an internal cycle and clears `complete`.
    let (_, back) = rpo_and_back_edges(body);
    let out = walk_region(&mut env, body, &members, body.entry, init, tt);

    let ff = env.solver.bool_const(false);
    let mut reach = ff;
    for pc in out.returns {
        reach = env.solver.or(reach, pc);
    }

    Encoding {
        violation_terms: out.violations,
        reach_term: reach,
        complete: out.complete && back.is_empty(),
    }
}

/// The two queries that make up a k-induction proof.
///
/// Both must be **UNSAT** for the obligation to be proved. They are separate
/// terms rather than one because each is a distinct claim and a caller that
/// conflates them proves nothing: the step case alone says only that the
/// property is preserved, which is vacuously true of a property that never
/// held.
pub struct KInductionQueries {
    /// Satisfiable iff the obligation is violated within the first `k`
    /// iterations, starting from the state the loop is actually entered in.
    pub base: Term,
    /// Satisfiable iff, from an **arbitrary** state, the obligation survives
    /// `k` consecutive iterations and then fails on the next.
    pub step: Term,
    /// The `k` these were built at.
    pub k: u32,
}

/// The blocks of the natural loop with the given header and back-edge tail:
/// everything that reaches `tail` without passing through `header`.
fn natural_loop(body: &Body, header: BlockId, tail: BlockId) -> BTreeSet<BlockId> {
    let mut preds: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for block in &body.blocks {
        for t in successors(block) {
            preds.entry(t).or_default().push(block.id);
        }
    }
    let mut set = BTreeSet::new();
    set.insert(header);
    let mut work = vec![tail];
    while let Some(b) = work.pop() {
        if b == header || !set.insert(b) {
            continue;
        }
        if let Some(ps) = preds.get(&b) {
            work.extend(ps.iter().copied());
        }
    }
    set
}

/// The blocks that one iteration of the loop can execute.
///
/// Not the natural loop. The natural loop is the blocks that *reach the
/// back-edge*, which omits any path that leaves the iteration without
/// completing it — and in lifted Java that is exactly where the interesting
/// obligation sits. `assert c;` compiles to a branch to a block that
/// constructs an `AssertionError` and throws, so the block carrying the
/// `Check` has no path back to the header and the natural loop excludes it.
/// Inducting over a region that cannot contain the property is vacuous.
///
/// Instead: everything reachable from the header without taking the loop's
/// exit edge or the back-edge. That is one pass, including the passes that
/// end by throwing.
fn loop_region(body: &Body, header: BlockId, tail: BlockId) -> BTreeSet<BlockId> {
    let nat = natural_loop(body, header, tail);
    // Successors of the header that leave the loop: the `i < n` test failing.
    let exit_targets: BTreeSet<BlockId> = body
        .blocks
        .get(header.0 as usize)
        .map(|h| {
            successors(h)
                .into_iter()
                .filter(|t| !nat.contains(t))
                .collect()
        })
        .unwrap_or_default();

    let mut region = BTreeSet::new();
    region.insert(header);
    let mut work = vec![header];
    while let Some(b) = work.pop() {
        let Some(block) = body.blocks.get(b.0 as usize) else { continue };
        for t in successors(block) {
            // The back-edge ends the iteration, and so does the exit edge.
            if t == header || (b == header && exit_targets.contains(&t)) {
                continue;
            }
            if region.insert(t) {
                work.push(t);
            }
        }
    }
    region
}

/// The single back-edge of `body`, if it has exactly one.
fn sole_back_edge(body: &Body) -> Option<(BlockId, BlockId)> {
    let (_, back) = rpo_and_back_edges(body);
    if back.len() != 1 {
        // Several loops, or an irreducible CFG. Neither is one transition
        // relation.
        return None;
    }
    back.iter().next().copied()
}

/// Whether `body` contains a `Check` of `oid` in any of `blocks`.
fn checks_in(body: &Body, blocks: &BTreeSet<BlockId>, oid: ObligationId) -> bool {
    blocks.iter().any(|b| {
        body.blocks
            .get(b.0 as usize)
            .is_some_and(|blk| blk.stmts.iter().any(|s| matches!(s, Stmt::Check(o) if *o == oid)))
    })
}

/// Whether `encode_k_induction` could possibly apply, without touching a
/// solver.
///
/// The engine consults this before spawning one. `encode_k_induction` repeats
/// the checks — it is called directly by tests and must not rely on a caller
/// having screened for it — but doing them here keeps a process spawn off the
/// path for every obligation in every loop-free method.
pub fn k_induction_applicable(body: &Body, oid: ObligationId) -> bool {
    let Some((tail, header)) = sole_back_edge(body) else {
        return false;
    };
    checks_in(body, &loop_region(body, header, tail), oid)
}

/// A rough count of the terms one k-induction attempt will build: the loop
/// region is encoded `2k + 1` times and each join emits an `ite` per live
/// variable and per heap map.
pub fn k_induction_cost(body: &Body, oid: ObligationId, k: u32) -> Option<usize> {
    let (tail, header) = sole_back_edge(body)?;
    let region = loop_region(body, header, tail);
    if !checks_in(body, &region, oid) {
        return None;
    }
    let stmts: usize = region
        .iter()
        .filter_map(|b| body.blocks.get(b.0 as usize))
        .map(|b| b.stmts.len().max(1))
        .sum();
    Some((2 * k as usize + 1) * stmts * body.vars.len().max(1))
}

/// Build the base and step queries for `oid` at depth `k`.
///
/// Returns `None` when the body is not a shape this can handle, which is the
/// common case and not an error: exactly one back-edge, no nested loop, the
/// obligation inside the loop, and a prefix the encoder describes completely.
///
/// # The argument
///
/// Let `T` be one pass through the loop body from the header back to the
/// header, and `P` the obligation. `base` asks whether `P` fails in any of the
/// first `k` iterations reached from the real entry state; `step` asks whether
/// there is *any* state from which `P` survives `k` iterations and fails on the
/// next. If both are unsatisfiable then, by induction on the iteration count,
/// `P` holds in every iteration — the base case covers `0..k`, and the step
/// carries `n..n+k` to `n+k+1` for every `n`.
///
/// This is what `try_step_case` was named for and did not do: it encoded the
/// body once, which is `base` at `k = 1` and no step case at all (#76).
///
/// Obligations *outside* the loop are not attempted. Discharging those needs
/// the loop's exit state, which needs an invariant rather than an induction on
/// a fixed depth.
pub fn encode_k_induction(
    solver: &mut dyn Solver,
    body: &Body,
    oid: ObligationId,
    k: u32,
) -> Option<KInductionQueries> {
    let (tail, header) = sole_back_edge(body)?;
    let loop_blocks = loop_region(body, header, tail);

    // The obligation has to be inside the loop for the induction to be about
    // it at all.
    if !checks_in(body, &loop_blocks, oid) {
        return None;
    }

    let mut env = Env::new(solver, "ki");

    // --- the state the loop is actually entered in ------------------------
    let all: BTreeSet<BlockId> = body.blocks.iter().map(|b| b.id).collect();
    let prefix: BTreeSet<BlockId> = all.difference(&loop_blocks).copied().collect();
    let entry_state = fresh_state(&mut env, body, "in");
    let tt = env.solver.bool_const(true);
    let pre = walk_region(&mut env, body, &prefix, body.entry, entry_state, tt);
    if !pre.complete {
        return None;
    }
    let into_header: Vec<(Term, State)> = pre
        .exits
        .into_iter()
        .filter(|(_, to, _, _)| *to == header)
        .map(|(_, _, pc, st)| (pc, st))
        .collect();
    if into_header.is_empty() {
        return None;
    }
    let (init_pc, init_state) = env.merge(into_header);

    // --- one pass through the loop ---------------------------------------
    // Returns the violation on this pass and the state on the back-edge.
    fn transition(
        env: &mut Env,
        body: &Body,
        loop_blocks: &BTreeSet<BlockId>,
        header: BlockId,
        oid: ObligationId,
        state: State,
        pc: Term,
        tag: &str,
    ) -> Option<(Term, Term, State)> {
        let saved = std::mem::replace(&mut env.frame, format!("ki{tag}"));
        let out = walk_region(env, body, loop_blocks, header, state, pc);
        env.frame = saved;
        if !out.complete {
            return None;
        }
        let violation = out
            .violations
            .get(&oid)
            .copied()
            .unwrap_or_else(|| env.solver.bool_const(false));
        // The back-edge is the exit whose target is the header.
        let back: Vec<(Term, State)> = out
            .exits
            .into_iter()
            .filter(|(_, to, _, _)| *to == header)
            .map(|(_, _, p, st)| (p, st))
            .collect();
        if back.is_empty() {
            return None;
        }
        let (next_pc, next_state) = env.merge(back);
        Some((violation, next_pc, next_state))
    }

    // --- base case: k iterations from the real entry state ----------------
    let mut base = env.solver.bool_const(false);
    let (mut st, mut pc) = (init_state, init_pc);
    for j in 0..k {
        let (v, next_pc, next_st) =
            transition(&mut env, body, &loop_blocks, header, oid, st, pc, &format!("b{j}"))?;
        base = env.solver.or(base, v);
        st = next_st;
        pc = next_pc;
    }

    // --- step case: k survived iterations from anywhere, then a failure ---
    let arb = fresh_state(&mut env, body, "s");
    let tt = env.solver.bool_const(true);
    let (mut st, mut pc) = (arb, tt);
    let mut step = env.solver.bool_const(true);
    for j in 0..=k {
        let (v, next_pc, next_st) =
            transition(&mut env, body, &loop_blocks, header, oid, st, pc, &format!("s{j}"))?;
        if j == k {
            // The failing iteration.
            step = env.solver.and(step, v);
        } else {
            // An iteration the hypothesis says held.
            let nv = env.solver.not(v);
            step = env.solver.and(step, nv);
        }
        st = next_st;
        pc = next_pc;
    }

    Some(KInductionQueries { base, step, k })
}

/// Internal encoding environment.
struct Env<'a> {
    solver: &'a mut dyn Solver,
    frame: String,
    vars: VarMap,
    pts: PtsMap,
    heap: Heap,
    next_site: Site,
    /// Address handed to the next allocation. See `alloc_ref`.
    next_addr: i64,
    next_ssa: u32,
}

impl<'a> Env<'a> {
    fn new(solver: &'a mut dyn Solver, frame: &str) -> Env<'a> {
        Env {
            solver,
            frame: frame.to_string(),
            vars: VarMap::new(),
            pts: PtsMap::new(),
            heap: Heap::default(),
            next_site: 0,
            next_addr: FIRST_ADDR,
            next_ssa: 0,
        }
    }

    fn fresh(&mut self, name: &str, width: u32) -> Term {
        self.next_ssa += 1;
        self.solver
            .fresh_bv(&format!("{}_{}{}", self.frame, name, self.next_ssa), width)
    }

    /// Join the states arriving on several edges into one.
    ///
    /// The path condition is the disjunction of the edge conditions; each
    /// variable becomes `ite(edge_pc, value_on_that_edge, rest)`. Folding from
    /// the last edge backwards makes the first edge the outermost test, so
    /// the term is determined by edge order rather than by map iteration
    /// order — the encoder must not depend on a hash seed.
    fn merge(&mut self, mut edges: Vec<(Term, State)>) -> (Term, State) {
        if edges.len() == 1 {
            return edges.pop().expect("length checked");
        }
        let mut pc = self.solver.bool_const(false);
        for (epc, _) in &edges {
            pc = self.solver.or(pc, *epc);
        }

        // Terms of any sort can be joined with `ite`, arrays included, so the
        // heap merges exactly like the locals do.
        macro_rules! join {
            ($($field:ident).+, $out:expr) => {{
                let keys: BTreeSet<_> = edges
                    .iter()
                    .flat_map(|(_, st)| st.$($field).+.keys().cloned())
                    .collect();
                for k in keys {
                    // Seed from the last edge so the fold has a base case; its
                    // guard is implied by the disjunction of the others.
                    let mut acc = None;
                    for (epc, st) in edges.iter().rev() {
                        let Some(&v) = st.$($field).+.get(&k) else { continue };
                        acc = Some(match acc {
                            None => v,
                            Some(rest) => self.solver.ite(*epc, v, rest),
                        });
                    }
                    if let Some(t) = acc {
                        $out.insert(k, t);
                    }
                }
            }};
        }

        let mut out = State::default();
        join!(vars, out.vars);
        join!(heap.arrays, out.heap.arrays);
        join!(heap.lengths, out.heap.lengths);
        join!(heap.fields, out.heap.fields);
        join!(heap.statics, out.heap.statics);

        // A reference resolves to an allocation site only if every incoming
        // edge agrees. Disagreement is a genuine may-alias, and dropping to
        // "unknown" is what makes a later store havoc all arrays instead of
        // updating the wrong one.
        let pts_keys: BTreeSet<VarId> =
            edges.iter().flat_map(|(_, st)| st.pts.keys().copied()).collect();
        for k in pts_keys {
            let mut sites = edges.iter().map(|(_, st)| st.pts.get(&k).copied());
            let first = sites.next().flatten();
            if let Some(site) = first {
                if sites.all(|s| s == Some(site)) {
                    out.pts.insert(k, site);
                }
            }
        }
        (pc, out)
    }

    /// A reference for a fresh object, distinct from every other allocation.
    ///
    /// Successive allocations get successive constants rather than fresh
    /// symbols with pairwise disequalities, which would be quadratic. The
    /// constants are sound because nothing in Java can observe an address:
    /// only reference equality is visible, and distinct constants preserve
    /// exactly the disequalities the JLS guarantees between a `new` object and
    /// every reference that already exists. References the encoder did not
    /// allocate stay unconstrained, so they can still alias anything — which
    /// costs precision, never soundness.
    fn alloc_ref(&mut self) -> Term {
        let addr = self.next_addr;
        self.next_addr += 1;
        self.solver.bv_const(addr, 32)
    }

    /// The allocation site a reference operand resolves to, if exactly one.
    fn site_of(&self, op: &Operand) -> Option<Site> {
        match op {
            Operand::Var(v) => self.pts.get(v).copied(),
            _ => None,
        }
    }

    /// The element map for an allocation site, created empty on first use.
    fn array_map(&mut self, site: Site, width: u32) -> Term {
        if let Some(&t) = self.heap.arrays.get(&site) {
            return t;
        }
        let t = {
            self.next_ssa += 1;
            let n = format!("{}_arr{}_{}", self.frame, site, self.next_ssa);
            self.solver.fresh_array(&n, width)
        };
        self.heap.arrays.insert(site, t);
        t
    }

    /// The map for an instance field, indexed by object reference.
    fn field_map(&mut self, fk: &FieldKey, width: u32) -> Term {
        if let Some(&t) = self.heap.fields.get(fk) {
            return t;
        }
        let t = {
            self.next_ssa += 1;
            let n = format!("{}_fld{}_{}", self.frame, self.next_ssa, fk.name);
            self.solver.fresh_array(&n, width)
        };
        self.heap.fields.insert(fk.clone(), t);
        t
    }

    /// Forget every array's contents.
    ///
    /// Used for a store through a reference whose allocation site is unknown.
    /// Dropping such a store would be unsound — the unknown reference may be
    /// the very array a later load reads — so the contents become arbitrary
    /// instead, which covers whatever the store actually did.
    fn havoc_arrays(&mut self) {
        let sites: Vec<Site> = self.heap.arrays.keys().copied().collect();
        for site in sites {
            self.next_ssa += 1;
            let n = format!("{}_arrhavoc{}_{}", self.frame, site, self.next_ssa);
            let t = self.solver.fresh_array(&n, 32);
            self.heap.arrays.insert(site, t);
        }
    }

    /// Forget the whole heap: array contents, instance fields, statics.
    ///
    /// A call that is not known to be pure can write anywhere the encoder
    /// cannot see. Lengths survive — an array's length is immutable in Java,
    /// and so is the reference-to-site mapping.
    fn havoc_heap(&mut self) {
        self.havoc_arrays();
        let fields: Vec<FieldKey> = self.heap.fields.keys().cloned().collect();
        for fk in fields {
            let w = field_width(&fk.desc);
            self.next_ssa += 1;
            let n = format!("{}_fldhavoc{}", self.frame, self.next_ssa);
            let t = self.solver.fresh_array(&n, w);
            self.heap.fields.insert(fk, t);
        }
        let statics: Vec<FieldKey> = self.heap.statics.keys().cloned().collect();
        for fk in statics {
            let w = field_width(&fk.desc);
            let t = self.fresh("sthavoc", w);
            self.heap.statics.insert(fk, t);
        }
    }

    fn operand_width(op: &Operand) -> u32 {
        match op {
            Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => 64,
            _ => 32,
        }
    }

    fn encode_operand(&mut self, op: &Operand) -> Term {
        match op {
            Operand::Var(v) => self.vars.get(v).copied().unwrap_or_else(|| {
                let t = self.fresh("uninit", 32);
                self.vars.insert(*v, t);
                t
            }),
            Operand::Const(Const::Int(n)) => self.solver.bv_const(*n as i64, 32),
            Operand::Const(Const::Long(n)) => self.solver.bv_const(*n, 64),
            Operand::Const(Const::Null) => self.solver.bv_const(0, 32),
            Operand::Const(Const::Str(_)) => self.solver.bv_const(1, 32),
            Operand::Const(Const::Float(f)) => self.solver.bv_const(f.to_bits() as i64, 32),
            Operand::Const(Const::Double(d)) => self.solver.bv_const(d.to_bits() as i64, 64),
            Operand::Const(_) => self.solver.bv_const(0, 32),
        }
    }

    /// Encode an rvalue, returning its term and — for an array allocation or
    /// a copy of an array reference — the allocation site it denotes.
    fn encode_rvalue(&mut self, rv: &Rvalue) -> (Term, Option<Site>) {
        match rv {
            Rvalue::Use(o) => (self.encode_operand(o), self.site_of(o)),
            Rvalue::Nondet(ty, _) | Rvalue::Havoc(ty, _) => {
                let w = width_of(ty);
                (self.fresh("nd", w), None)
            }
            Rvalue::Bin(op, a, b) => (self.encode_binop(*op, a, b), None),
            Rvalue::Neg(o) => {
                let t = self.encode_operand(o);
                (self.solver.bvneg(t), None)
            }
            Rvalue::Cast(ty, _src, o) => {
                let t = self.encode_operand(o);
                let t = match ty {
                    Ty::Long => self.solver.sign_extend(t, 32),
                    Ty::Int => self.solver.extract(t, 31, 0),
                    _ => t,
                };
                (t, None)
            }
            Rvalue::Cmp(_, a, b) => {
                let at = self.encode_operand(a);
                let bt = self.encode_operand(b);
                // Handle width mismatch: sign-extend shorter operand.
                let aw = Self::operand_width(a);
                let bw = Self::operand_width(b);
                let (at, bt) = if aw < bw {
                    (self.solver.sign_extend(at, bw - aw), bt)
                } else if bw < aw {
                    (at, self.solver.sign_extend(bt, aw - bw))
                } else {
                    (at, bt)
                };
                let lt = self.solver.bvslt(at, bt);
                let eq = self.solver.bveq(at, bt);
                let m1 = self.solver.bv_const(-1, 32);
                let zero = self.solver.bv_const(0, 32);
                let one = self.solver.bv_const(1, 32);
                let inner = self.solver.ite(eq, zero, one);
                (self.solver.ite(lt, m1, inner), None)
            }
            Rvalue::New(_) => {
                // Non-null by construction, and the index into this object's
                // field maps.
                (self.alloc_ref(), None)
            }
            Rvalue::NewArray { elem, len } => {
                let site = self.next_site;
                self.next_site += 1;
                let w = field_width(elem);
                let _ = self.array_map(site, w);
                let len_t = self.encode_operand(len);
                self.heap.lengths.insert(site, len_t);
                (self.alloc_ref(), Some(site))
            }
            Rvalue::ArrayLoad { arr, idx } => {
                let Some(site) = self.site_of(arr) else {
                    // Reading an array we cannot name yields an arbitrary
                    // value, which covers whatever it actually holds.
                    return (self.fresh("arrload", 32), None);
                };
                let map = self.array_map(site, 32);
                let i = self.encode_operand(idx);
                (self.solver.array_select(map, i), None)
            }
            Rvalue::ArrayLength(arr) => {
                match self.site_of(arr).and_then(|s| self.heap.lengths.get(&s).copied()) {
                    Some(t) => (t, None),
                    None => (self.fresh("arrlen", 32), None),
                }
            }
            Rvalue::GetField { obj, field } => {
                let w = field_width(&field.desc);
                let map = self.field_map(field, w);
                let r = self.encode_operand(obj);
                (self.solver.array_select(map, r), None)
            }
            Rvalue::GetStatic(fk) => {
                let w = field_width(&fk.desc);
                let t = match self.heap.statics.get(fk) {
                    Some(&t) => t,
                    None => {
                        let t = self.fresh("static", w);
                        self.heap.statics.insert(fk.clone(), t);
                        t
                    }
                };
                (t, None)
            }
            Rvalue::InstanceOf { .. } => (self.fresh("instanceof", 32), None),
            Rvalue::Call { target, .. } => {
                // A call that is not known to be pure may write anywhere.
                // Its return value is unconstrained either way.
                let pure = ajave_models::contract_of(&target.class, &target.name, &target.desc)
                    .map(|c| c.effect == ajave_models::Effect::Pure)
                    .unwrap_or(false);
                if !pure {
                    self.havoc_heap();
                }
                let w = return_width(&target.desc);
                (self.fresh("callret", w), None)
            }
        }
    }

    fn encode_binop(&mut self, op: BinOp, a: &Operand, b: &Operand) -> Term {
        let at = self.encode_operand(a);
        let bt = self.encode_operand(b);
        // Normalise widths: sign-extend shorter operand (except shifts).
        let aw = Self::operand_width(a);
        let bw = Self::operand_width(b);
        let (at, bt) = if !matches!(op, BinOp::Shl | BinOp::Shr | BinOp::UShr) && aw != bw {
            if aw < bw {
                (self.solver.sign_extend(at, bw - aw), bt)
            } else {
                (at, self.solver.sign_extend(bt, aw - bw))
            }
        } else {
            (at, bt)
        };
        let one = self.solver.bv_const(1, 32);
        let zero = self.solver.bv_const(0, 32);
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
                let aw = Self::operand_width(a);
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
                let c = self.solver.bveq(at, bt);
                self.solver.ite(c, one, zero)
            }
            BinOp::Ne => {
                let c = self.solver.bveq(at, bt);
                let nc = self.solver.not(c);
                self.solver.ite(nc, one, zero)
            }
            BinOp::Lt => {
                let c = self.solver.bvslt(at, bt);
                self.solver.ite(c, one, zero)
            }
            BinOp::Le => {
                let c = self.solver.bvsle(at, bt);
                self.solver.ite(c, one, zero)
            }
            BinOp::Gt => {
                let c = self.solver.bvsgt(at, bt);
                self.solver.ite(c, one, zero)
            }
            BinOp::Ge => {
                let c = self.solver.bvsge(at, bt);
                self.solver.ite(c, one, zero)
            }
        }
    }
}
