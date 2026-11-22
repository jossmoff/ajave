//! Post-dominator structure of one `Body`, and what it decides.
//!
//! A branch can be **merged** rather than **forked** exactly when both arms
//! reconverge at a point every path leaving the branch must reach. That point
//! is the branch block's immediate post-dominator, and finding it is the whole
//! content of large-block encoding (Beyer, Cimatti, Griggio, Keremoglu,
//! Sebastiani, *Software Model Checking via Large-Block Encoding*, FMCAD
//! 2009). The cost difference is not marginal: `handle_branch_diamond`
//! explores each arm to the join, merges with one `ite` per differing
//! variable, and continues **once**; `handle_branch_fork` explores each arm to
//! the end of the enclosing region, so every fork duplicates the entire
//! remainder of the method.
//!
//! ## What this replaced
//!
//! `find_join` intersected depth-limited forward-reachable sets and took the
//! numerically smallest common block. Two defects, and the second is the
//! expensive one:
//!
//! * The reachability walk was capped at 50 blocks and followed only edges to
//!   higher block ids, so a join further away was simply not found.
//! * It bailed out to forking whenever one arm's target was reachable from
//!   another arm's target, on the grounds that "the branches are not
//!   independent". That is **the most common branch shape in Java**: a
//!   one-armed `if` compiles to `ifeq join`, so the else target *is* the join
//!   and is trivially reachable from the then target. Every one-armed `if`
//!   forked.
//!
//! Simulink-generated bodies are hundreds of sequential one-armed ifs, which
//! is why `java-ranger-regression/alarm/Alarm_prop2` — 893 blocks in one
//! method — exhausted `MAX_FORKS` having visited a fraction of them, and why
//! raising one cap only moved the truncation to the next (gh #126, #128).
//!
//! ## Exception edges are deliberately absent
//!
//! `Block::exceptional` is not in this graph. An implicit throw is explored as
//! a separate subtree under a saved state and restored afterwards
//! (`fork_into_implicit_handler`, whose comment records that "an exception does
//! not rejoin the path it left"), so the main path still reaches the
//! post-dominator and merging there stays correct. Including those edges would
//! make the virtual exit the immediate post-dominator of almost every block
//! and merge nothing.
//!
//! ## What a consumer may conclude
//!
//! `join_for(b)` returning `Some(j)` means: every path from `b` that reaches a
//! method exit passes through `j`, and no path from `b` to `j` traverses a
//! loop back edge. Both halves are load-bearing. The first is what makes
//! merging at `j` sound — no arm can skip the merge point. The second is what
//! keeps the two states being merged states *at the same program point*,
//! rather than states at whatever point an unrolling bound ran out.

use std::collections::HashSet;

use ajave_ir::{Block, BlockId, Body, Terminator};

/// Upper bound on the number of blocks in a merged region. 0 means no bound.
///
/// Adjustable-block encoding (Beyer, Keremoglu, Wendler, *Predicate
/// Abstraction with Adjustable-Block Encoding*, FMCAD 2010) is precisely the
/// observation that region size is a parameter: large regions trade path
/// enumeration for formula size, and past some point the solver answers
/// `unknown` where enumeration would have answered.
///
/// This is a *fitted constant* of the kind `CLAUDE.md` warns about, so it is
/// swept rather than chosen: `AJAVE_LBE_MAX_REGION` overrides it.
const DEFAULT_MAX_REGION_BLOCKS: usize = 0;

fn max_region_blocks() -> usize {
    static N: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *N.get_or_init(|| {
        std::env::var("AJAVE_LBE_MAX_REGION")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(DEFAULT_MAX_REGION_BLOCKS)
    })
}

/// Whether post-dominator joins are used at all.
///
/// `AJAVE_LBE=0` leaves the previous reachability heuristic in place, so both
/// can be measured on one build — which is the only way to attribute a score
/// change to this and not to the build. See `changes.md`.
pub(super) fn lbe_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_LBE").as_deref() != Ok("0"))
}

/// Normal-control-flow successors of a block. See the module note on why
/// `exceptional` is excluded.
fn successors(b: &Block) -> Vec<BlockId> {
    match &b.term {
        Terminator::Goto(t) => vec![*t],
        Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
        Terminator::Switch { cases, default, .. } => {
            let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
            v.push(*default);
            v
        }
        // Control leaves the method: `Return`, `Throw`, `Halt`, `Diverge`.
        // These are the predecessors of the virtual exit.
        _ => vec![],
    }
}

/// Why a branching block was refused a join.
///
/// Counted rather than inferred. The corpus history is three buckets that
/// counted a *symptom* and were read as a *cause* — `refuted-witness` at 211
/// pairs that was really 1, the flattened-length premise at 198 that was
/// really 4, `budget` at 135 that was really 1 — so the next region increment
/// is chosen from these tallies and not from which of Java Ranger's
/// `veritestingMode` levels reads as next.
#[derive(Default, Clone, Copy, Debug)]
pub(super) struct DeclineTally {
    /// Branching blocks that got a join and will merge.
    pub merged: u32,
    /// The immediate post-dominator is the virtual exit: some path out of this
    /// branch leaves the method without reconverging. An arm with an early
    /// `return` or `throw` — a guard clause — is the common case, and this is
    /// what Java Ranger's levels 4 and 5 address by admitting regions with
    /// more than one exit.
    pub exits_method: u32,
    /// The region holds a loop back edge, so an arm cannot be explored to the
    /// join without unrolling. Not addressed by any Java Ranger level; loops
    /// are the explorer's own territory.
    pub back_edge: u32,
    /// `region_blocks` could not reach the claimed join. Post-dominance should
    /// make this impossible, so a non-zero count here is a bug in this file,
    /// not a program shape.
    pub region_escapes: u32,
    /// The region was larger than `AJAVE_LBE_MAX_REGION`.
    pub over_cap: u32,
}

pub(super) struct CfgInfo {
    /// `joins[i]` is where a branch or switch at block `i` may be merged, or
    /// `None` when it must fork. Computed eagerly: the explorer asks the same
    /// question once per visit to a block, and a loop body is visited many
    /// times.
    joins: Vec<Option<BlockId>>,
    /// Test-only: in production the tally is emitted as a log line and not
    /// retained, because nothing in the engine reads it back. Keeping the
    /// field unconditionally would be a dead-code warning, and silencing that
    /// with an allow would hide the next genuinely unread field.
    #[cfg(test)]
    tally: DeclineTally,
}

impl CfgInfo {
    pub(super) fn of(body: &Body) -> Self {
        let n = body.blocks.len();
        let succs: Vec<Vec<BlockId>> = body.blocks.iter().map(successors).collect();
        let ipdom = post_dominators(n, &succs);
        let back_edge_source = back_edge_sources(body.entry, n, &succs);
        let cap = max_region_blocks();

        let mut tally = DeclineTally::default();
        let mut joins: Vec<Option<BlockId>> = Vec::with_capacity(n);
        for i in 0..n {
            // Only branching blocks are ever asked, so only they are
            // computed: the region walk is the expensive part.
            if succs[i].len() < 2 {
                joins.push(None);
                continue;
            }
            let Some(j) = ipdom[i] else {
                tally.exits_method += 1;
                joins.push(None);
                continue;
            };
            let Some(region) = region_blocks(BlockId(i as u32), j, &succs) else {
                tally.region_escapes += 1;
                joins.push(None);
                continue;
            };
            if region.iter().any(|&b| back_edge_source[b as usize]) {
                tally.back_edge += 1;
                joins.push(None);
                continue;
            }
            if cap != 0 && region.len() > cap {
                tally.over_cap += 1;
                joins.push(None);
                continue;
            }
            tally.merged += 1;
            joins.push(Some(j));
        }

        if tally.merged
            + tally.exits_method
            + tally.back_edge
            + tally.region_escapes
            + tally.over_cap
            > 0
        {
            log::debug!(
                "cfg: {} blocks={} merged={} exits_method={} back_edge={} \
                 region_escapes={} over_cap={}",
                body.key,
                n,
                tally.merged,
                tally.exits_method,
                tally.back_edge,
                tally.region_escapes,
                tally.over_cap,
            );
        }

        CfgInfo {
            joins,
            #[cfg(test)]
            tally,
        }
    }

    #[cfg(test)]
    fn tally(&self) -> DeclineTally {
        self.tally
    }

    /// The block the arms of a branch or switch at `from` reconverge at, when
    /// merging there is sound and finite. See the module note.
    pub(super) fn join_for(&self, from: BlockId) -> Option<BlockId> {
        *self.joins.get(from.0 as usize)?
    }
}

/// Blocks on a path from `from` to `to`, `from` included and `to` excluded.
///
/// `None` when the walk leaves the method without passing `to`. Post-dominance
/// should make that impossible, so this is a declining guard rather than an
/// invariant asserted in a comment — the pattern `CLAUDE.md` names.
fn region_blocks(from: BlockId, to: BlockId, succs: &[Vec<BlockId>]) -> Option<Vec<u32>> {
    let mut seen: HashSet<u32> = HashSet::new();
    let mut out: Vec<u32> = Vec::new();
    let mut work = vec![from];
    while let Some(b) = work.pop() {
        if b == to || !seen.insert(b.0) {
            continue;
        }
        out.push(b.0);
        let ss = succs.get(b.0 as usize)?;
        if ss.is_empty() {
            // A return, throw or diverge inside the region: control leaves
            // without passing the claimed join.
            return None;
        }
        for s in ss {
            work.push(*s);
        }
    }
    out.sort_unstable();
    Some(out)
}

/// Immediate post-dominators, as dominators of the reverse graph rooted at a
/// virtual exit (Cooper, Harvey, Kennedy, *A Simple, Fast Dominance
/// Algorithm*, 2001).
///
/// Node `n` is the virtual exit; every block with no normal successor is its
/// predecessor in the forward graph, hence its successor in the reverse graph.
/// A block from which no exit is reachable — an infinite loop — is absent from
/// the traversal and gets `None`, which declines rather than inventing a join.
fn post_dominators(n: usize, succs: &[Vec<BlockId>]) -> Vec<Option<BlockId>> {
    let exit = n;
    let mut rev: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
    for (u, ss) in succs.iter().enumerate() {
        if ss.is_empty() {
            rev[exit].push(u);
        }
        for v in ss {
            rev[v.0 as usize].push(u);
        }
    }

    let order = reverse_postorder(exit, n + 1, &rev);
    let mut rpo_num = vec![usize::MAX; n + 1];
    for (i, &b) in order.iter().enumerate() {
        rpo_num[b] = i;
    }

    let mut idom: Vec<Option<usize>> = vec![None; n + 1];
    idom[exit] = Some(exit);
    let mut changed = true;
    while changed {
        changed = false;
        // `order[0]` is the exit, whose dominator is itself.
        for &b in order.iter().skip(1) {
            // Predecessors in the reverse graph are forward successors —
            // plus the virtual exit, for a block that leaves the method.
            // Omitting that second case left every exiting block with no
            // dominator, which propagated back and gave the entire body no
            // post-dominators at all.
            let mut preds: Vec<usize> = succs[b].iter().map(|s| s.0 as usize).collect();
            if preds.is_empty() {
                preds.push(exit);
            }
            let mut new_idom: Option<usize> = None;
            for p in preds {
                if idom[p].is_none() {
                    continue;
                }
                new_idom = Some(match new_idom {
                    None => p,
                    Some(cur) => intersect(cur, p, &idom, &rpo_num),
                });
            }
            if let Some(ni) = new_idom {
                if idom[b] != Some(ni) {
                    idom[b] = Some(ni);
                    changed = true;
                }
            }
        }
    }

    (0..n)
        .map(|b| match idom[b] {
            Some(d) if d != exit && d != b => Some(BlockId(d as u32)),
            _ => None,
        })
        .collect()
}

fn intersect(mut a: usize, mut b: usize, idom: &[Option<usize>], rpo: &[usize]) -> usize {
    while a != b {
        while rpo[a] > rpo[b] {
            match idom[a] {
                Some(d) if d != a => a = d,
                _ => return b,
            }
        }
        while rpo[b] > rpo[a] {
            match idom[b] {
                Some(d) if d != b => b = d,
                _ => return a,
            }
        }
    }
    a
}

/// Reverse postorder from `root`, iteratively: the explorer is already deeply
/// recursive and shares this stack.
fn reverse_postorder(root: usize, n: usize, graph: &[Vec<usize>]) -> Vec<usize> {
    let mut visited = vec![false; n];
    let mut post: Vec<usize> = Vec::new();
    let mut stack: Vec<(usize, usize)> = vec![(root, 0)];
    visited[root] = true;
    while let Some(&(node, i)) = stack.last() {
        if i < graph[node].len() {
            stack.last_mut().expect("stack non-empty").1 += 1;
            let next = graph[node][i];
            if !visited[next] {
                visited[next] = true;
                stack.push((next, 0));
            }
        } else {
            post.push(node);
            stack.pop();
        }
    }
    post.reverse();
    post
}

/// Which blocks are the source of a loop back edge — an edge whose target was
/// still on the DFS stack when it was taken.
fn back_edge_sources(entry: BlockId, n: usize, succs: &[Vec<BlockId>]) -> Vec<bool> {
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        White,
        Grey,
        Black,
    }
    let mut out = vec![false; n];
    if (entry.0 as usize) >= n {
        return out;
    }
    let mut colour = vec![Colour::White; n];
    colour[entry.0 as usize] = Colour::Grey;
    let mut stack: Vec<(usize, usize)> = vec![(entry.0 as usize, 0)];
    while let Some(&(node, i)) = stack.last() {
        if i < succs[node].len() {
            stack.last_mut().expect("stack non-empty").1 += 1;
            let next = succs[node][i].0 as usize;
            match colour.get(next) {
                Some(Colour::Grey) => out[node] = true,
                Some(Colour::White) => {
                    colour[next] = Colour::Grey;
                    stack.push((next, 0));
                }
                _ => {}
            }
        } else {
            colour[node] = Colour::Black;
            stack.pop();
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::{MethodKey, Operand, VarId};

    fn body(terms: Vec<Terminator>) -> Body {
        let blocks = terms
            .into_iter()
            .enumerate()
            .map(|(i, term)| Block {
                id: BlockId(i as u32),
                bytecode_offset: 0,
                stmts: vec![],
                term,
                exceptional: vec![],
            })
            .collect();
        Body {
            key: MethodKey {
                class: "C".into(),
                name: "m".into(),
                desc: "()V".into(),
            },
            entry: BlockId(0),
            blocks,
            vars: vec![],
            obligations: vec![],
            is_static: true,
        }
    }

    fn br(then_: u32, else_: u32) -> Terminator {
        Terminator::Branch {
            cond: Operand::Var(VarId(0)),
            then_: BlockId(then_),
            else_: BlockId(else_),
        }
    }

    /// `if (c) { x = 1; }` — the shape the old heuristic always forked, because
    /// the else target is the join and so is reachable from the then target.
    #[test]
    fn a_one_armed_if_has_a_join() {
        let b = body(vec![
            br(1, 2),
            Terminator::Goto(BlockId(2)),
            Terminator::Return(None),
        ]);
        assert_eq!(CfgInfo::of(&b).join_for(BlockId(0)), Some(BlockId(2)));
    }

    #[test]
    fn a_two_armed_if_has_a_join() {
        let b = body(vec![
            br(1, 2),
            Terminator::Goto(BlockId(3)),
            Terminator::Goto(BlockId(3)),
            Terminator::Return(None),
        ]);
        assert_eq!(CfgInfo::of(&b).join_for(BlockId(0)), Some(BlockId(3)));
    }

    /// A branch whose arms return separately has no join, and must fork.
    #[test]
    fn divergent_returns_have_no_join() {
        let b = body(vec![
            br(1, 2),
            Terminator::Return(None),
            Terminator::Return(None),
        ]);
        assert_eq!(CfgInfo::of(&b).join_for(BlockId(0)), None);
    }

    /// `while (c) { body }`: the region from the loop header to its
    /// post-dominator contains the back edge, so it is declined. Loops stay
    /// the explorer's unrolling territory.
    #[test]
    fn a_loop_header_is_declined_because_the_region_has_a_back_edge() {
        let b = body(vec![
            br(1, 2),
            Terminator::Goto(BlockId(0)),
            Terminator::Return(None),
        ]);
        let succs: Vec<Vec<BlockId>> = b.blocks.iter().map(successors).collect();
        assert!(back_edge_sources(b.entry, b.blocks.len(), &succs)[1]);
        assert_eq!(CfgInfo::of(&b).join_for(BlockId(0)), None);
    }

    /// A one-armed if *inside* a loop body still merges: the region between the
    /// branch and its join holds no back edge even though the method does.
    #[test]
    fn a_branch_inside_a_loop_body_still_merges() {
        let b = body(vec![
            br(1, 4),
            br(2, 3),
            Terminator::Goto(BlockId(3)),
            Terminator::Goto(BlockId(0)),
            Terminator::Return(None),
        ]);
        let info = CfgInfo::of(&b);
        assert_eq!(info.join_for(BlockId(1)), Some(BlockId(3)));
        assert_eq!(info.join_for(BlockId(0)), None);
    }

    /// A chain of one-armed ifs: the Simulink shape. Every branch merges, so
    /// nothing forks and the exploration is linear in the chain length.
    #[test]
    fn a_chain_of_one_armed_ifs_merges_at_every_branch() {
        let b = body(vec![
            br(1, 2),
            Terminator::Goto(BlockId(2)),
            br(3, 4),
            Terminator::Goto(BlockId(4)),
            br(5, 6),
            Terminator::Goto(BlockId(6)),
            Terminator::Return(None),
        ]);
        let info = CfgInfo::of(&b);
        assert_eq!(info.join_for(BlockId(0)), Some(BlockId(2)));
        assert_eq!(info.join_for(BlockId(2)), Some(BlockId(4)));
        assert_eq!(info.join_for(BlockId(4)), Some(BlockId(6)));
    }

    /// A switch is asked the same question, and a `tableswitch` over a chain of
    /// cases that all fall through to one block merges.
    #[test]
    fn a_switch_whose_cases_reconverge_has_a_join() {
        let b = body(vec![
            Terminator::Switch {
                value: Operand::Var(VarId(0)),
                cases: vec![(0, BlockId(1)), (1, BlockId(2))],
                default: BlockId(3),
            },
            Terminator::Goto(BlockId(4)),
            Terminator::Goto(BlockId(4)),
            Terminator::Goto(BlockId(4)),
            Terminator::Return(None),
        ]);
        assert_eq!(CfgInfo::of(&b).join_for(BlockId(0)), Some(BlockId(4)));
    }

    /// The region walk is what the cap bounds, so it has to report the real
    /// size.
    #[test]
    fn the_region_walk_reports_every_block_it_covers() {
        let b = body(vec![
            br(1, 2),
            Terminator::Goto(BlockId(2)),
            Terminator::Return(None),
        ]);
        let succs: Vec<Vec<BlockId>> = b.blocks.iter().map(successors).collect();
        let region = region_blocks(BlockId(0), BlockId(2), &succs).expect("join reachable");
        assert_eq!(region, vec![0, 1]);
    }

    /// A guard clause — `if (c) return;` — has no join inside the method, and
    /// the tally must attribute it to the exit reason rather than to a loop.
    /// This is the shape Java Ranger's levels 4 and 5 admit, so the count
    /// deciding whether to build them has to be right.
    #[test]
    fn a_guard_clause_is_counted_as_exiting_the_method() {
        // bb0: branch -> bb1 (return) / bb2 (continue)
        // bb1: return
        // bb2: return
        let b = body(vec![
            br(1, 2),
            Terminator::Return(None),
            Terminator::Return(None),
        ]);
        let t = CfgInfo::of(&b).tally();
        assert_eq!(t.exits_method, 1, "the branch exits without reconverging");
        assert_eq!(t.merged, 0);
        assert_eq!(t.back_edge, 0);
        assert_eq!(t.region_escapes, 0, "a correct ipdom never escapes");
    }

    /// A loop header must be attributed to the back edge, not to the exit,
    /// because the two reasons point at completely different work.
    #[test]
    fn a_loop_header_is_counted_as_a_back_edge_not_an_exit() {
        let b = body(vec![
            br(1, 2),
            Terminator::Goto(BlockId(0)),
            Terminator::Return(None),
        ]);
        let t = CfgInfo::of(&b).tally();
        assert_eq!(t.back_edge, 1);
        assert_eq!(t.exits_method, 0);
        assert_eq!(t.merged, 0);
    }

    /// And the merging shapes must be counted as merged, or the tally would
    /// make the encoding look like it never fires.
    #[test]
    fn a_chain_of_one_armed_ifs_is_counted_as_merged() {
        let b = body(vec![
            br(1, 2),
            Terminator::Goto(BlockId(2)),
            br(3, 4),
            Terminator::Goto(BlockId(4)),
            Terminator::Return(None),
        ]);
        let t = CfgInfo::of(&b).tally();
        assert_eq!(t.merged, 2);
        assert_eq!(t.exits_method, 0);
        assert_eq!(t.back_edge, 0);
    }

    /// `region_escapes` is a bug detector, not a program shape: a correct
    /// immediate post-dominator is always reachable from the branch. If this
    /// ever fires on the corpus, `post_dominators` is wrong.
    #[test]
    fn region_escapes_stays_zero_on_every_shape_here() {
        let shapes = vec![
            vec![
                br(1, 2),
                Terminator::Goto(BlockId(2)),
                Terminator::Return(None),
            ],
            vec![
                br(1, 2),
                Terminator::Goto(BlockId(3)),
                Terminator::Goto(BlockId(3)),
                Terminator::Return(None),
            ],
            vec![br(1, 2), Terminator::Return(None), Terminator::Return(None)],
            vec![
                br(1, 2),
                Terminator::Goto(BlockId(0)),
                Terminator::Return(None),
            ],
            vec![
                br(1, 4),
                br(2, 3),
                Terminator::Goto(BlockId(3)),
                Terminator::Goto(BlockId(0)),
                Terminator::Return(None),
            ],
        ];
        for (i, terms) in shapes.into_iter().enumerate() {
            let t = CfgInfo::of(&body(terms)).tally();
            assert_eq!(t.region_escapes, 0, "shape {i} escaped its own join");
        }
    }

    /// An infinite loop makes the exit unreachable, so post-dominance is
    /// undefined there and we decline rather than invent a join.
    #[test]
    fn an_unreachable_exit_yields_no_join() {
        let b = body(vec![br(1, 1), Terminator::Goto(BlockId(0))]);
        assert_eq!(CfgInfo::of(&b).join_for(BlockId(0)), None);
    }
}
