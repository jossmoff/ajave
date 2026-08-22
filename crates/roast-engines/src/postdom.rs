//! Post-dominator tree for a method body.
//!
//! Block `p` post-dominates `b` when every path from `b` to an exit passes
//! through `p`. The *immediate* post-dominator is the closest such block, and
//! it is exactly the join point a symbolic executor wants: the place where the
//! arms of a branch provably reconverge, so their states can be merged with an
//! `ite` instead of forked into separate paths.
//!
//! This replaces an ad-hoc search that ran a fresh forward-reachability sweep
//! from each branch target, intersected the results, and took the lowest common
//! block. That was wrong in two ways and slow in a third:
//!
//! * It capped each sweep at 50 blocks, so on a larger method it silently
//!   returned no join and the explorer fell back to path forking -- losing the
//!   exponential saving diamond merging exists for, with no signal that it had
//!   happened.
//! * It pruned to successors with a higher block id, assuming block numbering
//!   is a topological order. Any loop or unusual ordering breaks that.
//! * It re-ran per branch *per visit*, and exploration revisits blocks up to
//!   `MAX_BLOCK_VISITS` times, though post-dominance is a property of the CFG
//!   and does not change during exploration. It is computed once per body here.
//!
//! Post-dominance in the forward CFG is plain dominance in the reverse CFG, so
//! this is the iterative dominance algorithm of Cooper, Harvey and Kennedy
//! ("A Simple, Fast Dominance Algorithm", 2001) run on the reversed graph,
//! rooted at a virtual exit that every real exit flows to. Exact, uncapped, and
//! independent of block ordering.

use roast_ir::{Body, Terminator};

/// Immediate post-dominators for one body.
pub struct PostDom {
    /// Node count including the virtual exit, which is index `n_blocks`.
    exit: u32,
    /// `idom` in the reverse graph = immediate post-dominator in the forward
    /// one. `None` for a block from which no exit is reachable.
    ipdom: Vec<Option<u32>>,
    /// Reverse-post-order index per node; `usize::MAX` for unreachable nodes.
    rpo_pos: Vec<usize>,
}

/// Successors of a block in the forward CFG. `Return`, `Throw`, `Halt` and
/// `Diverge` all leave the body and have none.
pub fn successors(body: &Body, b: u32) -> Vec<u32> {
    match &body.blocks[b as usize].term {
        Terminator::Goto(t) => vec![t.0],
        Terminator::Branch { then_, else_, .. } => vec![then_.0, else_.0],
        Terminator::Switch { cases, default, .. } => {
            let mut v: Vec<u32> = cases.iter().map(|(_, t)| t.0).collect();
            v.push(default.0);
            v
        }
        _ => vec![],
    }
}

impl PostDom {
    pub fn new(body: &Body) -> PostDom {
        let n = body.blocks.len();
        let exit = n as u32;
        let total = n + 1;

        if n == 0 {
            return PostDom {
                exit,
                ipdom: vec![None; total],
                rpo_pos: vec![usize::MAX; total],
            };
        }

        // Reverse-CFG edges. Successors in the reverse graph are predecessors
        // in the forward graph, and vice versa.
        let mut fwd_succ: Vec<Vec<u32>> = vec![Vec::new(); total];
        for b in 0..n as u32 {
            let succs = successors(body, b);
            if succs.is_empty() {
                fwd_succ[b as usize].push(exit); // every exit flows to the virtual one
            } else {
                for s in succs {
                    if (s as usize) < n {
                        fwd_succ[b as usize].push(s);
                    }
                }
            }
        }
        let mut fwd_pred: Vec<Vec<u32>> = vec![Vec::new(); total];
        for b in 0..total as u32 {
            for &s in &fwd_succ[b as usize] {
                fwd_pred[s as usize].push(b);
            }
        }

        // RPO of the reverse graph from the virtual exit: DFS along forward
        // predecessors, then reverse the post-order.
        let mut visited = vec![false; total];
        let mut post: Vec<u32> = Vec::with_capacity(total);
        dfs_postorder(exit, &fwd_pred, &mut visited, &mut post);
        let rpo: Vec<u32> = post.iter().rev().copied().collect();

        let mut rpo_pos = vec![usize::MAX; total];
        for (i, &b) in rpo.iter().enumerate() {
            rpo_pos[b as usize] = i;
        }

        let mut ipdom: Vec<Option<u32>> = vec![None; total];
        ipdom[exit as usize] = Some(exit);

        let mut changed = true;
        while changed {
            changed = false;
            for &b in &rpo {
                if b == exit {
                    continue;
                }
                // Predecessors in the reverse graph = successors in the forward
                // graph.
                let mut new_ipdom: Option<u32> = None;
                for &s in &fwd_succ[b as usize] {
                    if ipdom[s as usize].is_none() {
                        continue; // not yet processed this round
                    }
                    new_ipdom = Some(match new_ipdom {
                        None => s,
                        Some(cur) => intersect(&ipdom, &rpo_pos, cur, s),
                    });
                }
                if new_ipdom.is_some() && ipdom[b as usize] != new_ipdom {
                    ipdom[b as usize] = new_ipdom;
                    changed = true;
                }
            }
        }

        PostDom {
            exit,
            ipdom,
            rpo_pos,
        }
    }

    /// The immediate post-dominator of `b`, or `None` when that is the virtual
    /// exit (i.e. nothing inside the body post-dominates it) or `b` cannot
    /// reach an exit at all.
    pub fn ipdom(&self, b: u32) -> Option<u32> {
        match self.ipdom.get(b as usize).copied().flatten() {
            Some(p) if p != self.exit && p != b => Some(p),
            _ => None,
        }
    }

    /// Does `p` post-dominate `b`?
    pub fn post_dominates(&self, p: u32, b: u32) -> bool {
        if p == b {
            return true;
        }
        let mut cur = b;
        for _ in 0..self.ipdom.len() {
            match self.ipdom.get(cur as usize).copied().flatten() {
                Some(next) if next == cur => return false, // the virtual exit
                Some(next) => {
                    if next == p {
                        return true;
                    }
                    cur = next;
                }
                None => return false,
            }
        }
        false
    }

    /// The nearest block post-dominating every block in `targets` — the join
    /// point for a branch or switch.
    ///
    /// `None` when the arms do not reconverge inside the body, or when one
    /// target post-dominates another. In that second case the arms are not
    /// independent and diamond-merging them would be wrong, so the caller
    /// must fall back to path forking.
    pub fn common(&self, targets: &[u32]) -> Option<u32> {
        let (first, rest) = targets.split_first()?;

        for (i, a) in targets.iter().enumerate() {
            for (j, b) in targets.iter().enumerate() {
                if i != j && self.post_dominates(*a, *b) {
                    return None;
                }
            }
        }

        let mut acc = *first;
        for t in rest {
            acc = intersect(&self.ipdom, &self.rpo_pos, acc, *t);
            if acc == self.exit {
                return None;
            }
        }
        if acc == self.exit || targets.contains(&acc) {
            return None;
        }
        Some(acc)
    }
}

/// Walk both fingers up the tree until they meet, comparing by reverse-post-
/// order position. Standard Cooper-Harvey-Kennedy `intersect`.
fn intersect(ipdom: &[Option<u32>], rpo_pos: &[usize], mut a: u32, mut b: u32) -> u32 {
    let pos = |x: u32| -> usize { rpo_pos.get(x as usize).copied().unwrap_or(usize::MAX) };
    let up = |x: u32| -> u32 { ipdom.get(x as usize).copied().flatten().unwrap_or(x) };

    let mut guard = 0usize;
    let limit = ipdom.len() * 4 + 8;
    while a != b {
        while pos(a) > pos(b) {
            let next = up(a);
            if next == a {
                break;
            }
            a = next;
            guard += 1;
            if guard > limit {
                return a;
            }
        }
        while pos(b) > pos(a) {
            let next = up(b);
            if next == b {
                break;
            }
            b = next;
            guard += 1;
            if guard > limit {
                return b;
            }
        }
        if pos(a) == pos(b) && a != b {
            // Two distinct unreachable nodes; no meaningful common ancestor.
            return a;
        }
        guard += 1;
        if guard > limit {
            return a;
        }
    }
    a
}

fn dfs_postorder(start: u32, succs: &[Vec<u32>], visited: &mut [bool], post: &mut Vec<u32>) {
    if visited[start as usize] {
        return;
    }
    visited[start as usize] = true;
    // Iterative, so a long chain cannot overflow the stack.
    let mut stack: Vec<(u32, usize)> = vec![(start, 0)];
    while let Some((b, i)) = stack.pop() {
        if i < succs[b as usize].len() {
            let next = succs[b as usize][i];
            stack.push((b, i + 1));
            if !visited[next as usize] {
                visited[next as usize] = true;
                stack.push((next, 0));
            }
        } else {
            post.push(b);
        }
    }
}
