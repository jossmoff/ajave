//! Post-dominator tree tests.
//!
//! The join point decides whether the BMC explorer diamond-merges a branch or
//! forks it, and forking is exponential. The search this replaced was capped at
//! 50 blocks and assumed block ids were a topological order, so it quietly
//! returned "no join" on anything larger or loopier — the tests at the end
//! cover exactly those cases.

use roast_engines::postdom::PostDom;
use roast_ir::*;

fn blk(id: u32, term: Terminator) -> Block {
    Block {
        id: BlockId(id),
        bytecode_offset: 0,
        stmts: vec![],
        term,
        exceptional: vec![],
    }
}

fn goto(id: u32, t: u32) -> Block {
    blk(id, Terminator::Goto(BlockId(t)))
}

fn branch(id: u32, t: u32, e: u32) -> Block {
    blk(
        id,
        Terminator::Branch {
            cond: Operand::int(1),
            then_: BlockId(t),
            else_: BlockId(e),
        },
    )
}

fn ret(id: u32) -> Block {
    blk(id, Terminator::Return(None))
}

fn body(blocks: Vec<Block>) -> Body {
    Body {
        key: MethodKey {
            class: "T".into(),
            name: "t".into(),
            desc: "()V".into(),
        },
        entry: BlockId(0),
        blocks,
        vars: vec![],
        obligations: vec![],
    }
}

// ---------------------------------------------------------------------------

#[test]
fn diamond_join_is_the_reconvergence_block() {
    //   0 -> 1, 2 ;  1 -> 3 ; 2 -> 3 ; 3 returns
    let b = body(vec![branch(0, 1, 2), goto(1, 3), goto(2, 3), ret(3)]);
    let pd = PostDom::new(&b);

    assert_eq!(pd.common(&[1, 2]), Some(3));
    assert_eq!(pd.ipdom(0), Some(3));
    assert_eq!(pd.ipdom(1), Some(3));
    assert_eq!(pd.ipdom(2), Some(3));
}

#[test]
fn nested_diamonds_resolve_to_the_inner_join_first() {
    //   0 -> 1,4 ; 1 -> 2,3 ; 2 -> 4 ; 3 -> 4 ; 4 -> 5 ; 5 returns
    let b = body(vec![
        branch(0, 1, 4),
        branch(1, 2, 3),
        goto(2, 4),
        goto(3, 4),
        goto(4, 5),
        ret(5),
    ]);
    let pd = PostDom::new(&b);

    assert_eq!(pd.common(&[2, 3]), Some(4), "inner arms join at 4");
    assert_eq!(
        pd.common(&[1, 4]),
        None,
        "4 post-dominates 1, not independent"
    );
    assert_eq!(pd.ipdom(1), Some(4));
}

#[test]
fn arms_that_both_return_have_no_join_inside_the_body() {
    //   0 -> 1,2 ; 1 returns ; 2 returns
    let b = body(vec![branch(0, 1, 2), ret(1), ret(2)]);
    let pd = PostDom::new(&b);

    assert_eq!(pd.common(&[1, 2]), None);
    assert_eq!(pd.ipdom(0), None, "the only common point is the exit");
}

#[test]
fn an_arm_that_returns_early_leaves_the_other_arm_as_the_join() {
    //   0 -> 1,2 ; 1 returns ; 2 -> 3 ; 3 returns
    let b = body(vec![branch(0, 1, 2), ret(1), goto(2, 3), ret(3)]);
    let pd = PostDom::new(&b);

    assert_eq!(pd.common(&[1, 2]), None, "no shared point before the exit");
    assert_eq!(pd.ipdom(2), Some(3));
}

#[test]
fn switch_arms_join_at_the_common_successor() {
    //   0 switches to 1,2,3 (default 3) ; all -> 4 ; 4 returns
    let b = body(vec![
        blk(
            0,
            Terminator::Switch {
                value: Operand::int(0),
                cases: vec![(1, BlockId(1)), (2, BlockId(2))],
                default: BlockId(3),
            },
        ),
        goto(1, 4),
        goto(2, 4),
        goto(3, 4),
        ret(4),
    ]);
    let pd = PostDom::new(&b);

    assert_eq!(pd.common(&[1, 2, 3]), Some(4));
}

#[test]
fn post_dominance_is_reflexive_and_follows_the_chain() {
    let b = body(vec![branch(0, 1, 2), goto(1, 3), goto(2, 3), ret(3)]);
    let pd = PostDom::new(&b);

    assert!(pd.post_dominates(0, 0), "reflexive");
    assert!(pd.post_dominates(3, 0), "3 is on every path out of 0");
    assert!(pd.post_dominates(3, 1));
    assert!(!pd.post_dominates(1, 0), "1 is only one arm");
    assert!(!pd.post_dominates(0, 3), "0 comes before 3");
}

// ---------------------------------------------------------------------------
// The cases the previous search got wrong
// ---------------------------------------------------------------------------

#[test]
fn a_join_beyond_fifty_blocks_is_still_found() {
    // The old search capped its sweep at 50 blocks and returned no join past
    // that, silently degrading diamond merging to path forking on any method
    // with a long body.
    //
    //   0 branches to two disjoint chains of 120 blocks each,
    //   both of which reconverge at block 240.
    let join = 240u32;
    let mut blocks: Vec<Block> = Vec::with_capacity(241);
    blocks.push(branch(0, 1, 121));
    for i in 1..=119u32 {
        blocks.push(goto(i, i + 1)); // chain A: 1 -> 2 -> ... -> 120
    }
    blocks.push(goto(120, join));
    for i in 121..=239u32 {
        blocks.push(goto(i, i + 1)); // chain B: 121 -> ... -> 240
    }
    blocks.push(ret(join));
    assert_eq!(blocks.len(), 241);

    let b = body(blocks);
    let pd = PostDom::new(&b);
    assert_eq!(
        pd.common(&[1, 121]),
        Some(join),
        "a join {join} blocks away must still be found"
    );
    assert_eq!(pd.ipdom(0), Some(join));
}

#[test]
fn a_backward_edge_does_not_confuse_the_join() {
    // The old search only followed successors with a *higher* block id, so any
    // loop broke it. Here the arms reconverge at 4, and 3 loops back to 1.
    //   0 -> 1,2 ; 1 -> 3 ; 3 -> 4 ; 2 -> 4 ; 4 returns
    let b = body(vec![
        branch(0, 1, 2),
        goto(1, 3),
        goto(2, 4),
        goto(3, 4),
        ret(4),
    ]);
    let pd = PostDom::new(&b);
    assert_eq!(pd.common(&[1, 2]), Some(4));
}

#[test]
fn a_join_at_a_lower_block_id_is_found() {
    // Nothing requires the join to be numbered after its arms.
    //   3 -> 4,5 ; 4 -> 1 ; 5 -> 1 ; 1 returns ; 0 -> 3
    let b = body(vec![
        goto(0, 3),
        ret(1),
        ret(2),
        branch(3, 4, 5),
        goto(4, 1),
        goto(5, 1),
    ]);
    let pd = PostDom::new(&b);
    assert_eq!(pd.common(&[4, 5]), Some(1));
}

#[test]
fn a_block_in_an_infinite_loop_has_no_post_dominator() {
    //   0 -> 1 ; 1 -> 2 ; 2 -> 1  (no exit reachable from 1 or 2)
    let b = body(vec![goto(0, 1), goto(1, 2), goto(2, 1)]);
    let pd = PostDom::new(&b);
    assert_eq!(pd.ipdom(1), None);
    assert_eq!(pd.ipdom(2), None);
}

#[test]
fn a_self_loop_terminates_rather_than_spinning() {
    let b = body(vec![branch(0, 0, 1), ret(1)]);
    let pd = PostDom::new(&b);
    assert_eq!(pd.ipdom(0), Some(1));
}

#[test]
fn an_empty_body_is_handled() {
    let b = body(vec![]);
    let pd = PostDom::new(&b);
    assert_eq!(pd.ipdom(0), None);
    assert_eq!(pd.common(&[0, 1]), None);
}

#[test]
fn a_single_returning_block_has_no_inner_post_dominator() {
    let b = body(vec![ret(0)]);
    let pd = PostDom::new(&b);
    assert_eq!(pd.ipdom(0), None);
}
