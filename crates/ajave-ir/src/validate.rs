//! Structural well-formedness of a `Body`.
//!
//! This states what a well-formed body *is*, which is the type's business
//! rather than any one consumer's — the lifter should be able to call it
//! without depending on the optimiser, and `ajave-opt` runs it after every
//! pass under `debug_assertions`.
//!
//! It converts a producer bug from a wrong verdict into a loud failure. Every
//! condition here corresponds to a defect that has actually occurred: an
//! obligation id used as if it were global, a block id from one method used to
//! index another, an obligation with no `Check` to reach it. `Body::block`,
//! `Body::var` and `Body::obligation` all index their vectors directly, so an
//! out-of-range id is either a panic or — worse, where a consumer does its own
//! bounds-dodging — a silent answer about the wrong program point.
//!
//! ## Deliberately structural only
//!
//! It cannot check that a producer preserved *meaning*. That is what
//! `tools/metamorphic.py` (meaning-preserving edits must not change a verdict)
//! and `tools/lifter_differential.py` (the IR interpreter must agree with a
//! real JVM) are for. Nor is "references a live var" checkable here in the
//! dataflow sense: without reaching definitions, in-range-and-described-by-a-
//! `VarInfo` is the strongest statement this pass can make, and it is the one
//! that distinguishes an id belonging to another `Body` from one belonging to
//! this one.
//!
//! ## Why a list rather than the first failure
//!
//! `defects` reports everything it finds. One lift bug typically produces the
//! same defect in many blocks, and the shape of that set is what identifies
//! the cause — a single error forces a fix-and-rerun loop over a producer that
//! may be wrong in several independent ways at once. `check` is the fail-fast
//! wrapper, for `debug_assert!`.

use crate::{rvalue_operands, BlockId, Body, Operand, Stmt, Terminator, VarId};
use std::fmt;

/// One way a `Body` is not well formed.
///
/// `site` is a human-readable position (`"bb3 branch condition"`), not a
/// machine key: a defect means the body's own ids cannot be trusted, so
/// returning one as structure would hand the reader the very value under
/// suspicion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Defect {
    /// No blocks at all. `entry` cannot name anything, and every consumer
    /// that starts by reading `body.block(body.entry)` panics.
    NoBlocks,
    EntryOutOfRange {
        entry: u32,
        blocks: usize,
    },
    /// `Body::block` indexes `blocks` directly, so a permuted or renumbered
    /// list silently returns a different block than the id names.
    BlockIdNotIndex {
        index: usize,
        id: u32,
    },
    /// Likewise `Body::obligation`.
    ObligationIdNotIndex {
        index: usize,
        id: u32,
    },
    /// A `VarId` with no `VarInfo` — so no type, and nothing to encode it as.
    VarOutOfRange {
        site: String,
        var: u32,
        vars: usize,
    },
    /// A `BlockId` outside this body. The historical instance: `current_block`
    /// was not restored after inlining, so a callee's id indexed the caller's
    /// blocks.
    /// An allocation names a position that is not where it appears.
    ///
    /// `AllocSite` is body-relative and derived from the allocation's own
    /// syntactic position, so a site disagreeing with where the statement
    /// actually sits means something rewrote statements without updating the
    /// sites — and an analysis keyed by site would then attribute two
    /// different objects to one cell, or one object to a cell nothing writes.
    /// `ajave-opt` moves statements, which is exactly how this would happen.
    AllocSiteMisplaced {
        at: BlockId,
        index: usize,
        claimed_block: BlockId,
        claimed_index: u32,
    },
    BlockOutOfRange {
        site: String,
        target: u32,
        blocks: usize,
    },
    ObligationOutOfRange {
        site: String,
        oid: u32,
        obligations: usize,
    },
    /// An obligation reached by a number of `Check` statements other than one.
    ///
    /// Zero means an engine discharging it is claiming something about a
    /// program point that does not exist. More than one makes "was this
    /// checked" ambiguous, and the id is the identity.
    CheckCount {
        oid: u32,
        count: usize,
    },
    /// A block whose terminator is `Diverge` but which still has successors.
    ///
    /// `Diverge` means control left the analysed fragment and we cannot say
    /// where it went. A successor claims we can. The two cannot both be true,
    /// and an over-approximating engine that reads the edge instead of the
    /// terminator concludes about states the lifter disclaimed.
    DivergeWithSuccessors {
        block: u32,
        successors: usize,
    },
}

impl fmt::Display for Defect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Defect::NoBlocks => write!(f, "has no blocks"),
            Defect::EntryOutOfRange { entry, blocks } => {
                write!(f, "entry bb{entry} is out of range ({blocks} blocks)")
            }
            Defect::BlockIdNotIndex { index, id } => {
                write!(f, "block at index {index} has id bb{id}")
            }
            Defect::ObligationIdNotIndex { index, id } => {
                write!(f, "obligation at index {index} has id #{id}")
            }
            Defect::VarOutOfRange { site, var, vars } => {
                write!(f, "{site} refers to v{var} of {vars}")
            }
            Defect::AllocSiteMisplaced {
                at,
                index,
                claimed_block,
                claimed_index,
            } => write!(
                f,
                "allocation at bb{}[{index}] claims site bb{}[{claimed_index}]",
                at.0, claimed_block.0
            ),
            Defect::BlockOutOfRange {
                site,
                target,
                blocks,
            } => write!(f, "{site} targets bb{target} of {blocks}"),
            Defect::ObligationOutOfRange {
                site,
                oid,
                obligations,
            } => write!(f, "{site} checks #{oid} of {obligations}"),
            Defect::CheckCount { oid, count } => write!(
                f,
                "obligation #{oid} is reached by {count} Check statements, expected 1"
            ),
            Defect::DivergeWithSuccessors { block, successors } => write!(
                f,
                "bb{block} diverges but has {successors} successor edge(s)"
            ),
        }
    }
}

/// Every way `body` is not well formed, in a stable order.
pub fn defects(body: &Body) -> Vec<Defect> {
    let nblocks = body.blocks.len();
    let nvars = body.vars.len();
    let nobs = body.obligations.len();
    let mut out = Vec::new();

    if nblocks == 0 {
        // Everything below indexes blocks; nothing more is knowable.
        return vec![Defect::NoBlocks];
    }
    if body.entry.0 as usize >= nblocks {
        out.push(Defect::EntryOutOfRange {
            entry: body.entry.0,
            blocks: nblocks,
        });
    }

    for (i, b) in body.blocks.iter().enumerate() {
        if b.id.0 as usize != i {
            out.push(Defect::BlockIdNotIndex {
                index: i,
                id: b.id.0,
            });
        }
    }
    for (i, o) in body.obligations.iter().enumerate() {
        if o.id.0 as usize != i {
            out.push(Defect::ObligationIdNotIndex {
                index: i,
                id: o.id.0,
            });
        }
    }

    let var = |out: &mut Vec<Defect>, v: VarId, site: String| {
        if (v.0 as usize) >= nvars {
            out.push(Defect::VarOutOfRange {
                site,
                var: v.0,
                vars: nvars,
            });
        }
    };
    let operand = |out: &mut Vec<Defect>, op: &Operand, site: String| {
        if let Operand::Var(v) = op {
            var(out, *v, site);
        }
    };
    let block = |out: &mut Vec<Defect>, b: BlockId, site: String| {
        if (b.0 as usize) >= nblocks {
            out.push(Defect::BlockOutOfRange {
                site,
                target: b.0,
                blocks: nblocks,
            });
        }
    };

    let mut checked: Vec<usize> = vec![0; nobs];
    for b in &body.blocks {
        let at = format!("bb{}", b.id.0);
        for (si, s) in b.stmts.iter().enumerate() {
            match s {
                Stmt::Assign(v, rv) => {
                    var(&mut out, *v, format!("{at} assignment target"));
                    for op in rvalue_operands(rv) {
                        operand(&mut out, op, format!("{at} rvalue"));
                    }
                    // An allocation must name where it actually is.
                    let site = match rv {
                        crate::Rvalue::New { site, .. } | crate::Rvalue::NewArray { site, .. } => {
                            Some(*site)
                        }
                        _ => None,
                    };
                    if let Some(site) = site {
                        if site.block != b.id || site.index as usize != si {
                            out.push(Defect::AllocSiteMisplaced {
                                at: b.id,
                                index: si,
                                claimed_block: site.block,
                                claimed_index: site.index,
                            });
                        }
                    }
                }
                Stmt::Check(oid) => {
                    let i = oid.0 as usize;
                    if i >= nobs {
                        out.push(Defect::ObligationOutOfRange {
                            site: at.clone(),
                            oid: oid.0,
                            obligations: nobs,
                        });
                    } else {
                        checked[i] += 1;
                    }
                }
                Stmt::Assume(op) | Stmt::MonitorEnter(op) | Stmt::MonitorExit(op) => {
                    operand(&mut out, op, format!("{at} statement"))
                }
                Stmt::PutStatic(_, op) => operand(&mut out, op, format!("{at} putstatic")),
                Stmt::PutField { obj, val, .. } => {
                    operand(&mut out, obj, format!("{at} putfield object"));
                    operand(&mut out, val, format!("{at} putfield value"));
                }
                Stmt::ArrayStore { arr, idx, val } => {
                    operand(&mut out, arr, format!("{at} arraystore array"));
                    operand(&mut out, idx, format!("{at} arraystore index"));
                    operand(&mut out, val, format!("{at} arraystore value"));
                }
                Stmt::Nop => {}
            }
        }
        match &b.term {
            Terminator::Goto(t) => block(&mut out, *t, format!("{at} goto")),
            Terminator::Branch { cond, then_, else_ } => {
                operand(&mut out, cond, format!("{at} branch condition"));
                block(&mut out, *then_, format!("{at} branch then"));
                block(&mut out, *else_, format!("{at} branch else"));
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                operand(&mut out, value, format!("{at} switch value"));
                for (_, t) in cases {
                    block(&mut out, *t, format!("{at} switch case"));
                }
                block(&mut out, *default, format!("{at} switch default"));
            }
            Terminator::Return(Some(op)) => operand(&mut out, op, format!("{at} return")),
            Terminator::Throw(op) => operand(&mut out, op, format!("{at} throw")),
            Terminator::Return(None) | Terminator::Halt | Terminator::Diverge(_) => {}
        }
        for e in &b.exceptional {
            block(&mut out, e.target, format!("{at} exceptional edge"));
        }
        // A diverging block's only possible successors are its exceptional
        // edges — `Terminator::Diverge` carries no target of its own.
        if matches!(b.term, Terminator::Diverge(_)) && !b.exceptional.is_empty() {
            out.push(Defect::DivergeWithSuccessors {
                block: b.id.0,
                successors: b.exceptional.len(),
            });
        }
    }

    // An obligation's safety condition is evaluated wherever an engine reads
    // it, not only at the `Check`, so an out-of-range var here is a defect
    // even though no statement mentions it. `concrete`'s `eval_check` reads it
    // through a store built elsewhere, which is exactly the seam where a stale
    // id would survive unnoticed.
    for o in &body.obligations {
        operand(
            &mut out,
            &o.cond,
            format!("obligation #{} condition", o.id.0),
        );
    }

    for (i, n) in checked.iter().enumerate() {
        if *n != 1 {
            out.push(Defect::CheckCount {
                oid: i as u32,
                count: *n,
            });
        }
    }
    out
}

/// Fail-fast form, for `debug_assert!` and for callers that only need a
/// message. The message names the method, which `Defect` deliberately does
/// not — a defect is about a site within one body, and the body knows its own
/// key.
pub fn check(body: &Body) -> Result<(), String> {
    let d = defects(body);
    if d.is_empty() {
        return Ok(());
    }
    let mut msg = format!("{}: {}", body.key, d[0]);
    for extra in &d[1..] {
        msg.push_str(&format!("; {extra}"));
    }
    Err(msg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    fn tiny() -> Body {
        Body {
            is_static: true,
            key: MethodKey {
                class: "C".into(),
                name: "m".into(),
                desc: "()V".into(),
            },
            entry: BlockId(0),
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts: vec![],
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
            vars: vec![VarInfo {
                kind: VarKind::Temp,
                ty: Ty::Int,
            }],
            obligations: vec![],
        }
    }

    fn ob(cond: Operand) -> Obligation {
        Obligation {
            id: ObligationId(0),
            kind: ObligationKind::Assertion,
            cond,
            bytecode_offset: 0,
            line: None,
            guarded: false,
        }
    }

    #[test]
    fn a_minimal_body_is_well_formed() {
        assert_eq!(defects(&tiny()), vec![]);
        assert!(check(&tiny()).is_ok());
    }

    #[test]
    fn an_empty_block_list_is_one_defect_and_not_a_panic() {
        let mut b = tiny();
        b.blocks.clear();
        // Not `EntryOutOfRange` as well: with nothing to index, the only
        // honest report is that there is nothing to index.
        assert_eq!(defects(&b), vec![Defect::NoBlocks]);
    }

    #[test]
    fn out_of_range_block_and_var_are_both_reported() {
        // The point of returning a list: one lift bug usually shows up at
        // several sites, and a first-failure validator hides the shape.
        let mut b = tiny();
        b.blocks[0]
            .stmts
            .push(Stmt::Assign(VarId(7), Rvalue::Use(Operand::Var(VarId(9)))));
        b.blocks[0].term = Terminator::Goto(BlockId(4));
        let d = defects(&b);
        assert_eq!(d.len(), 3, "{d:?}");
        assert!(d.iter().any(|x| matches!(
            x,
            Defect::VarOutOfRange {
                var: 7,
                vars: 1,
                ..
            }
        )));
        assert!(d.iter().any(|x| matches!(
            x,
            Defect::VarOutOfRange {
                var: 9,
                vars: 1,
                ..
            }
        )));
        assert!(d
            .iter()
            .any(|x| matches!(x, Defect::BlockOutOfRange { target: 4, .. })));
    }

    #[test]
    fn an_obligation_needs_exactly_one_check() {
        let mut b = tiny();
        b.obligations.push(ob(Operand::int(0)));
        assert_eq!(
            defects(&b),
            vec![Defect::CheckCount { oid: 0, count: 0 }],
            "an obligation with no Check names a program point that does not exist"
        );
        b.blocks[0].stmts.push(Stmt::Check(ObligationId(0)));
        assert_eq!(defects(&b), vec![]);
        b.blocks[0].stmts.push(Stmt::Check(ObligationId(0)));
        assert_eq!(defects(&b), vec![Defect::CheckCount { oid: 0, count: 2 }]);
    }

    #[test]
    fn a_check_naming_no_obligation_is_caught_without_indexing_it() {
        let mut b = tiny();
        b.blocks[0].stmts.push(Stmt::Check(ObligationId(3)));
        assert_eq!(
            defects(&b),
            vec![Defect::ObligationOutOfRange {
                site: "bb0".into(),
                oid: 3,
                obligations: 0
            }]
        );
    }

    #[test]
    fn an_obligation_condition_on_a_foreign_var_is_a_defect() {
        // The condition is the one operand no statement mentions, so it is the
        // one a statement-only walk cannot see. An `ObligationId` reused across
        // bodies lands here first.
        let mut b = tiny();
        b.obligations.push(ob(Operand::Var(VarId(5))));
        b.blocks[0].stmts.push(Stmt::Check(ObligationId(0)));
        assert_eq!(
            defects(&b),
            vec![Defect::VarOutOfRange {
                site: "obligation #0 condition".into(),
                var: 5,
                vars: 1
            }]
        );
    }

    #[test]
    fn diverge_must_not_have_successors() {
        let mut b = tiny();
        b.blocks[0].term = Terminator::Diverge("unmodelled".into());
        assert_eq!(defects(&b), vec![]);
        b.blocks[0].exceptional.push(ExcEdge {
            class: None,
            target: BlockId(0),
        });
        assert_eq!(
            defects(&b),
            vec![Defect::DivergeWithSuccessors {
                block: 0,
                successors: 1
            }]
        );
    }

    #[test]
    fn ids_must_equal_their_index() {
        let mut b = tiny();
        b.blocks[0].id = BlockId(1);
        b.obligations.push(Obligation {
            id: ObligationId(4),
            ..ob(Operand::int(0))
        });
        b.blocks[0].stmts.push(Stmt::Check(ObligationId(0)));
        let d = defects(&b);
        assert!(d.contains(&Defect::BlockIdNotIndex { index: 0, id: 1 }));
        assert!(d.contains(&Defect::ObligationIdNotIndex { index: 0, id: 4 }));
    }

    #[test]
    fn check_names_the_method_so_a_debug_assert_says_where() {
        let mut b = tiny();
        b.blocks[0].term = Terminator::Goto(BlockId(9));
        let msg = check(&b).unwrap_err();
        assert!(msg.starts_with("C.m()V: "), "{msg}");
        assert!(msg.contains("bb9"), "{msg}");
    }
}

#[cfg(test)]
mod alloc_site_tests {
    //! H0 (#98). An allocation must name where it actually is.

    use super::*;
    use crate::*;

    fn body_with(stmts: Vec<Stmt>) -> Body {
        Body {
            is_static: true,
            key: MethodKey {
                class: "Main".into(),
                name: "m".into(),
                desc: "()V".into(),
            },
            entry: BlockId(0),
            vars: vec![VarInfo {
                kind: VarKind::Local(0),
                ty: Ty::Ref,
            }],
            obligations: vec![],
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts,
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    #[test]
    fn a_correctly_placed_allocation_validates() {
        let b = body_with(vec![Stmt::Assign(
            VarId(0),
            Rvalue::New {
                class: "Foo".into(),
                site: AllocSite {
                    block: BlockId(0),
                    index: 0,
                },
            },
        )]);
        assert!(check(&b).is_ok(), "{:?}", defects(&b));
    }

    /// The failure mode this check exists for: `ajave-opt` moves statements,
    /// and a site left behind would make an analysis attribute two different
    /// objects to one cell, or one object to a cell nothing writes.
    #[test]
    fn a_site_that_disagrees_with_its_position_is_a_defect() {
        let b = body_with(vec![
            Stmt::Assign(VarId(0), Rvalue::Use(Operand::Const(Const::Null))),
            Stmt::Assign(
                VarId(0),
                Rvalue::New {
                    class: "Foo".into(),
                    // Sits at index 1, claims index 0 — what a statement
                    // reorder that forgot to update the site looks like.
                    site: AllocSite {
                        block: BlockId(0),
                        index: 0,
                    },
                },
            ),
        ]);
        let d = defects(&b);
        assert!(
            d.iter()
                .any(|x| matches!(x, Defect::AllocSiteMisplaced { .. })),
            "expected AllocSiteMisplaced, got {d:?}"
        );
    }

    #[test]
    fn an_array_allocation_is_checked_the_same_way() {
        let b = body_with(vec![Stmt::Assign(
            VarId(0),
            Rvalue::NewArray {
                elem: "I".into(),
                len: Operand::Const(Const::Int(3)),
                site: AllocSite {
                    block: BlockId(1),
                    index: 9,
                },
            },
        )]);
        assert!(defects(&b)
            .iter()
            .any(|x| matches!(x, Defect::AllocSiteMisplaced { .. })));
    }

    /// Two allocations in one block get distinct sites, which is the whole
    /// point: without identity the tree merged every instance of a class.
    #[test]
    fn two_allocations_in_one_block_have_distinct_sites() {
        let b = body_with(vec![
            Stmt::Assign(
                VarId(0),
                Rvalue::New {
                    class: "Foo".into(),
                    site: AllocSite {
                        block: BlockId(0),
                        index: 0,
                    },
                },
            ),
            Stmt::Assign(
                VarId(0),
                Rvalue::New {
                    class: "Foo".into(),
                    site: AllocSite {
                        block: BlockId(0),
                        index: 1,
                    },
                },
            ),
        ]);
        assert!(check(&b).is_ok(), "{:?}", defects(&b));
        let sites: Vec<AllocSite> = b.blocks[0]
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Assign(_, Rvalue::New { site, .. }) => Some(*site),
                _ => None,
            })
            .collect();
        assert_eq!(sites.len(), 2);
        assert_ne!(sites[0], sites[1], "same class, same block, same site");
    }
}
