//! State save/restore and ITE-merge logic for branch exploration.

use std::collections::HashSet;

use roast_core::smt::Term;
use roast_ir::VarId;

use super::{ExploreCtx, SavedState};

impl<'a> ExploreCtx<'a> {
    pub(super) fn save_state(&self) -> SavedState {
        SavedState {
            vars: self.vars.clone(),
            str_vars: self.str_vars.clone(),
            nondet_terms: self.nondet_terms.clone(),
            var_widths: self.var_widths.clone(),
            tainted: self.tainted.clone(),
            float_tainted: self.float_tainted.clone(),
            path_tainted: self.path_tainted,
            statics: self.statics.clone(),
            static_str: self.static_str.clone(),
            static_tainted: self.static_tainted.clone(),
            field_arrays: self.field_arrays.clone(),
            field_str: self.field_str.clone(),
            field_tainted: self.field_tainted.clone(),
            array_map: self.array_map.clone(),
            type_array: self.type_array,
            loop_visits: self.loop_visits.clone(),
            pc_len: self.path_constraints.len(),
        }
    }

    pub(super) fn restore_state(&mut self, s: SavedState) {
        self.vars = s.vars;
        self.str_vars = s.str_vars;
        self.nondet_terms = s.nondet_terms;
        self.var_widths = s.var_widths;
        self.tainted = s.tainted;
        self.float_tainted = s.float_tainted;
        self.path_tainted = s.path_tainted;
        self.statics = s.statics;
        self.static_str = s.static_str;
        self.static_tainted = s.static_tainted;
        self.field_arrays = s.field_arrays;
        self.field_str = s.field_str;
        self.field_tainted = s.field_tainted;
        self.array_map = s.array_map;
        self.type_array = s.type_array;
        self.loop_visits = s.loop_visits;
        self.path_constraints.truncate(s.pc_len);
    }

    /// ITE-merge two branch states into the current state.
    /// `cond` is the Bool term that selects `a` (true) vs `b` (false).
    /// `self` must hold the pre-branch state so that variables not modified
    /// on one side fall back to their pre-branch value instead of becoming
    /// unconstrained.
    pub(super) fn merge_states_ite(&mut self, cond: Term, a: &SavedState, b: &SavedState) {
        // Variables
        let all_vids: HashSet<VarId> = a.vars.keys().chain(b.vars.keys()).copied().collect();
        for vid in all_vids {
            let av = a.vars.get(&vid).copied();
            let bv = b.vars.get(&vid).copied();
            // Fall back to pre-branch value when a branch didn't touch the var
            let av = av.or_else(|| self.vars.get(&vid).copied());
            let bv = bv.or_else(|| self.vars.get(&vid).copied());
            match (av, bv) {
                (Some(t), Some(e)) if t == e => { self.vars.insert(vid, t); }
                (Some(t), Some(e)) => {
                    let m = self.solver.ite(cond, t, e);
                    self.vars.insert(vid, m);
                }
                (Some(t), None) => { self.vars.insert(vid, t); }
                (None, Some(e)) => { self.vars.insert(vid, e); }
                (None, None) => {}
            }
        }

        // Var widths — pick whichever was assigned
        for vid in a.var_widths.keys().chain(b.var_widths.keys()).copied().collect::<HashSet<_>>() {
            let w = a.var_widths.get(&vid).or_else(|| b.var_widths.get(&vid)).copied().unwrap_or(32);
            self.var_widths.insert(vid, w);
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

        // Instance field arrays
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

        // Array map: union
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

        // Type array
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

        // String vars
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

        // Instance field strings
        let all_fs: HashSet<_> = a.field_str.keys().chain(b.field_str.keys()).cloned().collect();
        self.field_str.clear();
        for k in all_fs {
            match (a.field_str.get(&k).copied(), b.field_str.get(&k).copied()) {
                (Some(t), Some(e)) if t == e => { self.field_str.insert(k, t); }
                (Some(t), Some(e)) => {
                    let m = self.solver.ite(cond, t, e);
                    self.field_str.insert(k, m);
                }
                (Some(t), None) => { self.field_str.insert(k, t); }
                (None, Some(e)) => { self.field_str.insert(k, e); }
                (None, None) => {}
            }
        }
    }

    /// ITE-merge a case state into an accumulator SavedState.
    /// `cond` selects `case` (true) vs `acc` (false).
    pub(super) fn merge_saved_into(&mut self, acc: &mut SavedState, cond: Term, case: &SavedState) {
        // Vars — fall back to pre-branch value (self.vars) for missing sides
        let all_vids: HashSet<VarId> = case.vars.keys().chain(acc.vars.keys()).copied().collect();
        for vid in all_vids {
            let cv = case.vars.get(&vid).copied().or_else(|| self.vars.get(&vid).copied());
            let av = acc.vars.get(&vid).copied().or_else(|| self.vars.get(&vid).copied());
            match (cv, av) {
                (Some(a), Some(b)) if a == b => { acc.vars.insert(vid, a); }
                (Some(a), Some(b)) => {
                    let m = self.solver.ite(cond, a, b);
                    acc.vars.insert(vid, m);
                }
                (Some(a), None) => { acc.vars.insert(vid, a); }
                (None, Some(_)) | (None, None) => {}
            }
        }
        // Var widths
        for (&vid, &w) in &case.var_widths {
            acc.var_widths.entry(vid).or_insert(w);
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
        // Instance field strings
        let all_fs: HashSet<_> = case.field_str.keys().chain(acc.field_str.keys()).cloned().collect();
        for k in all_fs {
            match (case.field_str.get(&k).copied(), acc.field_str.get(&k).copied()) {
                (Some(a), Some(b)) if a == b => {}
                (Some(a), Some(b)) => {
                    let m = self.solver.ite(cond, a, b);
                    acc.field_str.insert(k, m);
                }
                (Some(a), None) => { acc.field_str.insert(k, a); }
                _ => {}
            }
        }
    }

    /// Apply a merged SavedState to self.
    pub(super) fn apply_merged_state(&mut self, s: SavedState) {
        self.vars = s.vars;
        self.str_vars = s.str_vars;
        self.var_widths = s.var_widths;
        self.tainted = s.tainted;
        self.float_tainted = s.float_tainted;
        self.path_tainted = s.path_tainted;
        self.statics = s.statics;
        self.static_str = s.static_str;
        self.static_tainted = s.static_tainted;
        self.field_arrays = s.field_arrays;
        self.field_str = s.field_str;
        self.field_tainted = s.field_tainted;
        self.array_map = s.array_map;
        self.type_array = s.type_array;
    }

    /// Collect nondets from branch states, deduplicating by index.
    pub(super) fn collect_nondets_dedup(&mut self, states: &[&SavedState]) {
        let base_len = self.nondet_terms.len();
        for state in states {
            for nd in &state.nondet_terms[base_len..] {
                if !self.nondet_terms.iter().any(|(idx, _, _, _, _)| *idx == nd.0) {
                    self.nondet_terms.push(nd.clone());
                }
            }
        }
    }

    /// Collect nondets from two branch states (no dedup needed for binary branches).
    pub(super) fn collect_nondets_binary(&mut self, a: &SavedState, b: &SavedState) {
        let base_len = self.nondet_terms.len();
        for nd in &a.nondet_terms[base_len..] {
            self.nondet_terms.push(nd.clone());
        }
        for nd in &b.nondet_terms[base_len..] {
            self.nondet_terms.push(nd.clone());
        }
    }
}
