//! Conservative source ownership and projected-parent lifetime admission.
//!
//! Source .proj borrows a field: unlike Rust's compiler_alias, it does not
//! retain the Lean object. Model the source's protecting reference, not the
//! Rust allocation's memory-safety reference. The analysis intentionally
//! treats an unknown callee consuming the last root owner as a possible free.
//! A child retained by an explicit source .inc remains valid after that free.
//!
//! This is not an exact physical heap model: aliases outside the supported IR,
//! constructor-shell deletion with transferred fields, and specialized runtime
//! primitives need independent refinement evidence.
use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Default)]
struct ProjectedLifetime {
    // Projection/borrow-alias source identity. A field initially lives only
    // while its containing object keeps its original source-owned reference.
    parents: BTreeMap<usize, usize>,
    // The exact source .proj offset is required for constructor overwrite
    // and shell-deletion ownership transfer. Do not pool different fields.
    field_indices: BTreeMap<usize, usize>,
    // Lean's source .set writes one pointer slot without changing its RC.
    // Consecutive in-place rewrites can permute existing field owners.
    // Record origin-slot mapping and require a bijection before any other
    // instruction observes the constructor or leaves the current block.
    slot_permutations: BTreeMap<usize, BTreeMap<usize, usize>>,
    // A source Bool case establishes a path-local scalar constraint. Pass
    // that exact value through join parameters so repeated tests do not
    // invent infeasible combinations of unique and shared ownership.
    scalar_cases: BTreeMap<usize, u8>,
    // Credits created by a real owned input, source-producing declaration,
    // or explicitly emitted IR.inc; Rust Rc aliases do not count.
    owners: BTreeMap<usize, usize>,
    // Borrowed function formals are protected by a caller-owned reference.
    external: BTreeSet<usize>,
    // A source del or constructor mutation can invalidate a projected edge.
    invalidated: BTreeSet<usize>,
}

impl ProjectedLifetime {
    fn alive(&self, id: usize) -> bool {
        let mut node = id;
        for _ in 0..128 {
            if self.owners.get(&node).copied().unwrap_or(0) > 0 {
                return true;
            }
            if self.invalidated.contains(&node) {
                return false;
            }
            if self.external.contains(&node) {
                return true;
            }
            match self.parents.get(&node) {
                Some(parent) => node = *parent,
                None => return !self.owners.contains_key(&node),
            }
        }
        false
    }

    fn check(&self, id: usize, context: &str) -> CompilerResult<()> {
        // This pass establishes the safety of projected children only.
        // A direct root's physical RC can include aliases we have not
        // modeled. Do not make this conservative estimate into a global
        // rejection of otherwise-supported direct-call/isShared programs.
        if self.parents.contains_key(&id) && !self.alive(id) {
            return Err(CompilerError::new(
                RefusalKind::Decl,
                format!(
                    "projected/source object x_{id}: possible use after protecting parent release in {context}"
                ),
            ));
        }
        Ok(())
    }

    fn retain(&mut self, id: usize, n: usize) -> CompilerResult<()> {
        self.check(id, "source inc")?;
        if let Some(current) = self.owners.get_mut(&id) {
            *current = current.checked_add(n).ok_or(CompilerError::new(
                RefusalKind::ResourceLimit,
                "projected source reference-count overflow",
            ))?;
        }
        Ok(())
    }

    fn take(&mut self, id: usize, context: &str) -> CompilerResult<()> {
        self.check(id, context)?;
        if let Some(credits) = self.owners.get_mut(&id) {
            if *credits == 0 {
                if self.parents.contains_key(&id) {
                    return Err(CompilerError::new(
                        RefusalKind::Decl,
                        format!(
                            "projected/borrowed x_{id}: no owned source reference for {context}"
                        ),
                    ));
                }
                // Root alias counts are not complete. Only projected
                // variables admit the stronger source ownership claim.
                return Ok(());
            }
            *credits -= 1;
        }
        Ok(())
    }

    fn transfer_old_field(
        &mut self,
        parent: usize,
        index: usize,
        still_stored: bool,
    ) -> CompilerResult<()> {
        // Lean 4.34.1 lean_ctor_set overwrites a pointer slot without
        // decrementing the old value. lean_del_object frees the shell
        // without decrementing ANY field. Thus a previously projected
        // field can receive that existing source-owned reference when
        // the containing slot is replaced or the shell is deleted.
        //
        // A slot has exactly one source ownership credit. Multiple
        // projections of the same slot cannot all become owners.
        let matching: Vec<usize> = self
            .parents
            .iter()
            .filter(|(child, ancestor)| {
                **ancestor == parent
                    && self.field_indices.get(child) == Some(&index)
            })
            .map(|(child, _)| *child)
            .collect();
        if still_stored {
            // Writing the same pointer back leaves the constructor's
            // ownership in place; a projection remains borrowed.
            return Ok(());
        }
        if matching.len() == 1 {
            let child = matching[0];
            if let Some(owned) = self.owners.get_mut(&child) {
                *owned = owned.checked_add(1).ok_or(CompilerError::new(
                    RefusalKind::ResourceLimit,
                    "constructor field ownership transfer overflow",
                ))?;
            }
        } else {
            // Without a uniquely identified projection, we do not
            // fabricate one source owner for an arbitrary alias.
            for child in matching {
                self.invalidated.insert(child);
            }
        }
        Ok(())
    }

    fn settle_permutations(&mut self) -> CompilerResult<()> {
        for (target, updates) in &self.slot_permutations {
            let overwritten: BTreeSet<usize> = updates.keys().copied().collect();
            let sources: BTreeSet<usize> = updates.values().copied().collect();
            if overwritten != sources || sources.len() != updates.len() {
                return Err(CompilerError::new(
                    RefusalKind::Decl,
                    format!(
                        "source constructor x_{target}: incomplete or duplicate field-owner permutation"
                    ),
                ));
            }
        }
        self.slot_permutations.clear();
        Ok(())
    }

    fn invalidate_children(&mut self, parent: usize) {
        for (child, ancestor) in &self.parents {
            if *ancestor == parent {
                self.invalidated.insert(*child);
            }
        }
    }
}

impl Reader {
    pub(super) unsafe fn verify_projected_lifetimes(
        body: Obj,
        formals: &[(usize, bool)],
        functions: Option<&FunctionTable>,
    ) -> CompilerResult<()> {
        let mut state = ProjectedLifetime::default();
        for &(id, borrowed) in formals {
            if state.owners.insert(id, usize::from(!borrowed)).is_some() {
                return Err(CompilerError::new(
                    RefusalKind::Decl,
                    format!("duplicate lifetime source parameter x_{id}"),
                ));
            }
            if borrowed {
                state.external.insert(id);
            }
        }
        Self::lifetime_body(body, &mut state, functions, &BTreeMap::new(), 0, &mut 0)
    }

    unsafe fn lifetime_arg_id(arg: Obj) -> CompilerResult<Option<usize>> {
        Ok(if Self::checked_tag(arg, "Arg")? == 0 {
            Some(Self::var(Self::field(arg, 0)?)?)
        } else {
            None
        })
    }

    unsafe fn lifetime_read_arg(
        arg: Obj,
        state: &ProjectedLifetime,
        context: &str,
    ) -> CompilerResult<()> {
        if let Some(id) = Self::lifetime_arg_id(arg)? {
            state.check(id, context)?;
        }
        Ok(())
    }

    unsafe fn lifetime_transfer_arg(
        arg: Obj,
        state: &mut ProjectedLifetime,
        context: &str,
    ) -> CompilerResult<()> {
        if let Some(id) = Self::lifetime_arg_id(arg)? {
            state.take(id, context)?;
        }
        Ok(())
    }

    unsafe fn lifetime_expr(
        expr: Obj,
        state: &mut ProjectedLifetime,
        functions: Option<&FunctionTable>,
    ) -> CompilerResult<()> {
        match Self::checked_tag(expr, "Expr")? {
            0 | 7 => {
                let context = if Self::checked_tag(expr, "Expr")? == 0 {
                    "constructor field transfer"
                } else {
                    "closure capture"
                };
                for arg in Self::array(Self::field(expr, 1)?)? {
                    Self::lifetime_transfer_arg(arg, state, context)?;
                }
            }
            3 | 9 => {
                let id = Self::var(Self::field(expr, 1)?)?;
                state.check(id, "projection or box")?;
            }
            5 => {
                let id = Self::var(Self::field(expr, 2)?)?;
                state.check(id, "scalar field projection")?;
            }
            6 => {
                let name = Self::name(Self::field(expr, 0)?, 0)?;
                let args = Self::array(Self::field(expr, 1)?)?;
                let signature = functions.and_then(|table| table.get(&name));
                // The production primitive validator supplies the canonical
                // rejection for unknown operations and malformed arities.
                if signature.is_none()
                    && !is_nat_primitive(&name)
                    && !is_primitive(&name)
                    && runtime_primitive_spec(&name).is_none()
                    && !matches!(
                        name.as_str(),
                        "Array.mkEmpty"
                            | "Array.getInternal"
                            | "Array.getInternalBorrowed"
                            | "Array.set!"
                    )
                {
                    return Ok(());
                }
                if let Some(sig) = signature {
                    if args.len() != sig.borrows.len() {
                        return Ok(());
                    }
                }
                for (i, arg) in args.into_iter().enumerate() {
                    let borrowed = signature.map_or_else(
                        || Self::primitive_borrows(&name, i),
                        |sig| sig.borrows[i],
                    );
                    if borrowed {
                        Self::lifetime_read_arg(arg, state, "borrowed call")?;
                    } else {
                        Self::lifetime_transfer_arg(arg, state, "owned call")?;
                    }
                }
            }
            8 => {
                let id = Self::var(Self::field(expr, 0)?)?;
                state.take(id, "indirect closure application")?;
                for arg in Self::array(Self::field(expr, 1)?)? {
                    Self::lifetime_transfer_arg(arg, state, "indirect argument")?;
                }
            }
            10 | 12 => {
                let id = Self::var(Self::field(expr, 0)?)?;
                state.check(id, "unbox or sharing observation")?;
            }
            // Other expression types are checked by the ordinary IR reader;
            // do not replace its structured unsupported-operation diagnosis.
            _ => {}
        }
        Ok(())
    }

    unsafe fn lifetime_bool_arm(alt: Obj) -> CompilerResult<Option<u8>> {
        if Self::checked_tag(alt, "Alt")? != 0 {
            return Ok(None);
        }
        let info = Self::field(alt, 0)?;
        let name = Self::name(Self::field(info, 0)?, 0)?;
        Ok(match name.as_str() {
            "Bool.false" => Some(0),
            "Bool.true" => Some(1),
            _ => None,
        })
    }

    unsafe fn lifetime_body(
        mut body: Obj,
        state: &mut ProjectedLifetime,
        functions: Option<&FunctionTable>,
        joins: &BTreeMap<usize, (Obj, Vec<(usize, bool)>)>,
        depth: usize,
        steps: &mut usize,
    ) -> CompilerResult<()> {
        if depth > 128 {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "projected lifetime join/branch nesting exceeded 128",
            ));
        }
        loop {
            *steps += 1;
            if *steps > 100_000 {
                return Err(CompilerError::new(
                    RefusalKind::ResourceLimit,
                    "projected lifetime IR traversal exceeded 100000 instructions",
                ));
            }
            // Non-set operations cannot run in the middle of an unfinished
            // permutation. The C runtime temporarily contains duplicates
            // until the matching slots are restored; inc/dec/calls/cases
            // would otherwise observe an unjustified ownership state.
            if Self::checked_tag(body, "FnBody")? != 2 {
                state.settle_permutations()?;
            }
            match Self::body_view(body)? {
                FnBodyView::Decl {
                    defined,
                    ty,
                    expr,
                    next,
                } => {
                    let target = Self::var(defined)?;
                    let value_type = is_value_type(Self::ty(ty)?);
                    let projection = value_type && Self::checked_tag(expr, "Expr")? == 3;
                    let parent = if projection {
                        Some(Self::var(Self::field(expr, 1)?)?)
                    } else {
                        None
                    };
                    Self::lifetime_expr(expr, state, functions)?;
                    if value_type {
                        if state.owners.insert(target, usize::from(!projection)).is_some() {
                            return Err(CompilerError::new(
                                RefusalKind::Decl,
                                format!("duplicate lifetime source variable x_{target}"),
                            ));
                        }
                        if let Some(parent) = parent {
                            state.parents.insert(target, parent);
                            state.field_indices.insert(
                                target,
                                Self::nat(Self::field(expr, 0)?)?,
                            );
                        }
                    }
                    body = next;
                }
                FnBodyView::Inc {
                    target,
                    persistent,
                    next,
                    ..
                } => {
                    if !persistent {
                        state.retain(
                            Self::var(target)?,
                            Self::nat(Self::field(body, 1)?)?,
                        )?;
                    }
                    body = next;
                }
                FnBodyView::Dec {
                    target,
                    persistent,
                    next,
                    ..
                } => {
                    if !persistent {
                        state.take(Self::var(target)?, "source dec")?;
                    }
                    body = next;
                }
                FnBodyView::Delete { target, next } => {
                    let id = Self::var(target)?;
                    state.take(id, "source del")?;
                    // The pinned C runtime frees only the shell. Each field
                    // slot contributes at most one source-owned reference
                    // to a uniquely projected child; nested descendants
                    // remain protected by that child's transferred owner.
                    let indices: BTreeSet<usize> = state
                        .parents
                        .iter()
                        .filter(|(_, parent)| **parent == id)
                        .filter_map(|(child, _)| state.field_indices.get(child).copied())
                        .collect();
                    for index in indices {
                        state.transfer_old_field(id, index, false)?;
                    }
                    state.invalidated.insert(id);
                    body = next;
                }
                FnBodyView::Set {
                    target,
                    index,
                    value,
                    next,
                } => {
                    let id = Self::var(target)?;
                    let slot = Self::nat(index)?;
                    state.check(id, "constructor mutation")?;
                    let new_value = Self::lifetime_arg_id(value)?;
                    let source_slot = new_value.and_then(|child| {
                        (state.parents.get(&child) == Some(&id))
                            .then(|| state.field_indices.get(&child).copied())
                            .flatten()
                    });
                    if let Some(origin) = source_slot {
                        if state.owners.get(&id).copied() != Some(1)
                            || state.external.contains(&id)
                        {
                            return Err(CompilerError::new(
                                RefusalKind::Decl,
                                format!("source constructor x_{id}: unverified unique field permutation"),
                            ));
                        }
                        // This is not an owned argument transfer. It is a
                        // temporary in-place rewrite of the SAME object's
                        // existing source pointer slots, with no RC delta.
                        // The completed mapping must be a permutation.
                        state.slot_permutations.entry(id).or_default().insert(slot, origin);
                    } else {
                        state.settle_permutations()?;
                        Self::lifetime_transfer_arg(value, state, "constructor field set")?;
                        state.transfer_old_field(id, slot, false)?;
                    }
                    body = next;
                }
                FnBodyView::ScalarSet { target, next, .. } => {
                    let id = Self::var(target)?;
                    state.check(id, "scalar constructor mutation")?;
                    state.invalidate_children(id);
                    body = next;
                }
                FnBodyView::Join {
                    id,
                    params,
                    value,
                    next,
                } => {
                    let id = Self::var(id)?;
                    let mut scoped = joins.clone();
                    let mut formals = Vec::new();
                    for param in Self::array(params)? {
                        formals.push((
                            Self::var(Self::field(param, 0)?)?,
                            is_value_type(Self::ty(Self::field(param, 1)?)?)
                                && Self::param_borrow(param)?,
                        ));
                    }
                    if scoped.insert(id, (value, formals)).is_some() {
                        return Err(CompilerError::new(
                            RefusalKind::Decl,
                            format!("projected lifetime join point {id} is shadowed"),
                        ));
                    }
                    return Self::lifetime_body(
                        next,
                        state,
                        functions,
                        &scoped,
                        depth + 1,
                        steps,
                    );
                }
                FnBodyView::Case {
                    scrutinee,
                    alternatives,
                } => {
                    let tested = Self::var(scrutinee)?;
                    state.check(tested, "case scrutinee")?;
                    let alts = Self::array(alternatives)?;
                    // The pinned source stores Bool in UInt8 IR
                    // representation. Discriminate using the ORIGINAL
                    // constructor identities, not the scalar storage
                    // type name (which is "UInt8", not "Bool").
                    let mut bool_case = false;
                    for alt in &alts {
                        if Self::lifetime_bool_arm(*alt)?.is_some() {
                            bool_case = true;
                            break;
                        }
                    }
                    let known = if bool_case {
                        state.scalar_cases.get(&tested).copied()
                    } else {
                        None
                    };
                    let matching_ctor = if let Some(expected) = known {
                        let mut present = false;
                        for alt in &alts {
                            if Self::lifetime_bool_arm(*alt)? == Some(expected) {
                                present = true;
                            }
                        }
                        present
                    } else {
                        false
                    };
                    for alt in alts {
                        let constructor_value = if bool_case {
                            Self::lifetime_bool_arm(alt)?
                        } else {
                            None
                        };
                        if let Some(expected) = known {
                            if matching_ctor {
                                if constructor_value != Some(expected) {
                                    continue;
                                }
                            } else if Self::checked_tag(alt, "Alt")? == 0 {
                                // No matching constructor: only the
                                // source default arm is executable.
                                continue;
                            }
                        }
                        let arm = match Self::alt_view(alt)? {
                            AltView::Constructor { body } | AltView::Default { body } => body,
                        };
                        let mut path = state.clone();
                        if let Some(value) = constructor_value {
                            path.scalar_cases.insert(tested, value);
                        }
                        Self::lifetime_body(
                            arm,
                            &mut path,
                            functions,
                            joins,
                            depth + 1,
                            steps,
                        )?;
                    }
                    return Ok(());
                }
                FnBodyView::Jump { id, arguments } => {
                    let id = Self::var(id)?;
                    let Some((value, formals)) = joins.get(&id) else {
                        // The ordinary reader owns the unknown-target error.
                        return Ok(());
                    };
                    let args = Self::array(arguments)?;
                    if args.len() != formals.len() {
                        return Ok(());
                    }
                    let mut destination = state.clone();
                    for (arg, (formal, borrowed)) in args.into_iter().zip(formals.iter()) {
                        let actual = Self::lifetime_arg_id(arg)?;
                        if let Some(actual) = actual {
                            destination.check(actual, "join argument")?;
                            if let Some(value) = destination.scalar_cases.get(&actual).copied() {
                                destination.scalar_cases.insert(*formal, value);
                            }
                            if *borrowed {
                                destination.owners.insert(*formal, 0);
                                destination.parents.insert(*formal, actual);
                            } else {
                                destination.take(actual, "owned join argument")?;
                                destination.owners.insert(*formal, 1);
                                destination.parents.remove(formal);
                                // A source owned join parameter is another
                                // name for the SAME heap object, not a new
                                // allocation. Redirect already projected
                                // field dependents to the transferred owner.
                                let children: Vec<usize> = destination
                                    .parents
                                    .iter()
                                    .filter(|(_, parent)| **parent == actual)
                                    .map(|(child, _)| *child)
                                    .collect();
                                for child in children {
                                    destination.parents.insert(child, *formal);
                                }
                            }
                        }
                    }
                    return Self::lifetime_body(
                        *value,
                        &mut destination,
                        functions,
                        joins,
                        depth + 1,
                        steps,
                    );
                }
                FnBodyView::Return { value } => {
                    Self::lifetime_transfer_arg(value, state, "return value")?;
                    return Ok(());
                }
            }
        }
    }
}
