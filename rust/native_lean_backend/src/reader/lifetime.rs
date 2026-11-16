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
                    // lean_del_object frees the shell, NOT its transferred
                    // children. We do not assume those transfer obligations
                    // have been established for the source projection graph.
                    state.invalidated.insert(id);
                    body = next;
                }
                FnBodyView::Set {
                    target,
                    value,
                    next,
                    ..
                } => {
                    let id = Self::var(target)?;
                    state.check(id, "constructor mutation")?;
                    Self::lifetime_transfer_arg(value, state, "constructor field set")?;
                    state.invalidate_children(id);
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
                    state.check(Self::var(scrutinee)?, "case scrutinee")?;
                    for alt in Self::array(alternatives)? {
                        let arm = match Self::alt_view(alt)? {
                            AltView::Constructor { body } | AltView::Default { body } => body,
                        };
                        let mut path = state.clone();
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
                            if *borrowed {
                                destination.owners.insert(*formal, 0);
                                destination.parents.insert(*formal, actual);
                            } else {
                                destination.take(actual, "owned join argument")?;
                                destination.owners.insert(*formal, 1);
                                destination.parents.remove(formal);
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
