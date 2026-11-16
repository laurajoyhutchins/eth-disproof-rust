//! Source IR direct borrowed-parameter transfer admission.
//!
//! Lean's Param.borrow means the callee does not own an incoming reference.
//! A borrowed argument may be read without changing its source count, but
//! transferring that *same source variable* into an owned result, field,
//! closure capture, or owned call requires an explicit prior source inc.
//!
//! Direct borrowed formals and their transitive constructor projections are
//! tracked by source VarId. Join parameter flags and jump arguments come from
//! pinned Lean IR. Call-result aliasing and other heap effects remain outside
//! the certified subset; Rust Rc aliases never grant source ownership.
//! The Rust compiler must never manufacture ownership from Rc::clone.
use super::*;
use std::collections::BTreeMap;

impl Reader {
    pub(super) unsafe fn verify_direct_borrow_transfers(
        body: Obj,
        borrowed: &[usize],
        functions: Option<&FunctionTable>,
    ) -> CompilerResult<()> {
        if borrowed.is_empty() {
            return Ok(());
        }
        let mut rights = BTreeMap::new();
        for &id in borrowed {
            if rights.insert(id, 0usize).is_some() {
                return Err(CompilerError::new(
                    RefusalKind::Decl,
                    "duplicate borrowed parameter identity",
                ));
            }
        }
        Self::borrow_body(body, &mut rights, functions, &BTreeMap::new(), 0, &mut 0)
    }

    unsafe fn borrow_take(
        arg: Obj,
        rights: &mut BTreeMap<usize, usize>,
        context: &str,
    ) -> CompilerResult<()> {
        if Self::checked_tag(arg, "Arg")? != 0 {
            return Ok(());
        }
        let id = Self::var(Self::field(arg, 0)?)?;
        if let Some(remaining) = rights.get_mut(&id) {
            if *remaining == 0 {
                return Err(CompilerError::new(
                    RefusalKind::Decl,
                    format!("borrowed parameter x_{id}: unverified owned transfer in {context} without source inc"),
                ));
            }
            *remaining -= 1;
        }
        Ok(())
    }

    // For a source runtime primitive, the owner policy is deliberately
    // narrower than the accepted value-semantic primitive inventory. Other
    // primitive calls with direct borrowed objects are refused.
    fn primitive_borrows(name: &str, index: usize) -> bool {
        match name {
            "Nat.add"
            | "Nat.sub"
            | "Nat.mul"
            | "Nat.div"
            | "Nat.mod"
            | "Nat.decEq"
            | "Nat.decLt"
            | "Nat.decLe"
            | "Int.add"
            | "String.append"
            | "String.length"
            | "String.utf8ByteSize" => true,
            "Array.size" | "Array.getInternal" | "Array.getInternalBorrowed" => index == 1,
            _ => false,
        }
    }

    unsafe fn borrow_expr(
        expr: Obj,
        rights: &mut BTreeMap<usize, usize>,
        functions: Option<&FunctionTable>,
    ) -> CompilerResult<()> {
        match Self::checked_tag(expr, "Expr")? {
            0 => {
                for arg in Self::array(Self::field(expr, 1)?)? {
                    Self::borrow_take(arg, rights, "constructor field")?;
                }
            }
            6 => {
                let name = Self::name(Self::field(expr, 0)?, 0)?;
                let args = Self::array(Self::field(expr, 1)?)?;
                let signature = functions.and_then(|table| table.get(&name));
                // Preserve the production primitive validator as the sole
                // authority for unknown/unsupported names. Otherwise this
                // ownership preflight would hide the canonical structured
                // Primitive refusal behind a less informative borrow error.
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
                    if args.len() != sig.params.len() || args.len() != sig.borrows.len() {
                        return Err(CompilerError::new(
                            RefusalKind::Decl,
                            format!("{name}: source borrowed-call arity mismatch"),
                        ));
                    }
                }
                for (index, arg) in args.into_iter().enumerate() {
                    let borrows = signature.map_or_else(
                        || Self::primitive_borrows(&name, index),
                        |sig| sig.borrows[index],
                    );
                    if !borrows {
                        Self::borrow_take(
                            arg,
                            rights,
                            &format!("call to {name} argument {index}"),
                        )?;
                    }
                }
            }
            7 => {
                // PAP storage takes ownership of each captured reference,
                // even when the eventual function formal is borrowed.
                for arg in Self::array(Self::field(expr, 1)?)? {
                    Self::borrow_take(arg, rights, "partial application capture")?;
                }
            }
            8 => {
                // A dynamic AP consumes the closure and its boxed operands.
                let id = Self::var(Self::field(expr, 0)?)?;
                if rights.contains_key(&id) {
                    return Err(CompilerError::new(
                        RefusalKind::Decl,
                        format!(
                            "borrowed parameter x_{id}: unverified indirect closure consumption"
                        ),
                    ));
                }
                for arg in Self::array(Self::field(expr, 1)?)? {
                    Self::borrow_take(arg, rights, "indirect application")?;
                }
            }
            // Projections, scalar reads, and tests cannot by themselves
            // transfer a reference to the directly borrowed parameter.
            _ => {}
        }
        Ok(())
    }

    unsafe fn borrow_body(
        mut body: Obj,
        rights: &mut BTreeMap<usize, usize>,
        functions: Option<&FunctionTable>,
        joins: &BTreeMap<usize, Vec<bool>>,
        depth: usize,
        steps: &mut usize,
    ) -> CompilerResult<()> {
        if depth > 128 {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "borrowed parameter control-flow nesting limit",
            ));
        }
        loop {
            *steps += 1;
            if *steps > 100_000 {
                return Err(CompilerError::new(
                    RefusalKind::ResourceLimit,
                    "borrowed parameter instruction limit",
                ));
            }
            match Self::body_view(body)? {
                FnBodyView::Decl {
                    defined,
                    ty,
                    expr,
                    next,
                } => {
                    Self::borrow_expr(expr, rights, functions)?;
                    // A source .proj borrows the parent's pointer field. A
                    // projected object from a tracked source starts with no
                    // transferable reference, including nested projections.
                    if is_value_type(Self::ty(ty)?) && Self::checked_tag(expr, "Expr")? == 3 {
                        let source = Self::var(Self::field(expr, 1)?)?;
                        if rights.contains_key(&source) {
                            let target = Self::var(defined)?;
                            if rights.insert(target, 0).is_some() {
                                return Err(CompilerError::new(
                                    RefusalKind::Decl,
                                    format!(
                                        "borrowed projection x_{target} shadows a tracked source"
                                    ),
                                ));
                            }
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
                    let id = Self::var(target)?;
                    if !persistent {
                        if let Some(owned) = rights.get_mut(&id) {
                            let n = Self::nat(Self::field(body, 1)?)?;
                            *owned = owned.checked_add(n).ok_or(CompilerError::new(
                                RefusalKind::ResourceLimit,
                                "borrowed parameter inc overflow",
                            ))?;
                        }
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
                        let id = Self::var(target)?;
                        if let Some(owned) = rights.get_mut(&id) {
                            if *owned == 0 {
                                return Err(CompilerError::new(
                                    RefusalKind::Decl,
                                    format!(
                                        "borrowed parameter x_{id}: source dec without owned inc"
                                    ),
                                ));
                            }
                            *owned -= 1;
                        }
                    }
                    body = next;
                }
                FnBodyView::Delete { target, next } => {
                    let id = Self::var(target)?;
                    if let Some(owned) = rights.get_mut(&id) {
                        if *owned == 0 {
                            return Err(CompilerError::new(
                                RefusalKind::Decl,
                                format!("borrowed parameter x_{id}: source del without owned inc"),
                            ));
                        }
                        *owned -= 1;
                    }
                    body = next;
                }
                FnBodyView::Set {
                    target,
                    value,
                    next,
                    ..
                } => {
                    Self::borrow_take(value, rights, "constructor field mutation")?;
                    let id = Self::var(target)?;
                    if rights.contains_key(&id) {
                        return Err(CompilerError::new(
                            RefusalKind::Decl,
                            format!("borrowed parameter x_{id}: unverified in-place mutation"),
                        ));
                    }
                    body = next;
                }
                FnBodyView::ScalarSet { target, next, .. } => {
                    let id = Self::var(target)?;
                    if rights.contains_key(&id) {
                        return Err(CompilerError::new(
                            RefusalKind::Decl,
                            format!("borrowed parameter x_{id}: unverified in-place mutation"),
                        ));
                    }
                    body = next;
                }
                FnBodyView::Join {
                    id,
                    params,
                    value,
                    next,
                } => {
                    let id = Self::var(id)?;
                    let mut join_rights = rights.clone();
                    let mut formal_borrows = Vec::new();
                    for param in Self::array(params)? {
                        let param_id = Self::var(Self::field(param, 0)?)?;
                        let is_object = is_value_type(Self::ty(Self::field(param, 1)?)?);
                        let borrowed = is_object && Self::param_borrow(param)?;
                        formal_borrows.push(borrowed);
                        if borrowed && join_rights.insert(param_id, 0).is_some() {
                            return Err(CompilerError::new(
                                RefusalKind::Decl,
                                format!(
                                    "borrowed join parameter x_{param_id} shadows a tracked source"
                                ),
                            ));
                        }
                    }
                    let mut scoped = joins.clone();
                    if scoped.insert(id, formal_borrows).is_some() {
                        return Err(CompilerError::new(
                            RefusalKind::Decl,
                            format!("borrowed provenance cannot verify shadowed join point {id}"),
                        ));
                    }
                    Self::borrow_body(
                        value,
                        &mut join_rights,
                        functions,
                        &scoped,
                        depth + 1,
                        steps,
                    )?;
                    // Rights created in the join body cannot authorize a
                    // transfer in the lexical predecessor of its jump.
                    return Self::borrow_body(next, rights, functions, &scoped, depth + 1, steps);
                }
                FnBodyView::Case { alternatives, .. } => {
                    for alt in Self::array(alternatives)? {
                        let branch = match Self::alt_view(alt)? {
                            AltView::Constructor { body } | AltView::Default { body } => body,
                        };
                        let mut branch_rights = rights.clone();
                        Self::borrow_body(
                            branch,
                            &mut branch_rights,
                            functions,
                            joins,
                            depth + 1,
                            steps,
                        )?;
                    }
                    return Ok(());
                }
                FnBodyView::Jump { id, arguments } => {
                    let jump_id = Self::var(id)?;
                    let args = Self::array(arguments)?;
                    if let Some(formals) = joins.get(&jump_id) {
                        if args.len() != formals.len() {
                            // Preserve the ordinary reader's source join
                            // arity diagnostic rather than replacing it.
                            return Ok(());
                        }
                        for (index, (arg, borrowed)) in
                            args.into_iter().zip(formals.iter()).enumerate()
                        {
                            if !borrowed {
                                Self::borrow_take(
                                    arg,
                                    rights,
                                    &format!("join point {jump_id} argument {index}"),
                                )?;
                            }
                        }
                    } else {
                        for arg in args {
                            if Self::checked_tag(arg, "Arg")? == 0 {
                                let var = Self::var(Self::field(arg, 0)?)?;
                                if rights.contains_key(&var) {
                                    return Err(CompilerError::new(
                                        RefusalKind::Decl,
                                        format!("borrowed parameter x_{var}: unverified join argument ownership"),
                                    ));
                                }
                            }
                        }
                    }
                    return Ok(());
                }
                FnBodyView::Return { value } => {
                    Self::borrow_take(value, rights, "return value")?;
                    return Ok(());
                }
            }
        }
    }
}
