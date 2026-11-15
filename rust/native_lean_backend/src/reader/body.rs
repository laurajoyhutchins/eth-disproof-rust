//! Lexically scoped FnBody lowering, sharing and joins.
use super::*;

impl Reader {
    pub(super) unsafe fn body(
        mut x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> CompilerResult<()> {
        if depth > 128 {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "IR control-flow nesting limit",
            ));
        }
        loop {
            *count += 1;
            if *count > 100_000 {
                return Err(CompilerError::new(
                    RefusalKind::ResourceLimit,
                    "IR instruction limit exceeded",
                ));
            }
            match Self::body_view(x)? {
                FnBodyView::Decl {
                    defined,
                    ty: decl_ty,
                    expr,
                    next,
                } => {
                    // vdecl(x, ty, expr, body)
                    let name = Self::var(defined)?;
                    let ty = Self::ty(decl_ty)?;
                    // Only top-level array candidates can transfer ownership.
                    // Their full tails are scanned for references through
                    // branch and join bodies, conservatively preserving aliases.
                    let straight_line = depth == 0 && ctx.joins.is_empty();
                    let tail = next;
                    let consumed_array = if straight_line {
                        Self::consumable_array(expr, tail)?
                    } else {
                        None
                    };
                    let consumed_calls = if straight_line {
                        Self::consumable_call(expr, tail, ctx.functions)?
                    } else {
                        BTreeSet::new()
                    };
                    let consumed_ap = if straight_line {
                        Self::consumable_ap(expr, tail)?
                    } else {
                        None
                    };
                    let value = Self::expr(
                        expr,
                        ty,
                        env,
                        ctx,
                        consumed_array,
                        &consumed_calls,
                        consumed_ap,
                    )?;
                    if env.insert(name, ty).is_some() {
                        return Err(CompilerError::new(
                            RefusalKind::FnBody,
                            format!("variable x_{name} defined more than once"),
                        ));
                    }
                    writeln!(code, "    let x_{name}: {} = {value};", rust_type(ty)).unwrap();
                    x = next;
                }
                FnBodyView::Join {
                    id: join_id,
                    params,
                    value,
                    next,
                } => {
                    // jdecl(joinId, params, value, continuation): the join's
                    // body is a typed, lexically captured Rust closure. Its
                    // declaration is deliberately absent from its own value
                    // scope: recursive join jumps are refused, not miscompiled.
                    let id = Self::var(join_id)?;
                    if ctx.joins.contains_key(&id) {
                        return Err(CompilerError::new(
                            RefusalKind::FnBody,
                            format!("join point {id} shadows a visible join"),
                        ));
                    }
                    let mut param_types = Vec::new();
                    let join_shared = Self::shared_observations(value)?;
                    let mut value_env = env.clone();
                    let mut param_code = Vec::new();
                    for param in Self::array(params)? {
                        let var = Self::var(Self::field(param, 0)?)?;
                        let ty = Self::ty(Self::field(param, 1)?)?;
                        if Self::param_borrow(param)? && join_shared.contains(&var) {
                            return Err(CompilerError::new(RefusalKind::FnBody, format!(
                                "borrowed join parameter x_{var} has unverified isShared ownership semantics"
                            )));
                        }
                        if value_env.insert(var, ty).is_some() {
                            return Err(CompilerError::new(
                                RefusalKind::FnBody,
                                format!("join parameter x_{var} reused a visible variable"),
                            ));
                        }
                        if is_value_type(ty) {
                            RuntimeFeatures::mark(ctx.features, RuntimeFeatures::VALUE);
                        }
                        param_code.push(format!("x_{var}: {}", rust_type(ty)));
                        param_types.push(ty);
                    }
                    writeln!(
                        code,
                        "    let j_{id} = |{}| -> {} {{",
                        param_code.join(", "),
                        rust_type(ret_ty)
                    )
                    .unwrap();
                    Self::body(value, code, depth + 1, count, &mut value_env, ret_ty, ctx)?;
                    writeln!(code, "    }};").unwrap();
                    let mut scoped_joins = ctx.joins.clone();
                    scoped_joins.insert(id, param_types);
                    Self::body(
                        next,
                        code,
                        depth + 1,
                        count,
                        env,
                        ret_ty,
                        LoweringContext {
                            functions: ctx.functions,
                            joins: &scoped_joins,
                            features: ctx.features,
                        },
                    )?;
                    return Ok(());
                }
                FnBodyView::Set {
                    target,
                    index,
                    value,
                    next,
                } => {
                    // Source FnBody.set on pointer fields; preserve aliases.
                    let id = Self::var(target)?;
                    let ty = env.get(&id).ok_or(CompilerError::new(
                        RefusalKind::FnBody,
                        "set on undefined variable",
                    ))?;
                    if !matches!(*ty, "obj" | "tobj") {
                        return Err(CompilerError::new(
                            RefusalKind::FnBody,
                            "constructor set requires heap object",
                        ));
                    }
                    let index = Self::nat(index)?;
                    if index >= 1024 {
                        return Err(CompilerError::new(
                            RefusalKind::FnBody,
                            "constructor pointer index exceeds bound",
                        ));
                    }
                    let value = Self::arg(value, env, "tobj")?;
                    writeln!(
                        code,
                        "    let x_{id} = x_{id}.with_field({index}, {value});"
                    )
                    .unwrap();
                    env.insert(id, "obj");
                    RuntimeFeatures::mark(ctx.features, RuntimeFeatures::CONSTRUCTOR_SET_TESTS);
                    x = next;
                }
                FnBodyView::ScalarSet {
                    target,
                    pointers: source_pointers,
                    offset: source_offset,
                    value: source_value,
                    ty: source_ty,
                    next,
                } => {
                    // Source sset is legal only for a unique constructor.
                    // The emitted runtime consumes the Rc and rejects aliases.
                    let id = Self::var(target)?;
                    let pointers = Self::nat(source_pointers)?;
                    let offset = Self::nat(source_offset)?;
                    let value = Self::var(source_value)?;
                    let ty = Self::ty(source_ty)?;
                    if pointers != 4
                        || offset >= 8
                        || ty != "u8"
                        || !env.get(&id).is_some_and(|t| is_value_type(t))
                        || env.get(&value) != Some(&"u8")
                    {
                        return Err(CompilerError::new(
                            RefusalKind::FnBody,
                            format!(
                                "unverified sset layout n={pointers}, offset={offset}, type={ty}"
                            ),
                        ));
                    }
                    writeln!(
                        code,
                        "    let x_{id} = x_{id}.pull_in_set_u8({pointers}, {offset}, x_{value});"
                    )
                    .unwrap();
                    x = next;
                }
                FnBodyView::Inc { target, next }
                | FnBodyView::Dec { target, next }
                | FnBodyView::Delete { target, next } => {
                    // In the bounded value-semantic subset, Rc aliases own
                    // their Rust references. A source-CFG preflight refuses
                    // isShared after a possible earlier inc/dec/del effect.
                    // This is not Lean/Rust reference-count equivalence.
                    let id = Self::var(target)?;
                    let ty = env.get(&id).ok_or(CompilerError::new(
                        RefusalKind::FnBody,
                        "reference bookkeeping for undefined variable",
                    ))?;
                    if !is_value_type(ty) {
                        return Err(CompilerError::new(
                            RefusalKind::FnBody,
                            "reference bookkeeping on non-object variable",
                        ));
                    }
                    x = next;
                }
                FnBodyView::Case { .. } => {
                    // case(tid, scrutinee, type, alts)
                    Self::case_body(x, code, depth, count, env, ret_ty, ctx)?;
                    return Ok(());
                }
                FnBodyView::Jump {
                    id: jump_id,
                    arguments,
                } => {
                    // jmp(joinId, arguments): a typed non-recursive jump
                    // into the enclosing join point's continuation.
                    let id = Self::var(jump_id)?;
                    let types = ctx.joins.get(&id).ok_or_else(|| {
                        CompilerError::new(
                            RefusalKind::FnBody,
                            format!("unsupported or recursive jump to join point {id}"),
                        )
                    })?;
                    let args = Self::array(arguments)?;
                    if args.len() != types.len() {
                        return Err(CompilerError::new(
                            RefusalKind::FnBody,
                            format!(
                                "join point {id} expects {} args, got {}",
                                types.len(),
                                args.len()
                            ),
                        ));
                    }
                    let mut lowered = Vec::new();
                    for (arg, ty) in args.into_iter().zip(types.iter()) {
                        if Self::checked_tag(arg, "Arg")? == 1 {
                            if !is_value_type(ty) {
                                return Err(CompilerError::new(
                                    RefusalKind::FnBody,
                                    "erased scalar join argument not supported",
                                ));
                            }
                            // Source-optimized guard-dependent parameters are
                            // physically absent. Any later read must fail,
                            // never silently materialize an arbitrary value.
                            lowered.push("__LeanValue::erased()".into());
                        } else if *ty == "obj" && Self::checked_tag(arg, "Arg")? == 0 {
                            // Only a typed join argument may refine tobj
                            // (tagged-or-heap) to a heap-only constructor.
                            // All other IR uses keep the strict object type
                            // contract; the runtime checks the actual value.
                            let var = Self::var(Self::field(arg, 0)?)?;
                            if env.get(&var) == Some(&"tobj") {
                                lowered
                                    .push(format!("x_{var}.clone().require_constructor_object()"));
                                RuntimeFeatures::mark(
                                    ctx.features,
                                    RuntimeFeatures::HEAP_JOIN_TESTS,
                                );
                            } else {
                                lowered.push(Self::arg(arg, env, ty)?);
                            }
                        } else {
                            lowered.push(Self::arg(arg, env, ty)?);
                        }
                    }
                    writeln!(code, "    j_{id}({})", lowered.join(", ")).unwrap();
                    return Ok(());
                }
                FnBodyView::Return { value } => {
                    // ret(Arg)
                    writeln!(code, "    {}", Self::arg(value, env, ret_ty)?).unwrap();
                    return Ok(());
                }
            }
        }
    }
}
