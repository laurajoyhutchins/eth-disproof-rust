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
    ) -> Result<(), String> {
        if depth > 128 {
            return Err("IR control-flow nesting limit".into());
        }
        loop {
            *count += 1;
            if *count > 100_000 {
                return Err("IR instruction limit exceeded".into());
            }
            match Self::checked_tag(x, "FnBody")? {
                0 => {
                    // vdecl(x, ty, expr, body)
                    let name = Self::var(Self::field(x, 0)?)?;
                    let ty = Self::ty(Self::field(x, 1)?)?;
                    if ty == "erased" {
                        return Err("erased local declaration has no runtime expression".into());
                    }
                    let expr = Self::field(x, 2)?;
                    // Only top-level array candidates can transfer ownership.
                    // Their full tails are scanned for references through
                    // branch and join bodies, conservatively preserving aliases.
                    let straight_line = depth == 0 && ctx.joins.is_empty();
                    let tail = Self::field(x, 3)?;
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
                        ctx.functions,
                        consumed_array,
                        &consumed_calls,
                        consumed_ap,
                    )?;
                    if env.insert(name, ty).is_some() {
                        return Err(format!("variable x_{name} defined more than once"));
                    }
                    writeln!(code, "    let x_{name}: {} = {value};", rust_type(ty)).unwrap();
                    x = Self::field(x, 3)?;
                }
                1 => {
                    // jdecl(joinId, params, value, continuation): the join's
                    // body is a typed, lexically captured Rust closure. Its
                    // declaration is deliberately absent from its own value
                    // scope: recursive join jumps are refused, not miscompiled.
                    let id = Self::var(Self::field(x, 0)?)?;
                    if ctx.joins.contains_key(&id) {
                        return Err(format!("join point {id} shadows a visible join"));
                    }
                    let mut param_types = Vec::new();
                    let mut value_env = env.clone();
                    let mut param_code = Vec::new();
                    for param in Self::array(Self::field(x, 1)?)? {
                        let var = Self::var(Self::field(param, 0)?)?;
                        let ty = Self::ty(Self::field(param, 1)?)?;
                        if ty == "erased" {
                            return Err("erased join parameter not yet source-verified".into());
                        }
                        if value_env.insert(var, ty).is_some() {
                            return Err(format!(
                                "join parameter x_{var} reused a visible variable"
                            ));
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
                    Self::body(
                        Self::field(x, 2)?,
                        code,
                        depth + 1,
                        count,
                        &mut value_env,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "    }};").unwrap();
                    let mut scoped_joins = ctx.joins.clone();
                    scoped_joins.insert(id, param_types);
                    Self::body(
                        Self::field(x, 3)?,
                        code,
                        depth + 1,
                        count,
                        env,
                        ret_ty,
                        LoweringContext {
                            functions: ctx.functions,
                            joins: &scoped_joins,
                        },
                    )?;
                    return Ok(());
                }
                2 => {
                    // Source FnBody.set on pointer fields; preserve aliases.
                    let id = Self::var(Self::field(x, 0)?)?;
                    let ty = env.get(&id).ok_or("set on undefined variable")?;
                    if !matches!(*ty, "obj" | "tobj") {
                        return Err("constructor set requires heap object".into());
                    }
                    let index = Self::nat(Self::field(x, 1)?)?;
                    if index >= 1024 {
                        return Err("constructor pointer index exceeds bound".into());
                    }
                    let value = Self::arg(Self::field(x, 2)?, env, "tobj")?;
                    writeln!(
                        code,
                        "    let x_{id} = x_{id}.with_field({index}, {value});"
                    )
                    .unwrap();
                    env.insert(id, "obj");
                    x = Self::field(x, 3)?;
                }
                5 => {
                    // Source sset is legal only for a unique constructor.
                    // The emitted runtime consumes the Rc and rejects aliases.
                    let id = Self::var(Self::field(x, 0)?)?;
                    let pointers = Self::nat(Self::field(x, 1)?)?;
                    let offset = Self::nat(Self::field(x, 2)?)?;
                    let value = Self::var(Self::field(x, 3)?)?;
                    let ty = Self::ty(Self::field(x, 4)?)?;
                    if pointers != 4
                        || offset >= 8
                        || ty != "u8"
                        || !env.get(&id).is_some_and(|t| is_value_type(t))
                        || env.get(&value) != Some(&"u8")
                    {
                        return Err(format!(
                            "unverified sset layout n={pointers}, offset={offset}, type={ty}"
                        ));
                    }
                    writeln!(
                        code,
                        "    let x_{id} = x_{id}.pull_in_set_u8({pointers}, {offset}, x_{value});"
                    )
                    .unwrap();
                    x = Self::field(x, 5)?;
                }
                6..=8 => {
                    // Immutable Rc-backed emitted values own their references;
                    // Lean's inc/dec/del bookkeeping is non-observable in this
                    // subset because reset/reuse/isShared are refused.
                    let id = Self::var(Self::field(x, 0)?)?;
                    let ty = env
                        .get(&id)
                        .ok_or("reference bookkeeping for undefined variable")?;
                    if !is_value_type(ty) {
                        return Err("reference bookkeeping on non-object variable".into());
                    }
                    let body_index = if Self::tag(x)? == 8 { 1 } else { 2 };
                    x = Self::field(x, body_index)?;
                }
                9 => {
                    // case(tid, scrutinee, type, alts)
                    Self::case_body(x, code, depth, count, env, ret_ty, ctx)?;
                    return Ok(());
                }
                11 => {
                    // jmp(joinId, arguments): a typed non-recursive jump
                    // into the enclosing join point's continuation.
                    let id = Self::var(Self::field(x, 0)?)?;
                    let types = ctx.joins.get(&id).ok_or_else(|| {
                        format!("unsupported or recursive jump to join point {id}")
                    })?;
                    let args = Self::array(Self::field(x, 1)?)?;
                    if args.len() != types.len() {
                        return Err(format!(
                            "join point {id} expects {} args, got {}",
                            types.len(),
                            args.len()
                        ));
                    }
                    let mut lowered = Vec::new();
                    for (arg, ty) in args.into_iter().zip(types.iter()) {
                        if Self::checked_tag(arg, "Arg")? == 1 {
                            if !is_value_type(ty) {
                                return Err("erased scalar join argument not supported".into());
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
                10 => {
                    // ret(Arg)
                    writeln!(code, "    {}", Self::arg(Self::field(x, 0)?, env, ret_ty)?).unwrap();
                    return Ok(());
                }
                t => return Err(format!("IR body constructor {t} unsupported")),
            }
        }
    }
}
