//! Expression lowering and conservative ownership/last-use analysis.
use super::*;

impl Reader {
    // Last-use analysis only permits moves through a straight-line tail.
    // Any join, branch, unknown expression, or reference bookkeeping for the
    // candidate is conservatively considered an additional use. This avoids
    // unnecessary transient Rc aliases, but does not prove Lean's physical
    // reference-count trace equals Rust's trace.
    pub(super) unsafe fn arg_refs(x: Obj, id: usize) -> Result<bool, String> {
        Ok(match Self::checked_tag(x, "Arg")? {
            0 => Self::var(Self::field(x, 0)?)? == id,
            1 => false,
            _ => true,
        })
    }

    pub(super) unsafe fn args_ref(args: Obj, id: usize) -> Result<bool, String> {
        for arg in Self::array(args)? {
            if Self::arg_refs(arg, id)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) unsafe fn expr_refs(x: Obj, id: usize) -> Result<bool, String> {
        Ok(match Self::checked_tag(x, "Expr")? {
            0 => Self::args_ref(Self::field(x, 1)?, id)?,
            3 | 9 => Self::var(Self::field(x, 1)?)? == id,
            6 | 7 => Self::args_ref(Self::field(x, 1)?, id)?,
            8 => Self::var(Self::field(x, 0)?)? == id || Self::args_ref(Self::field(x, 1)?, id)?,
            10 => Self::var(Self::field(x, 0)?)? == id,
            11 => false,
            _ => true,
        })
    }

    pub(super) unsafe fn straight_tail_unused(mut x: Obj, id: usize) -> Result<bool, String> {
        for _ in 0..100_000 {
            match Self::checked_tag(x, "FnBody")? {
                0 => {
                    if Self::expr_refs(Self::field(x, 2)?, id)? {
                        return Ok(false);
                    }
                    x = Self::field(x, 3)?;
                }
                6 | 7 => {
                    if Self::var(Self::field(x, 0)?)? == id {
                        return Ok(false);
                    }
                    x = Self::field(x, 2)?;
                }
                8 => {
                    if Self::var(Self::field(x, 0)?)? == id {
                        return Ok(false);
                    }
                    x = Self::field(x, 1)?;
                }
                10 => return Ok(!Self::arg_refs(Self::field(x, 0)?, id)?),
                _ => return Ok(false),
            }
        }
        Ok(false)
    }

    pub(super) unsafe fn tail_unused_on_all_paths(body: Obj, id: usize) -> Result<bool, String> {
        let mut pending = vec![(body, 0usize)];
        let mut steps = 0usize;
        while let Some((current, depth)) = pending.pop() {
            steps += 1;
            if steps > 100_000 || depth > 128 {
                return Ok(false);
            }
            let next_depth = depth + 1;
            match Self::checked_tag(current, "FnBody")? {
                0 => {
                    // vdecl: both the expression and all subsequent uses matter.
                    // Reject shadowing rather than reasoning across renamings.
                    if Self::var(Self::field(current, 0)?)? == id
                        || Self::expr_refs(Self::field(current, 2)?, id)?
                    {
                        return Ok(false);
                    }
                    pending.push((Self::field(current, 3)?, depth));
                }
                1 => {
                    // jdecl: the generated Rust lexical closure may capture
                    // variables from its environment. Scan its whole body,
                    // all parameters and the continuation, not just the jump.
                    for param in Self::array(Self::field(current, 1)?)? {
                        if Self::var(Self::field(param, 0)?)? == id {
                            return Ok(false);
                        }
                    }
                    pending.push((Self::field(current, 2)?, next_depth));
                    pending.push((Self::field(current, 3)?, depth));
                }
                2 => {
                    // Constructor pointer-field set mutates/observes its target.
                    if Self::var(Self::field(current, 0)?)? == id
                        || Self::arg_refs(Self::field(current, 2)?, id)?
                    {
                        return Ok(false);
                    }
                    pending.push((Self::field(current, 3)?, depth));
                }
                5 => {
                    // Packed-field sset reads its object and byte-value IDs.
                    if Self::var(Self::field(current, 0)?)? == id
                        || Self::var(Self::field(current, 3)?)? == id
                    {
                        return Ok(false);
                    }
                    pending.push((Self::field(current, 5)?, depth));
                }
                6 | 7 => {
                    // inc/dec: conservatively retain variables involved in
                    // source reference-count operations, even if IR is erased.
                    if Self::var(Self::field(current, 0)?)? == id {
                        return Ok(false);
                    }
                    pending.push((Self::field(current, 2)?, depth));
                }
                8 => {
                    // del: likewise, don't transfer when source bookkeeping
                    // mentions this value after the candidate consuming call.
                    if Self::var(Self::field(current, 0)?)? == id {
                        return Ok(false);
                    }
                    pending.push((Self::field(current, 1)?, depth));
                }
                9 => {
                    // case: scan scrutinee plus every constructor/default arm.
                    if Self::var(Self::field(current, 1)?)? == id {
                        return Ok(false);
                    }
                    for alt in Self::array(Self::field(current, 3)?)? {
                        let body_index = match Self::checked_tag(alt, "Alt")? {
                            0 => 1, // constructor alternative
                            1 => 0, // default alternative
                            _ => return Ok(false),
                        };
                        pending.push((Self::field(alt, body_index)?, next_depth));
                    }
                }
                10 => {
                    if Self::arg_refs(Self::field(current, 0)?, id)? {
                        return Ok(false);
                    }
                }
                11 => {
                    // A typed jump can pass the value to a join even though
                    // that join's body doesn't mention the original VarId.
                    if Self::args_ref(Self::field(current, 1)?, id)? {
                        return Ok(false);
                    }
                }
                // setTag, uset and other unsupported forms are never
                // a reason to silently consume an array.
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    pub(super) unsafe fn consumable_array(expr: Obj, tail: Obj) -> Result<Option<usize>, String> {
        if Self::checked_tag(expr, "Expr")? != 6 {
            return Ok(None);
        }
        let name = Self::name(Self::field(expr, 0)?, 0)?;
        let arity = match name.as_str() {
            "Array.push" => 3,
            "Array.set!" => 4,
            _ => return Ok(None),
        };
        let args = Self::array(Self::field(expr, 1)?)?;
        if args.len() != arity || Self::checked_tag(args[1], "Arg")? != 0 {
            return Ok(None);
        }
        let id = Self::var(Self::field(args[1], 0)?)?;
        for arg in args.iter().skip(2) {
            if Self::arg_refs(*arg, id)? {
                return Ok(None);
            }
        }
        Ok(Self::tail_unused_on_all_paths(tail, id)?.then_some(id))
    }

    // A direct callee takes ownership of its argument. Moving an object at
    // its unique final use avoids manufacturing a temporary Rust Rc alias.
    // Do not extend this analysis through joins, branches, indirect calls,
    // bookkeeping, or unrecognized expressions.
    pub(super) unsafe fn consumable_call(
        expr: Obj,
        tail: Obj,
        functions: Option<&FunctionTable>,
    ) -> Result<BTreeSet<usize>, String> {
        let mut consumed = BTreeSet::new();
        if Self::checked_tag(expr, "Expr")? != 6 {
            return Ok(consumed);
        }
        let name = Self::name(Self::field(expr, 0)?, 0)?;
        let Some(signature) = functions.and_then(|f| f.get(&name)) else {
            return Ok(consumed);
        };
        let args = Self::array(Self::field(expr, 1)?)?;
        if args.len() != signature.params.len() {
            return Ok(consumed);
        }
        let mut counts = BTreeMap::<usize, usize>::new();
        for arg in &args {
            if Self::checked_tag(*arg, "Arg")? == 0 {
                let id = Self::var(Self::field(*arg, 0)?)?;
                *counts.entry(id).or_default() += 1;
            }
        }
        for (arg, ty) in args.into_iter().zip(signature.params.iter()) {
            if !is_value_type(ty) || Self::checked_tag(arg, "Arg")? != 0 {
                continue;
            }
            let id = Self::var(Self::field(arg, 0)?)?;
            if counts.get(&id) == Some(&1) && Self::straight_tail_unused(tail, id)? {
                consumed.insert(id);
            }
        }
        Ok(consumed)
    }

    pub(super) unsafe fn expr(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
        functions: Option<&FunctionTable>,
        consumed_array: Option<usize>,
        consumed_calls: &BTreeSet<usize>,
    ) -> Result<String, String> {
        match Self::checked_tag(x, "Expr")? {
            0 => {
                // Source-pinned zero-field scalar inductives do not allocate a heap.
                // Object constructors retain the independently verified Rc model.
                if matches!(var_ty, "u8" | "usize") {
                    // ctor(info, fields). Only nullary scalar constructors are
                    // representable without a Lean heap. No field-packing shortcut.
                    if !matches!(var_ty, "u8" | "usize") {
                        return Err("heap-backed or non-scalar constructor is unsupported".into());
                    }
                    let info = Self::field(x, 0)?;
                    let fields = Self::array(Self::field(x, 1)?)?;
                    if !fields.is_empty() {
                        return Err("constructor with fields requires an object runtime".into());
                    }
                    for field in 2..=4 {
                        if Self::nat(Self::field(info, field)?)? != 0 {
                            return Err(
                                "constructor with pointer/scalar layout is unsupported".into()
                            );
                        }
                    }
                    let _name = Self::name(Self::field(info, 0)?, 0)?;
                    let index = Self::nat(Self::field(info, 1)?)?;
                    if index > 255 {
                        return Err("constructor tag exceeds nullary enum bound".into());
                    }
                    return Ok(format!("{index}{var_ty}"));
                }
                // ctor: only immutable, pointer-field constructors with
                // verified metadata. Scalar-field layouts are not yet mapped.
                if !is_value_type(var_ty) {
                    return Err("ctor result is not an object-valued IR type".into());
                }
                let info = Self::field(x, 0)?;
                let name = Self::name(Self::field(info, 0)?, 0)?;
                let tag = Self::nat(Self::field(info, 1)?)?;
                let fields = Self::array(Self::field(x, 1)?)?;
                let size = Self::nat(Self::field(info, 2)?)?;
                let usize_count = Self::nat(Self::field(info, 3)?)?;
                let ssize = Self::nat(Self::field(info, 4)?)?;
                if name == "SyncModel.PullIn.mk" {
                    if var_ty != "obj"
                        || tag != 0
                        || size != 4
                        || usize_count != 0
                        || ssize != 8
                        || fields.len() != 4
                    {
                        return Err(
                            "PullIn.mk requires exact source 4-pointer/8-byte layout".into()
                        );
                    }
                    let mut args = Vec::new();
                    for arg in fields {
                        args.push(Self::arg(arg, env, "tobj")?);
                    }
                    return Ok(format!(
                        "__LeanValue::pull_in_ctor(vec![{}])",
                        args.join(", ")
                    ));
                }
                // The source CtorInfo is authoritative: only zero-field
                // tagged variants and heap objects with pointer-only fields
                // are representable. Never pack a scalar field implicitly.
                if !name.contains('.')
                    || name.is_empty()
                    || tag >= 256
                    || size > 1024
                    || size != fields.len()
                    || usize_count != 0
                    || ssize != 0
                {
                    return Err(format!(
                        "constructor {name} has unsupported scalar, tag or field layout"
                    ));
                }
                if size == 0 {
                    if var_ty != "tagged" {
                        return Err(format!("zero-field constructor {name} is not tagged"));
                    }
                    return Ok(format!("__LeanValue::tagged({tag})"));
                }
                if var_ty != "obj" {
                    return Err("heap constructor has unexpected IR result type".into());
                }
                let mut args = Vec::new();
                for arg in fields {
                    args.push(Self::arg(arg, env, "tobj")?);
                }
                if name == "List.cons" {
                    return Ok(format!("__LeanValue::list_cons({}, {})", args[0], args[1]));
                }
                Ok(format!(
                    "__LeanValue::ctor({tag}, \"{name}\", vec![{}])",
                    args.join(", ")
                ))
            }
            3 => {
                // proj(index, object)
                if !is_value_type(var_ty) {
                    return Err("object projection result has non-object type".into());
                }
                let index = Self::nat(Self::field(x, 0)?)?;
                let id = Self::var(Self::field(x, 1)?)?;
                let found = env.get(&id).ok_or("projection of undefined variable")?;
                if !is_value_type(found) {
                    return Err("projection from scalar variable".into());
                }
                Ok(format!("x_{id}.field({index})"))
            }

            5 => {
                // Lean sproj(n,offset,x): only pinned original PullIn.mk's
                // four object pointers and eight source Bool bytes.
                if var_ty != "u8" {
                    return Err("PullIn sproj requires UInt8 result".into());
                }
                let pointers = Self::nat(Self::field(x, 0)?)?;
                let offset = Self::nat(Self::field(x, 1)?)?;
                let id = Self::var(Self::field(x, 2)?)?;
                if pointers != 4 || offset >= 8 || !env.get(&id).is_some_and(|ty| is_value_type(ty))
                {
                    return Err(format!(
                        "unverified sproj layout n={pointers}, offset={offset}, operand=x_{id}"
                    ));
                }
                Ok(format!("x_{id}.pull_in_sproj_u8({pointers}, {offset})"))
            }
            7 => {
                // PAP(callee, captured operands). For this first subset, each
                // source callee must be compiled and its ABI must consist
                // solely of boxed values, both parameters and return.
                if !is_value_type(var_ty) {
                    return Err("PAP result must be an object".into());
                }
                let name = Self::name(Self::field(x, 0)?, 0)?;
                let signature = functions
                    .and_then(|table| table.get(&name))
                    .ok_or_else(|| format!("PAP {name} lacks reachable executable IR"))?;
                let args = Self::array(Self::field(x, 1)?)?;
                if signature.params.is_empty()
                    || args.len() >= signature.params.len()
                    || !signature.params.iter().all(|ty| is_value_type(ty))
                    || !is_value_type(signature.result)
                {
                    return Err(format!("PAP {name} has unsupported typed/arity layout"));
                }
                let mut captured = Vec::new();
                for arg in args {
                    // A generated helper may accept tagged while its source
                    // PAP operand is tobj (boxed Bool). Both map to the same
                    // immutable value model; scalar operands still refuse.
                    captured.push(Self::arg(arg, env, "tobj")?);
                }
                Ok(format!(
                    "__LeanValue::pap({}, {}, vec![{}])",
                    internal_closure_name(&name),
                    signature.params.len(),
                    captured.join(", ")
                ))
            }
            8 => {
                // AP(f, arguments): supported as 1..16 boxed-value operands.
                // A dynamic closure may be partially applied again.
                if !is_value_type(var_ty) {
                    return Err("AP scalar result requires an unsupported ABI adapter".into());
                }
                let fun = Self::var(Self::field(x, 0)?)?;
                let found = env
                    .get(&fun)
                    .ok_or_else(|| format!("undefined AP function x_{fun}"))?;
                if !is_value_type(found) {
                    return Err("AP function must have an object representation".into());
                }
                let args = Self::array(Self::field(x, 1)?)?;
                if args.is_empty() || args.len() > 16 {
                    return Err("AP requires 1..16 object arguments".into());
                }
                let mut lowered = Vec::new();
                for arg in args {
                    lowered.push(Self::arg(arg, env, "tobj")?);
                }
                Ok(format!("x_{fun}.apply(vec![{}])", lowered.join(", ")))
            }
            9 => {
                // box(scalar type, variable)
                if !is_value_type(var_ty) {
                    return Err("boxed scalar result must be object-valued".into());
                }
                let ty = Self::ty(Self::field(x, 0)?)?;
                if is_value_type(ty) {
                    return Err("box expects a scalar IR type".into());
                }
                if ty == "f64" {
                    return Err("Float boxing requires an unsupported runtime adapter".into());
                }
                let id = Self::var(Self::field(x, 1)?)?;
                if env.get(&id) != Some(&ty) {
                    return Err("box scalar input type mismatch".into());
                }
                Ok(format!("__LeanValue::boxed_{ty}(x_{id})"))
            }
            10 => {
                // unbox(object variable) to a statically known scalar.
                if is_value_type(var_ty) {
                    return Err("unbox result type must be scalar".into());
                }
                let id = Self::var(Self::field(x, 0)?)?;
                let found = env.get(&id).ok_or("unbox of undefined variable")?;
                if !is_value_type(found) {
                    return Err("unbox from non-object variable".into());
                }
                Ok(format!("x_{id}.unbox_{var_ty}()"))
            }
            6 => {
                // fap, preserving the exact known primitive semantics.
                let name = Self::name(Self::field(x, 0)?, 0)?;
                let args = Self::array(Self::field(x, 1)?)?;
                if let Some(signature) = functions.and_then(|table| table.get(&name)) {
                    if args.len() != signature.params.len() {
                        return Err(format!(
                            "{name}: expected {} arguments, got {}",
                            signature.params.len(),
                            args.len()
                        ));
                    }
                    if var_ty != signature.result {
                        return Err(format!(
                            "{name}: expected result type {}, got {var_ty}",
                            signature.result
                        ));
                    }
                    let mut lowered = Vec::with_capacity(args.len());
                    for (arg, ty) in args.into_iter().zip(signature.params.iter()) {
                        let typed = Self::arg(arg, env, ty)?;
                        if is_value_type(ty) && Self::checked_tag(arg, "Arg")? == 0 {
                            let id = Self::var(Self::field(arg, 0)?)?;
                            if consumed_calls.contains(&id) {
                                lowered.push(format!("x_{id}"));
                                continue;
                            }
                        }
                        lowered.push(typed);
                    }
                    return Ok(format!("{}({})", internal_name(&name), lowered.join(", ")));
                }
                // These exact compiler externs are added to the canonical
                // object runtime. Existing Array.push and boxed Array.size
                // stay in the source-reviewed primitive adapter registry.
                if matches!(
                    name.as_str(),
                    "Array.mkEmpty"
                        | "Array.getInternal"
                        | "Array.getInternalBorrowed"
                        | "Array.set!"
                ) {
                    let expected = match name.as_str() {
                        "Array.mkEmpty" => 2,
                        _ => 4,
                    };
                    if args.len() != expected {
                        return Err(format!(
                            "{name}: expected {expected} operands, got {}",
                            args.len()
                        ));
                    }
                    let erased = |index: usize| -> Result<(), String> {
                        if Self::checked_tag(args[index], "Arg")? == 1 {
                            Ok(())
                        } else {
                            Err(format!(
                                "{name}: expected erased source type/proof at {index}"
                            ))
                        }
                    };
                    erased(0)?;
                    return match name.as_str() {
                        "Array.mkEmpty" => {
                            if var_ty != "obj" {
                                return Err("Array.mkEmpty requires object result".into());
                            }
                            let capacity = Self::arg(args[1], env, "tagged")?;
                            Ok(format!("__LeanValue::empty_array({capacity}.tagged_nat())"))
                        }
                        "Array.getInternal" | "Array.getInternalBorrowed" => {
                            if var_ty != "tobj" {
                                return Err(format!("{name} requires object element result"));
                            }
                            erased(3)?;
                            let array = Self::arg(args[1], env, "obj")?;
                            let index = Self::arg(args[2], env, "tagged")?;
                            Ok(format!("{array}.array_get_tagged({index}.tagged_nat())"))
                        }
                        "Array.set!" => {
                            if var_ty != "obj" {
                                return Err("Array.set! requires object result".into());
                            }
                            let array = Self::arg(args[1], env, "obj")?;
                            let index = Self::arg(args[2], env, "tagged")?;
                            let value = Self::arg(args[3], env, "tobj")?;
                            if let Some(id) = consumed_array {
                                Ok(format!(
                                    "x_{id}.array_set_tagged_owned({index}.tagged_nat(), {value})"
                                ))
                            } else {
                                Ok(format!(
                                    "{array}.array_set_tagged({index}.tagged_nat(), {value})"
                                ))
                            }
                        }
                        _ => unreachable!(),
                    };
                }
                if let Some(runtime) = runtime_primitive_spec(&name) {
                    if !is_value_type(var_ty) {
                        return Err(format!("{name}: object result required for native runtime"));
                    }
                    let expected = match runtime.shape {
                        "unary" => 1,
                        "binary" => 2,
                        "erased_unary" => 2,
                        "erased_binary" => 3,
                        _ => return Err(format!("{name}: unrecognized runtime call shape")),
                    };
                    if args.len() != expected {
                        return Err(format!(
                            "{name}: expected {expected} operands, got {}",
                            args.len()
                        ));
                    }
                    let begin = if runtime.shape.starts_with("erased_") {
                        if Self::checked_tag(args[0], "Arg")? != 1 {
                            return Err(format!("{name}: missing erased source type proof"));
                        }
                        1
                    } else {
                        0
                    };
                    let mut operands = Vec::new();
                    for arg in &args[begin..] {
                        operands.push(Self::arg(*arg, env, "tobj")?);
                    }
                    if name == "Array.push" {
                        if let Some(id) = consumed_array {
                            if operands.len() != 2 {
                                return Err("Array.push ownership operands malformed".into());
                            }
                            return Ok(format!("x_{id}.array_push_owned({})", operands[1]));
                        }
                    }
                    return match operands.as_slice() {
                        [value] => Ok(format!("{value}.{}()", runtime.rust_function)),
                        [lhs, rhs] => Ok(format!("{lhs}.{}(&{rhs})", runtime.rust_function)),
                        _ => Err(format!("{name}: inconsistent runtime operand count")),
                    };
                }
                if args.len() != 2 {
                    return Err(format!("{name}: expected binary operands"));
                }
                // Statically tagged immediate Nat comparisons do not require
                // GMP. Boxed arbitrary Nat continues through the GMP path.
                let mut both_tagged =
                    matches!(name.as_str(), "Nat.decEq" | "Nat.decLt" | "Nat.decLe");
                if both_tagged {
                    for arg in &args {
                        if Self::checked_tag(*arg, "Arg")? != 0 {
                            both_tagged = false;
                            break;
                        }
                        let id = Self::var(Self::field(*arg, 0)?)?;
                        if env.get(&id) != Some(&"tagged") {
                            both_tagged = false;
                            break;
                        }
                    }
                }
                if both_tagged {
                    if var_ty != "u8" {
                        return Err(format!("{name}: tagged Nat comparison must return UInt8"));
                    }
                    let lhs = Self::arg(args[0], env, "tagged")?;
                    let rhs = Self::arg(args[1], env, "tagged")?;
                    let op = match name.as_str() {
                        "Nat.decEq" => "==",
                        "Nat.decLt" => "<",
                        _ => "<=",
                    };
                    return Ok(format!(
                        "u8::from({lhs}.tagged_nat() {op} {rhs}.tagged_nat())"
                    ));
                }
                if is_nat_primitive(&name) {
                    let lhs = Self::arg(args[0], env, "tobj")?;
                    let rhs = Self::arg(args[1], env, "tobj")?;
                    return match name.as_str() {
                        "Nat.add" | "Nat.sub" | "Nat.mul" | "Nat.div" | "Nat.mod" => {
                            if !is_value_type(var_ty) {
                                return Err(format!("{name}: result must be object-valued"));
                            }
                            let op = name.strip_prefix("Nat.").unwrap();
                            Ok(format!("{lhs}.nat_binary(&{rhs}, \"{op}\")"))
                        }
                        "Nat.decEq" | "Nat.decLt" | "Nat.decLe" => {
                            if var_ty != "u8" {
                                return Err(format!("{name}: result must be u8"));
                            }
                            let operator = match name.as_str() {
                                "Nat.decEq" => "== 0",
                                "Nat.decLt" => "< 0",
                                _ => "<= 0",
                            };
                            Ok(format!("u8::from({lhs}.nat_cmp(&{rhs}) {operator})"))
                        }
                        _ => unreachable!(),
                    };
                }
                let spec = primitive_spec(&name)
                    .ok_or_else(|| format!("unrecognized primitive call: {name}"))?;
                let op = spec.rust_op;
                let comparison = spec.comparison;
                let expected_ty = spec.operand_type;
                let lhs = Self::arg(args[0], env, expected_ty)?;
                let rhs = Self::arg(args[1], env, expected_ty)?;
                if comparison {
                    if var_ty != "u8" {
                        return Err(format!("{name}: comparison must produce u8, got {var_ty}"));
                    }
                    Ok(format!("u8::from({lhs} {op} {rhs})"))
                } else {
                    if var_ty != expected_ty {
                        return Err(format!(
                            "{name}: result type mismatch: expected {expected_ty}, got {var_ty}"
                        ));
                    }
                    match (expected_ty, op) {
                        ("f64", "+" | "-" | "*") => Ok(format!("{lhs} {op} {rhs}")),
                        (_, "wrapping_add" | "wrapping_sub" | "wrapping_mul") => {
                            Ok(format!("{lhs}.{op}({rhs})"))
                        }
                        // Lean's unsigned division and remainder are total.
                        // Rust's raw / and % panic on zero: never substitute them.
                        (_, "checked_div") => Ok(format!("{lhs}.checked_div({rhs}).unwrap_or(0)")),
                        (_, "checked_rem") => {
                            Ok(format!("{lhs}.checked_rem({rhs}).unwrap_or({lhs})"))
                        }
                        (_, "&" | "|" | "^") => Ok(format!("{lhs} {op} {rhs}")),
                        (_, "wrapping_shl" | "wrapping_shr") => {
                            // Lean shifts modulo the bit width, including counts
                            // beyond 64 and on the platform-sized USize type.
                            Ok(format!(
                                "{lhs}.{op}(({rhs} % ({expected_ty}::BITS as {expected_ty})) as u32)"
                            ))
                        }
                        _ => Err(format!("{name}: unreviewed primitive operation {op}")),
                    }
                }
            }
            11 => Ok(Self::lit(Self::field(x, 0)?, var_ty)?),
            12 => {
                if var_ty != "u8" {
                    return Err("isShared must yield uint8".into());
                }
                let id = Self::var(Self::field(x, 0)?)?;
                if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
                    return Err("isShared requires a value object".into());
                }
                Ok(format!("x_{id}.is_shared()"))
            }
            t => Err(format!("IR expression constructor {t} unsupported")),
        }
    }

    // Only Boolean pattern matches are supported. Lean represents Bool as
    // UInt8 at this compiler stage. Never interpret a different inductive
    // datatype's constructor index as a Boolean branch.
}
