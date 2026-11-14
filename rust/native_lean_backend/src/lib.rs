//! An in-process, strict Lean 4.34.1 IR -> Rust code emitter.
//!
//! This entry point receives `Lean.IR.Decl` *directly* as a borrowed Lean object.
//! It does not serialize or clone the IR. Only an explicitly accepted subset is
//! lowered; unknown instructions and types are errors, never substitutions.
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{c_char, c_void, CStr, CString};
use std::fmt::Write;

#[repr(C)]
pub struct LeanObject {
    _opaque: [u8; 0],
}
type Obj = *const LeanObject;
extern "C" {
    fn lr_is_scalar(x: Obj) -> i32;
    fn lr_scalar_value(x: Obj) -> usize;
    fn lr_is_ctor(x: Obj) -> i32;
    fn lr_tag(x: Obj) -> i32;
    fn lr_field_count(x: Obj) -> usize;
    fn lr_field(x: Obj, n: usize) -> Obj;
    fn lr_is_array(x: Obj) -> i32;
    fn lr_array_len(x: Obj) -> usize;
    fn lr_array_at(x: Obj, n: usize) -> Obj;
    fn lr_string_ptr(x: Obj) -> *const c_char;
    fn lean_mk_string(x: *const c_char) -> *mut c_void;
}

#[derive(Debug, Clone)]
struct Signature {
    params: Vec<&'static str>,
    result: &'static str,
}

type FunctionTable = BTreeMap<String, Signature>;
// Lexically visible, typed IR join points. Each body has its own scope.
type JoinTable = BTreeMap<usize, Vec<&'static str>>;

#[derive(Clone, Copy)]
struct LoweringContext<'a> {
    functions: Option<&'a FunctionTable>,
    joins: &'a JoinTable,
}

struct Reader;
impl Reader {
    unsafe fn scalar(x: Obj) -> Result<usize, String> {
        if lr_is_scalar(x) == 0 {
            Err("expected tagged scalar".into())
        } else {
            Ok(lr_scalar_value(x))
        }
    }
    unsafe fn tag(x: Obj) -> Result<usize, String> {
        if lr_is_scalar(x) != 0 {
            return Ok(lr_scalar_value(x));
        }
        if lr_is_ctor(x) == 0 {
            return Err("expected inductive constructor".into());
        }
        Ok(lr_tag(x) as usize)
    }
    unsafe fn field(x: Obj, index: usize) -> Result<Obj, String> {
        if lr_is_ctor(x) == 0 || index >= lr_field_count(x) {
            return Err(format!(
                "constructor field {index} unavailable (tag={}, fields={}, scalar={})",
                lr_tag(x),
                lr_field_count(x),
                lr_is_scalar(x)
            ));
        }
        Ok(lr_field(x, index))
    }
    unsafe fn array(x: Obj) -> Result<Vec<Obj>, String> {
        if lr_is_array(x) == 0 {
            return Err("expected Lean Array".into());
        }
        let count = lr_array_len(x);
        if count > 1_000_000 {
            return Err("IR node array exceeds safety cap".into());
        }
        Ok((0..count).map(|i| lr_array_at(x, i)).collect())
    }
    unsafe fn string(x: Obj) -> Result<String, String> {
        let ptr = lr_string_ptr(x);
        if ptr.is_null() {
            return Err("expected Lean String".into());
        }
        Ok(CStr::from_ptr(ptr)
            .to_str()
            .map_err(|_| "invalid UTF-8")?
            .to_owned())
    }
    unsafe fn nat(x: Obj) -> Result<usize, String> {
        Self::scalar(x).map_err(|_| "large Nat unsupported by v0 compiler".into())
    }
    // Lean.Name: anonymous=0, str(parent, string)=1, num(parent, nat)=2.
    unsafe fn name(x: Obj, depth: usize) -> Result<String, String> {
        if depth > 128 {
            return Err("name nesting limit".into());
        }
        match Self::tag(x)? {
            0 => Ok(String::new()),
            1 => {
                let p = Self::name(Self::field(x, 0)?, depth + 1)?;
                let s = Self::string(Self::field(x, 1)?)?;
                // Restrict names to unambiguous ASCII segments until the
                // backend uses structured Name identity throughout. Without
                // this, a quoted segment containing '.' could collide with
                // a nested Lean name in the call graph.
                if s.is_empty()
                    || !s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
                    || s.as_bytes()[0].is_ascii_digit()
                {
                    return Err(
                        "unsupported Lean.Name segment; refusing ambiguous dependency identity"
                            .into(),
                    );
                }
                Ok(if p.is_empty() { s } else { format!("{p}.{s}") })
            }
            2 => Err("numeric Lean.Name components require a structured identity adapter".into()),
            t => Err(format!("unknown Lean.Name tag {t}")),
        }
    }
    unsafe fn var(x: Obj) -> Result<usize, String> {
        // A Lean single-field structure may be represented as its single field
        // after erasure; accept both representations, reject all other cases.
        if lr_is_scalar(x) != 0 {
            return Self::nat(x);
        }
        if lr_is_ctor(x) != 0 && lr_field_count(x) == 1 {
            return Self::nat(Self::field(x, 0)?);
        }
        Err("unsupported VarId runtime representation".into())
    }
    unsafe fn arg(
        x: Obj,
        env: &BTreeMap<usize, &'static str>,
        expected: &str,
    ) -> Result<String, String> {
        match Self::tag(x)? {
            0 => {
                let id = Self::var(Self::field(x, 0)?)?;
                let found = env
                    .get(&id)
                    .ok_or_else(|| format!("unknown input variable x_{id}"))?;
                if *found != expected {
                    return Err(format!("x_{id}: expected {expected}, got {found}"));
                }
                Ok(format!("x_{id}"))
            }
            1 => Err("erased value used as runtime operand".into()),
            t => Err(format!("unknown Arg constructor {t}")),
        }
    }
    unsafe fn ty(x: Obj) -> Result<&'static str, String> {
        // The tag ordering comes from the pinned Lean.Compiler.IR.Basic.
        match Self::tag(x)? {
            0 => Ok("f64"),
            1 => Ok("u8"),
            2 => Ok("u16"),
            3 => Ok("u32"),
            4 => Ok("u64"),
            5 => Ok("usize"),
            12 => Ok("usize"), // nullary enum/tagged constructor, never heap object
            t => Err(format!(
                "IR type tag {t} unsupported (supported f64/u8/u16/u32/u64/usize/tagged-nullary)"
            )),
        }
    }
    unsafe fn lit(x: Obj, ty: &str) -> Result<String, String> {
        match Self::tag(x)? {
            0 => {
                let n = Self::nat(Self::field(x, 0)?)?;
                let max = match ty {
                    "u8" => u8::MAX as usize,
                    "u16" => u16::MAX as usize,
                    "u32" => u32::MAX as usize,
                    "u64" => usize::MAX, // Pinned Linux x86-64 Lean ABI.
                    "usize" => usize::MAX,
                    _ => return Err(format!("literal type {ty} unsupported")),
                };
                if n > max {
                    return Err(format!("literal {n} exceeds type {ty}"));
                }
                Ok(format!("{n}{ty}"))
            }
            t => Err(format!("literal constructor {t} unsupported")),
        }
    }
    unsafe fn expr(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
        functions: Option<&FunctionTable>,
    ) -> Result<String, String> {
        match Self::tag(x)? {
            0 => {
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
                        return Err("constructor with pointer/scalar layout is unsupported".into());
                    }
                }
                let _name = Self::name(Self::field(info, 0)?, 0)?;
                let index = Self::nat(Self::field(info, 1)?)?;
                if index > 255 {
                    return Err("constructor tag exceeds nullary enum bound".into());
                }
                Ok(format!("{index}{var_ty}"))
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
                        lowered.push(Self::arg(arg, env, ty)?);
                    }
                    return Ok(format!("{}({})", internal_name(&name), lowered.join(", ")));
                }
                if args.len() != 2 {
                    return Err(format!("{name}: expected binary operands"));
                }
                // Production lowering and closure discovery consult one versioned
                // primitive registry. Unknown calls cannot acquire host semantics.
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
                        (_, "checked_div") => {
                            Ok(format!("{lhs}.checked_div({rhs}).unwrap_or(0)"))
                        }
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
            t => Err(format!("IR expression constructor {t} unsupported")),
        }
    }

    // Only Boolean pattern matches are supported. Lean represents Bool as
    // UInt8 at this compiler stage. Never interpret a different inductive
    // datatype's constructor index as a Boolean branch.
    unsafe fn boolean_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> Result<(), String> {
        // Lean 4.34.1 IR uses the *storage type* name UInt8 here,
        // not the source Bool name. Validate Bool constructor names below.
        if Self::name(Self::field(x, 0)?, 0)? != "UInt8" {
            return Err("case on a non-UInt8 representation is unsupported".into());
        }
        if Self::ty(Self::field(x, 2)?)? != "u8" {
            return Err("Bool case must have UInt8 scrutinee".into());
        }
        let scrutinee = Self::var(Self::field(x, 1)?)?;
        if env.get(&scrutinee) != Some(&"u8") {
            return Err("Bool scrutinee variable is not UInt8".into());
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.len() != 2 {
            return Err("Bool case requires exactly two constructor alternatives".into());
        }
        let mut seen = [false; 2];
        writeln!(code, "    match x_{scrutinee} {{").unwrap();
        for alt in alts {
            if Self::tag(alt)? != 0 {
                return Err("Bool default case is not yet supported".into());
            }
            let info = Self::field(alt, 0)?;
            let name = Self::name(Self::field(info, 0)?, 0)?;
            let cidx = Self::nat(Self::field(info, 1)?)?;
            let expected = match cidx {
                0 => "Bool.false",
                1 => "Bool.true",
                _ => return Err(format!("invalid Bool constructor index {cidx}")),
            };
            if name != expected || seen[cidx] {
                return Err(format!("invalid or repeated Bool alternative {name}"));
            }
            seen[cidx] = true;
            writeln!(code, "        {cidx} => {{").unwrap();
            // Branch-local variable definitions must never leak across arms.
            let mut arm_env = env.clone();
            Self::body(
                Self::field(alt, 1)?,
                code,
                depth + 1,
                count,
                &mut arm_env,
                ret_ty,
                ctx,
            )?;
            writeln!(code, "        }}").unwrap();
        }
        if !seen.into_iter().all(|b| b) {
            return Err("incomplete Bool alternatives".into());
        }
        writeln!(
            code,
            "        _ => unreachable!(\"invalid Lean Bool tag\"),"
        )
        .unwrap();
        writeln!(code, "    }}").unwrap();
        Ok(())
    }

    // Data-free inductives may use UInt8 or tagged scalar storage.
    // Constructor identity, not a guessed source datatype, directs patterns.
    unsafe fn scalar_enum_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> Result<(), String> {
        let repr = match Self::tag(Self::field(x, 2)?)? {
            1 => "u8",
            12 => "usize",
            _ => return Err("non-scalar inductive case is unsupported".into()),
        };
        let _storage_type = Self::name(Self::field(x, 0)?, 0)?;
        let scrutinee = Self::var(Self::field(x, 1)?)?;
        if env.get(&scrutinee) != Some(&repr) {
            return Err("inductive scrutinee storage type mismatch".into());
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.is_empty() || alts.len() > 256 {
            return Err("tagged case has unsupported number of alternatives".into());
        }
        let mut seen = BTreeSet::new();
        let mut constructor_parent: Option<String> = None;
        let mut default = None;
        writeln!(code, "    match x_{scrutinee} {{").unwrap();
        for alt in alts {
            match Self::tag(alt)? {
                0 => {
                    let info = Self::field(alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    let parent = name
                        .rsplit_once('.')
                        .map(|(p, _)| p)
                        .ok_or_else(|| format!("unqualified inductive constructor {name}"))?;
                    if let Some(prior) = &constructor_parent {
                        if prior != parent {
                            return Err(format!(
                                "mixed inductive constructor families: {prior} and {parent}"
                            ));
                        }
                    } else {
                        constructor_parent = Some(parent.to_owned());
                    }
                    let index = Self::nat(Self::field(info, 1)?)?;
                    if index > 255 || !seen.insert(index) {
                        return Err(format!("invalid or repeated tagged constructor {name}"));
                    }
                    writeln!(code, "        {index} => {{").unwrap();
                    let mut branch_env = env.clone();
                    Self::body(
                        Self::field(alt, 1)?,
                        code,
                        depth + 1,
                        count,
                        &mut branch_env,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "        }}").unwrap();
                }
                1 => {
                    if default.replace(Self::field(alt, 0)?).is_some() {
                        return Err("multiple tagged default alternatives".into());
                    }
                }
                t => return Err(format!("unknown tagged alternative constructor {t}")),
            }
        }
        if constructor_parent.is_none() {
            return Err("scalar inductive case lacks constructor identity".into());
        }
        if let Some(body) = default {
            writeln!(code, "        _ => {{").unwrap();
            let mut branch_env = env.clone();
            Self::body(body, code, depth + 1, count, &mut branch_env, ret_ty, ctx)?;
            writeln!(code, "        }}").unwrap();
        } else {
            writeln!(
                code,
                "        _ => unreachable!(\"invalid tagged enum value\"),"
            )
            .unwrap();
        }
        writeln!(code, "    }}").unwrap();
        Ok(())
    }

    unsafe fn body(
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
            match Self::tag(x)? {
                0 => {
                    // vdecl(x, ty, expr, body)
                    let name = Self::var(Self::field(x, 0)?)?;
                    let ty = Self::ty(Self::field(x, 1)?)?;
                    let expr = Self::field(x, 2)?;
                    if Self::tag(expr)? == 0 && !matches!(Self::tag(Self::field(x, 1)?)?, 1 | 12) {
                        return Err(
                            "nullary constructor needs UInt8 or tagged scalar IRType".into()
                        );
                    }
                    let value = Self::expr(expr, ty, env, ctx.functions)?;
                    if env.insert(name, ty).is_some() {
                        return Err(format!("variable x_{name} defined more than once"));
                    }
                    writeln!(code, "    let x_{name}: {ty} = {value};").unwrap();
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
                        if value_env.insert(var, ty).is_some() {
                            return Err(format!(
                                "join parameter x_{var} reused a visible variable"
                            ));
                        }
                        param_code.push(format!("x_{var}: {ty}"));
                        param_types.push(ty);
                    }
                    writeln!(
                        code,
                        "    let j_{id} = |{}| -> {ret_ty} {{",
                        param_code.join(", ")
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
                9 => {
                    // case(tid, scrutinee, type, alts)
                    let alts = Self::array(Self::field(x, 3)?)?;
                    let mut is_bool = false;
                    for alt in &alts {
                        if Self::tag(*alt)? == 0 {
                            let name = Self::name(Self::field(Self::field(*alt, 0)?, 0)?, 0)?;
                            is_bool = name == "Bool.false" || name == "Bool.true";
                            break;
                        }
                    }
                    if is_bool {
                        Self::boolean_case(x, code, depth, count, env, ret_ty, ctx)?;
                    } else {
                        Self::scalar_enum_case(x, code, depth, count, env, ret_ty, ctx)?;
                    }
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
                        lowered.push(Self::arg(arg, env, ty)?);
                    }
                    writeln!(code, "    return j_{id}({});", lowered.join(", ")).unwrap();
                    return Ok(());
                }
                10 => {
                    // ret(Arg)
                    writeln!(
                        code,
                        "    return {};",
                        Self::arg(Self::field(x, 0)?, env, ret_ty)?
                    )
                    .unwrap();
                    return Ok(());
                }
                t => return Err(format!("IR body constructor {t} unsupported")),
            }
        }
    }
    unsafe fn emit(decl: Obj, rust_name: Obj) -> Result<String, String> {
        Self::emit_function(decl, &Self::string(rust_name)?, None)
    }

    unsafe fn emit_function(
        decl: Obj,
        rust_name: &str,
        functions: Option<&FunctionTable>,
    ) -> Result<String, String> {
        if Self::tag(decl)? != 0 {
            return Err("extern declaration without executable body".into());
        }
        let declared_name = Self::name(Self::field(decl, 0)?, 0)?;
        if rust_name.is_empty()
            || !rust_name.as_bytes()[0].is_ascii_alphabetic()
            || !rust_name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_')
        {
            return Err("unsafe Rust function name".into());
        }
        const KEYWORDS: &[&str] = &[
            "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum",
            "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod",
            "move", "mut", "pub", "ref", "return", "self", "Self", "static", "struct", "super",
            "trait", "true", "type", "unsafe", "use", "where", "while", "abstract", "become",
            "box", "gen", "try", "typeof", "unsized", "virtual", "yield",
        ];
        if KEYWORDS.contains(&rust_name) || rust_name == "_" {
            return Err("reserved Rust function name".into());
        }
        let params = Self::array(Self::field(decl, 1)?)?;
        let ret = Self::ty(Self::field(decl, 2)?)?;
        let body = Self::field(decl, 3)?;
        let mut env = BTreeMap::new();
        let clean_name = declared_name.replace(['\n', '\r'], "_");
        let mut result = format!("// Generated directly from Lean IR declaration: {clean_name}\n");
        write!(result, "pub fn {rust_name}(").unwrap();
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            let var = Self::var(Self::field(*param, 0)?)?;
            let ty = Self::ty(Self::field(*param, 1)?)?;
            if env.insert(var, ty).is_some() {
                return Err(format!("duplicate parameter x_{var}"));
            }
            write!(result, "x_{var}: {ty}").unwrap();
        }
        writeln!(result, ") -> {ret} {{").unwrap();
        Self::body(
            body,
            &mut result,
            0,
            &mut 0,
            &mut env,
            ret,
            LoweringContext {
                functions,
                joins: &JoinTable::new(),
            },
        )?;
        result.push_str("}\n");
        Ok(result)
    }
}

// Naming is injective over UTF-8 bytes and independent of declaration ordering.
fn internal_name(lean_name: &str) -> String {
    let mut out = String::from("lean_");
    for byte in lean_name.as_bytes() {
        write!(&mut out, "{byte:02x}").unwrap();
    }
    out
}

impl Reader {
    unsafe fn signature(decl: Obj) -> Result<Signature, String> {
        if Self::tag(decl)? != 0 {
            return Err("extern or opaque declaration in native dependency closure".into());
        }
        let mut params = Vec::new();
        for param in Self::array(Self::field(decl, 1)?)? {
            params.push(Self::ty(Self::field(param, 1)?)?);
        }
        Ok(Signature {
            params,
            result: Self::ty(Self::field(decl, 2)?)?,
        })
    }

    // Traverse dependency IR iteratively to avoid stack growth on long
    // straight-line functions. All control-flow shapes not handled by the
    // emitter fail closed before code publication.
    unsafe fn body_calls(x: Obj, calls: &mut BTreeSet<String>) -> Result<(), String> {
        let mut pending = vec![x];
        let mut count = 0;
        while let Some(body) = pending.pop() {
            count += 1;
            if count > 100_000 {
                return Err("dependency IR traversal exceeded 100000 instructions".into());
            }
            match Self::tag(body)? {
                0 => {
                    let expr = Self::field(body, 2)?;
                    if Self::tag(expr)? == 6 {
                        calls.insert(Self::name(Self::field(expr, 0)?, 0)?);
                    }
                    pending.push(Self::field(body, 3)?);
                }
                1 => {
                    pending.push(Self::field(body, 2)?);
                    pending.push(Self::field(body, 3)?);
                }
                9 => {
                    for alt in Self::array(Self::field(body, 3)?)? {
                        match Self::tag(alt)? {
                            0 => pending.push(Self::field(alt, 1)?),
                            1 => pending.push(Self::field(alt, 0)?),
                            t => return Err(format!("unknown alternative constructor {t}")),
                        }
                    }
                }
                10 | 11 => (),
                t => {
                    return Err(format!(
                        "dependency traversal does not support IR body constructor {t}"
                    ))
                }
            }
        }
        Ok(())
    }

    unsafe fn emit_module(decls: Obj, root: Obj, public_name: Obj) -> Result<String, String> {
        let root = Self::string(root)?;
        let public_name = Self::string(public_name)?;
        Self::emit_roots(decls, vec![(root, public_name)])
    }

    unsafe fn emit_module_many(decls: Obj, roots: Obj) -> Result<String, String> {
        let mut public_roots = Vec::new();
        for item in Self::array(roots)? {
            let root = Self::string(item)?;
            // In v1 we expose the final Lean identifier as the Rust public API.
            // Any collisions (e.g. Foo.run and Bar.run) must refuse.
            let public = root.rsplit('.').next().unwrap_or("").to_owned();
            public_roots.push((root, public));
        }
        Self::emit_roots(decls, public_roots)
    }

    unsafe fn emit_roots(decls: Obj, roots: Vec<(String, String)>) -> Result<String, String> {
        if roots.is_empty() || roots.len() > 128 {
            return Err("expected 1..128 public Lean root declarations".into());
        }
        let entries = Self::array(decls)?;
        let mut definitions = BTreeMap::<String, Obj>::new();
        for decl in entries {
            let name = Self::name(Self::field(decl, 0)?, 0)?;
            if definitions.insert(name.clone(), decl).is_some() {
                return Err(format!("duplicate IR declaration in closure: {name}"));
            }
        }
        let mut pending = Vec::new();
        let mut public_names = BTreeSet::new();
        let mut root_names = BTreeSet::new();
        for (root, public) in &roots {
            if !root_names.insert(root.clone()) {
                return Err(format!("duplicate public Lean root: {root}"));
            }
            if !public_names.insert(public.clone()) {
                return Err(format!("duplicate Rust public API name: {public}"));
            }
            if !definitions.contains_key(root) {
                return Err(format!("requested Lean root {root} has no compiler IR"));
            }
            pending.push(root.clone());
        }
        let mut visited = BTreeSet::<String>::new();
        let mut closure = BTreeMap::<String, Obj>::new();
        let mut signatures = FunctionTable::new();
        while let Some(name) = pending.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }
            if visited.len() > 2048 {
                return Err("native declaration closure exceeds 2048 functions".into());
            }
            let decl = *definitions.get(&name).ok_or_else(||
                format!("dependency {name} has no compiled IR in the current module; no external fallback"))?;
            let sig = Self::signature(decl).map_err(|e| format!("{name}: {e}"))?;
            let mut called = BTreeSet::new();
            Self::body_calls(Self::field(decl, 3)?, &mut called)?;
            for callee in called {
                if !is_primitive(&callee) {
                    pending.push(callee);
                }
            }
            signatures.insert(name.clone(), sig);
            closure.insert(name, decl);
        }
        let mut result = String::from(
            "// Native in-process Lean IR closure; no JSON or Lean runtime dependency.\n",
        );
        for (name, decl) in &closure {
            result.push_str(&Self::emit_function(
                *decl,
                &internal_name(name),
                Some(&signatures),
            )?);
            result.push('\n');
        }
        // An exported public name cannot shadow a generated internal callee.
        // Internal names are byte-injective over the full Lean declaration name.
        let internal_names = closure
            .keys()
            .map(|name| internal_name(name))
            .collect::<BTreeSet<_>>();
        for (root, public_name) in &roots {
            if internal_names.contains(public_name) {
                return Err(format!(
                    "{root}: public export {public_name} collides with an internal Lean symbol"
                ));
            }
        }
        // Exact same dependency closure is shared by all public wrappers.
        for (root, public_name) in roots {
            let sig = signatures
                .get(&root)
                .ok_or("requested root missing from closure")?;
            // Validate the identifier, including Rust reserved words.
            let _ = Self::emit_function(
                *closure.get(&root).unwrap(),
                &public_name,
                Some(&signatures),
            )?;
            write!(result, "pub fn {public_name}(").unwrap();
            for (i, ty) in sig.params.iter().enumerate() {
                if i > 0 {
                    result.push_str(", ");
                }
                write!(result, "p_{i}: {ty}").unwrap();
            }
            write!(
                result,
                ") -> {} {{\n    {}(",
                sig.result,
                internal_name(&root)
            )
            .unwrap();
            for i in 0..sig.params.len() {
                if i > 0 {
                    result.push_str(", ");
                }
                write!(result, "p_{i}").unwrap();
            }
            result.push_str(")\n}\n");
        }
        Ok(result)
    }
}

// One pinned primitive registry drives lowering, closure collection, and tests.
// Unsupported or undocumented functions never fall back to host operations.
const PRIMITIVE_REGISTRY: &str = include_str!("../primitive-registry.tsv");

struct PrimitiveSpec<'a> {
    operand_type: &'a str,
    rust_op: &'a str,
    comparison: bool,
}

fn primitive_spec(name: &str) -> Option<PrimitiveSpec<'static>> {
    PRIMITIVE_REGISTRY
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .find_map(|line| {
            let mut cells = line.split('\t');
            let id = cells.next()?;
            let operand_type = cells.next()?;
            let rust_op = cells.next()?;
            let kind = cells.next()?;
            if cells.next().is_some() || id != name {
                return None;
            }
            Some(PrimitiveSpec {
                operand_type,
                rust_op,
                comparison: kind == "comparison",
            })
        })
}

fn is_primitive(name: &str) -> bool {
    primitive_spec(name).is_some()
}

unsafe fn reply_module_many(decls: Obj, roots: Obj) -> *mut c_void {
    let text = match std::panic::catch_unwind(|| Reader::emit_module_many(decls, roots)) {
        Ok(Ok(s)) => format!("OK\n{s}"),
        Ok(Err(e)) => format!("ERROR\n{e}"),
        Err(_) => "ERROR\nbackend panic (no code emitted)".into(),
    };
    lean_mk_string(
        CString::new(text.replace('\0', "\\0"))
            .expect("no interior NUL")
            .as_ptr(),
    )
}

/// # Safety
/// Arguments are synchronously borrowed Lean 4.34.1 Array IR.Decl and Array String.
#[no_mangle]
pub unsafe extern "C" fn rs_emit_ir_module_many(decls: Obj, roots: Obj) -> *mut c_void {
    reply_module_many(decls, roots)
}
/// # Safety
/// Interpreter entrypoint with same Lean ABI contract as rs_emit_ir_module_many.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn l_NativeRust_emitModuleMany(decls: Obj, roots: Obj) -> *mut c_void {
    reply_module_many(decls, roots)
}
/// # Safety
/// Boxed interpreter entrypoint with same Lean ABI contract.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn l_NativeRust_emitModuleMany___boxed(
    decls: Obj,
    roots: Obj,
) -> *mut c_void {
    reply_module_many(decls, roots)
}

unsafe fn reply_module(decls: Obj, root: Obj, public_name: Obj) -> *mut c_void {
    let text = match std::panic::catch_unwind(|| Reader::emit_module(decls, root, public_name)) {
        Ok(Ok(s)) => format!("OK\n{s}"),
        Ok(Err(e)) => format!("ERROR\n{e}"),
        Err(_) => "ERROR\nbackend panic (no code emitted)".into(),
    };
    let text = text.replace('\0', "\\0");
    let cstr = CString::new(text).expect("replaced NUL");
    lean_mk_string(cstr.as_ptr())
}

/// # Safety
/// Arguments must be live borrowed Lean 4.34.1 Array IR.Decl, String, String.
#[no_mangle]
pub unsafe extern "C" fn rs_emit_ir_module(decls: Obj, root: Obj, public_name: Obj) -> *mut c_void {
    reply_module(decls, root, public_name)
}
/// # Safety
/// Interpreter entrypoint: same synchronous borrow contract as rs_emit_ir_module.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn l_NativeRust_emitModule(decls: Obj, root: Obj, name: Obj) -> *mut c_void {
    reply_module(decls, root, name)
}
/// # Safety
/// Boxed interpreter entrypoint.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn l_NativeRust_emitModule___boxed(
    decls: Obj,
    root: Obj,
    name: Obj,
) -> *mut c_void {
    reply_module(decls, root, name)
}

unsafe fn reply(decl: Obj, name: Obj) -> *mut c_void {
    let text = match std::panic::catch_unwind(|| Reader::emit(decl, name)) {
        Ok(Ok(s)) => format!("OK\n{s}"),
        Ok(Err(e)) => format!("ERROR\n{e}"),
        Err(_) => "ERROR\nbackend panic (no code emitted)".into(),
    };
    // Lean strings do not contain NUL bytes. Sanitizing inputs prevents interior
    // NUL from causing an FFI panic; diagnostics remain safely in the error channel.
    let text = text.replace('\0', "\\0");
    let cstr = CString::new(text).expect("replaced NUL");
    lean_mk_string(cstr.as_ptr())
}

// `rs_emit_ir` is the native compiled ABI; the l_* names let Lean's
// interpreter use the same shared library through `--load-dynlib`.
/// # Safety
/// `decl` must be a live borrowed `Lean.IR.Decl` and `name` a live borrowed
/// Lean String from the exact pinned Lean 4.34.1 runtime.
#[no_mangle]
pub unsafe extern "C" fn rs_emit_ir(decl: Obj, name: Obj) -> *mut c_void {
    reply(decl, name)
}

/// # Safety
/// Same ABI and borrowed arguments as `rs_emit_ir`; interpreter entrypoint.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn l_NativeRust_emit(decl: Obj, name: Obj) -> *mut c_void {
    reply(decl, name)
}

/// # Safety
/// Same ABI and borrowed arguments as `rs_emit_ir`; boxed interpreter entrypoint.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn l_NativeRust_emit___boxed(decl: Obj, name: Obj) -> *mut c_void {
    reply(decl, name)
}

#[cfg(test)]
mod tests {
    use super::{internal_name, primitive_spec, PRIMITIVE_REGISTRY};
    use std::collections::BTreeSet;
    #[test]
    fn closure_symbol_mangling_is_injective_on_ascii_names() {
        assert_ne!(internal_name("X.ab"), internal_name("X.a_b"));
        assert_ne!(internal_name("X.A"), internal_name("X.a"));
        assert!(internal_name("X.a").starts_with("lean_"));
    }
    #[test]
    fn primitive_registry_is_complete_and_unambiguous() {
        let mut seen = BTreeSet::new();
        for line in PRIMITIVE_REGISTRY.lines() {
            if line.starts_with('#') || line.is_empty() {
                continue;
            }
            let parts = line.split('\t').collect::<Vec<_>>();
            assert_eq!(parts.len(), 4, "malformed registry row: {line}");
            let name = parts[0];
            assert!(seen.insert(name), "duplicate primitive: {name}");
            let (family, operation) = name.split_once('.').expect("primitive qualified name");
            assert!(
                ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"].contains(&family),
                "unsupported primitive family: {family}"
            );
            assert!(
                ["add", "sub", "mul", "decEq", "decLt", "decLe", "div", "mod", "land", "lor", "xor", "shiftLeft", "shiftRight"].contains(&operation),
                "unreviewed primitive operation: {operation}"
            );
            let spec = primitive_spec(name).expect("registered primitive cannot disappear");
            assert_eq!(spec.operand_type, parts[1]);
            assert_eq!(spec.rust_op, parts[2]);
            assert_eq!(spec.comparison, parts[3] == "comparison");
        }
        for family in ["UInt8", "UInt16", "UInt32", "UInt64", "USize"] {
            for operation in ["add", "sub", "mul", "decEq", "decLt", "decLe", "div", "mod", "land", "lor", "xor", "shiftLeft", "shiftRight"] {
                let name = format!("{family}.{operation}");
                assert!(seen.contains(name.as_str()), "primitive missing: {name}");
            }
        }
        for operation in ["add", "sub", "mul"] {
            let name = format!("Float.{operation}");
            assert!(
                seen.contains(name.as_str()),
                "missing finite-f64 primitive: {name}"
            );
        }
        assert_eq!(seen.len(), 68);
        assert!(primitive_spec("UInt64.shiftLeft").is_none());
        assert!(primitive_spec("IO.println").is_none());
    }

    #[test]
    fn permitted_rust_identacters_only() {
        for s in ["a", "a_1", "Fn2"] {
            assert!(s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'));
        }
    }
}
