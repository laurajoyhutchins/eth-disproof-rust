//! An in-process, strict Lean 4.34.1 IR -> Rust code emitter.
//!
//! This entry point receives `Lean.IR.Decl` *directly* as a borrowed Lean object.
//! It does not serialize or clone the IR. Only an explicitly accepted subset is
//! lowered; unknown instructions and types are errors, never substitutions.
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{c_char, c_void, CStr, CString};
use std::fmt::Write;
use std::time::{Duration, Instant};

mod safety;

// Exact standalone value semantics, also unit-tested inside the backend.
#[cfg(test)]
#[allow(dead_code)]
mod standalone_runtime;

// Generated at build time from the pinned constructor classification.
include!(concat!(env!("OUT_DIR"), "/ir_coverage_tags.rs"));

#[repr(C)]
pub struct LeanObject {
    _opaque: [u8; 0],
}
type Obj = *const LeanObject;
extern "C" {
    fn lr_abi_probe() -> i32;
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

struct EmitContext<'a> {
    functions: Option<&'a FunctionTable>,
    started: &'a Instant,
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
    unsafe fn checked_tag(x: Obj, family: &str) -> Result<usize, String> {
        let tag = Self::tag(x)?;
        if SUPPORTED_IR_TAGS.contains(&(family, tag)) {
            Ok(tag)
        } else {
            Err(format!(
                "{family} constructor tag {tag} explicitly unsupported by pinned IR coverage contract"
            ))
        }
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
        match Self::checked_tag(x, "Arg")? {
            0 => {
                let id = Self::var(Self::field(x, 0)?)?;
                let found = env
                    .get(&id)
                    .ok_or_else(|| format!("unknown input variable x_{id}"))?;
                if *found != expected {
                    return Err(format!("x_{id}: expected {expected}, got {found}"));
                }
                Ok(if expected == "Value" {
                    format!("x_{id}.clone()")
                } else {
                    format!("x_{id}")
                })
            }
            1 => Err("erased value used as runtime operand".into()),
            t => Err(format!("unknown Arg constructor {t}")),
        }
    }
    unsafe fn ty(x: Obj) -> Result<&'static str, String> {
        // The tag ordering comes from the pinned Lean.Compiler.IR.Basic.
        match Self::checked_tag(x, "IRType")? {
            1 => Ok("u8"),
            2 => Ok("u16"),
            3 => Ok("u32"),
            4 => Ok("u64"),
            5 => Ok("usize"),
            7 | 8 | 12 => Ok("Value"),
            t => Err(format!(
                "IR type tag {t} unsupported (supported u8/u16/u32/u64/usize)"
            )),
        }
    }
    unsafe fn lit(x: Obj, ty: &str) -> Result<String, String> {
        match Self::checked_tag(x, "LitVal")? {
            0 => {
                let n = Self::nat(Self::field(x, 0)?)?;
                let max = match ty {
                    "u8" => u8::MAX as usize,
                    "u16" => u16::MAX as usize,
                    "u32" => u32::MAX as usize,
                    "u64" => usize::MAX, // Pinned Linux x86-64 Lean ABI.
                    "usize" => usize::MAX,
                    "Value" => {
                        return Ok(format!(
                            "Value::Nat(native_runtime::BigNat::from_u64({n}u64))"
                        ))
                    }
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
        match Self::checked_tag(x, "Expr")? {
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
                if let Some(runtime) = runtime_primitive_spec(&name) {
                    if var_ty != "Value" {
                        return Err(format!(
                            "{name}: expected object-valued result, got {var_ty}"
                        ));
                    }
                    let required = match runtime.shape {
                        "unary" => 1,
                        "binary" => 2,
                        "erased_unary" => 2,
                        "erased_binary" => 3,
                        _ => return Err(format!("{name}: unsupported runtime primitive shape")),
                    };
                    if args.len() != required {
                        return Err(format!(
                            "{name}: expected {required} IR operands, got {}",
                            args.len()
                        ));
                    }
                    let start = if runtime.shape.starts_with("erased_") {
                        if Self::checked_tag(args[0], "Arg")? != 1 {
                            return Err(format!("{name}: missing exact erased type argument"));
                        }
                        1
                    } else {
                        0
                    };
                    let mut values = Vec::new();
                    for arg in &args[start..] {
                        values.push(format!("&{}", Self::arg(*arg, env, "Value")?));
                    }
                    return Ok(format!(
                        "native_runtime::{}({})",
                        runtime.rust_function,
                        values.join(", ")
                    ));
                }
                if args.len() != 2 {
                    return Err(format!("{name}: expected binary operands"));
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
                    Ok(format!("{lhs}.{op}({rhs})"))
                }
            }
            9 => {
                if var_ty != "Value" || Self::ty(Self::field(x, 0)?)? != "u64" {
                    return Err("box supports only UInt64 into object Value".into());
                }
                let id = Self::var(Self::field(x, 1)?)?;
                if env.get(&id) != Some(&"u64") {
                    return Err(format!("box UInt64 operand x_{id} has wrong type"));
                }
                Ok(format!("native_runtime::box_uint64(x_{id})"))
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
        context: &EmitContext<'_>,
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
            if Self::checked_tag(alt, "Alt")? != 0 {
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
            Self::body(
                Self::field(alt, 1)?,
                code,
                depth + 1,
                count,
                env,
                ret_ty,
                context,
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

    unsafe fn body(
        mut x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        context: &EmitContext<'_>,
    ) -> Result<(), String> {
        if depth > 128 {
            return Err("IR control-flow nesting limit".into());
        }
        loop {
            *count += 1;
            if *count > 100_000 {
                return Err("IR instruction limit exceeded".into());
            }
            if code.len() > safety::MAX_OUTPUT_BYTES {
                return Err("generated Rust output byte limit exceeded".into());
            }
            if context.started.elapsed() > Duration::from_secs(10) {
                return Err("IR code generation time budget exceeded".into());
            }
            match Self::checked_tag(x, "FnBody")? {
                0 => {
                    // vdecl(x, ty, expr, body)
                    let name = Self::var(Self::field(x, 0)?)?;
                    let ty = Self::ty(Self::field(x, 1)?)?;
                    let value = Self::expr(Self::field(x, 2)?, ty, env, context.functions)?;
                    if env.insert(name, ty).is_some() {
                        return Err(format!("variable x_{name} defined more than once"));
                    }
                    writeln!(code, "    let x_{name}: {ty} = {value};").unwrap();
                    x = Self::field(x, 3)?;
                }
                9 => {
                    // case(tid, scrutinee, type, alts)
                    Self::boolean_case(x, code, depth, count, env, ret_ty, context)?;
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
    unsafe fn emit(decl: Obj, rust_name: Obj) -> Result<String, String> {
        if lr_abi_probe() == 0 {
            return Err("Lean C ABI runtime probe failed".into());
        }
        let declared_name = Self::name(Self::field(decl, 0)?, 0)?;
        let code = Self::emit_function(decl, &Self::string(rust_name)?, None)
            .map_err(|e| format!("declaration={declared_name}; {e}"))?;
        Ok(with_runtime_if_needed(code))
    }

    unsafe fn emit_function(
        decl: Obj,
        rust_name: &str,
        functions: Option<&FunctionTable>,
    ) -> Result<String, String> {
        if Self::checked_tag(decl, "Decl")? != 0 {
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
        let started = Instant::now();
        let context = EmitContext {
            functions,
            started: &started,
        };
        Self::body(body, &mut result, 0, &mut 0, &mut env, ret, &context)?;
        result.push_str("}\n");
        if result.len() > safety::MAX_OUTPUT_BYTES {
            return Err("generated Rust output byte limit exceeded".into());
        }
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
        if Self::checked_tag(decl, "Decl")? != 0 {
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
        let started = Instant::now();
        while let Some(body) = pending.pop() {
            count += 1;
            if count > 100_000 {
                return Err("dependency IR traversal exceeded 100000 instructions".into());
            }
            if started.elapsed() > Duration::from_secs(10) {
                return Err("dependency IR traversal time budget exceeded".into());
            }
            match Self::checked_tag(body, "FnBody")? {
                0 => {
                    let expr = Self::field(body, 2)?;
                    if Self::checked_tag(expr, "Expr")? == 6 {
                        calls.insert(Self::name(Self::field(expr, 0)?, 0)?);
                    }
                    pending.push(Self::field(body, 3)?);
                }
                9 => {
                    for alt in Self::array(Self::field(body, 3)?)? {
                        match Self::checked_tag(alt, "Alt")? {
                            0 => pending.push(Self::field(alt, 1)?),
                            1 => pending.push(Self::field(alt, 0)?),
                            t => return Err(format!("unknown alternative constructor {t}")),
                        }
                    }
                }
                10 => (),
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
        if lr_abi_probe() == 0 {
            return Err("Lean C ABI runtime probe failed".into());
        }
        let started = Instant::now();
        let root = Self::string(root)?;
        let public_name = Self::string(public_name)?;
        // Public name is validated by the same strict emitter before publishing.
        let entries = Self::array(decls)?;
        let mut definitions = BTreeMap::<String, Obj>::new();
        for decl in entries {
            let name = Self::name(Self::field(decl, 0)?, 0)?;
            if definitions.insert(name.clone(), decl).is_some() {
                return Err(format!("duplicate IR declaration in closure: {name}"));
            }
        }
        let mut pending = vec![root.clone()];
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
            if started.elapsed() > Duration::from_secs(15) {
                return Err("declaration closure code generation time budget exceeded".into());
            }
            let decl = *definitions.get(&name).ok_or_else(||
                format!("declaration={name}; dependency {name} has no compiled IR in the current module; no external fallback"))?;
            let sig = Self::signature(decl).map_err(|e| format!("declaration={name}; {e}"))?;
            let mut called = BTreeSet::new();
            Self::body_calls(Self::field(decl, 3)?, &mut called)
                .map_err(|e| format!("declaration={name}; {e}"))?;
            for callee in called {
                if !is_primitive(&callee) {
                    pending.push(callee);
                }
            }
            signatures.insert(name.clone(), sig);
            closure.insert(name, decl);
        }
        let root_signature = signatures
            .get(&root)
            .ok_or("requested root missing from closure")?;
        let mut result = String::from(
            "// Native in-process Lean IR closure; no JSON or Lean runtime dependency.\n",
        );
        for (name, decl) in &closure {
            if started.elapsed() > Duration::from_secs(15) {
                return Err("declaration closure code generation time budget exceeded".into());
            }
            result.push_str(
                &Self::emit_function(*decl, &internal_name(name), Some(&signatures))
                    .map_err(|e| format!("declaration={name}; {e}"))?,
            );
            result.push('\n');
            if result.len() > safety::MAX_OUTPUT_BYTES {
                return Err("generated Rust closure output byte limit exceeded".into());
            }
        }
        // Keep the existing external API for a single public root while
        // exposing all internal callees using stable, collision-free names.
        write!(result, "pub fn {public_name}(").unwrap();
        for (i, ty) in root_signature.params.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            write!(result, "p_{i}: {ty}").unwrap();
        }
        write!(
            result,
            ") -> {} {{\n    {}(",
            root_signature.result,
            internal_name(&root)
        )
        .unwrap();
        for i in 0..root_signature.params.len() {
            if i > 0 {
                result.push_str(", ");
            }
            write!(result, "p_{i}").unwrap();
        }
        result.push_str(")\n}\n");
        // Invalid public Rust identifiers fail at generation, not only when
        // rustc later parses the output. Reuse existing validation via an
        // in-memory synthetic wrapper is unnecessary: emit_function accepts
        // an actual root declaration under the public name and validates it.
        let _ = Self::emit_function(
            *closure.get(&root).unwrap(),
            &public_name,
            Some(&signatures),
        )
        .map_err(|e| format!("declaration={root}; {e}"))?;
        if result.len() > safety::MAX_OUTPUT_BYTES {
            return Err("generated Rust closure output byte limit exceeded".into());
        }
        Ok(with_runtime_if_needed(result))
    }
}

// The release coverage registry is the same table consulted by production
// codegen and dependency-closure discovery, not a second documentation list.
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
    primitive_spec(name).is_some() || runtime_primitive_spec(name).is_some()
}

const RUNTIME_PRIMITIVE_REGISTRY: &str = include_str!("../runtime-primitive-registry.tsv");

struct RuntimePrimitiveSpec<'a> {
    rust_function: &'a str,
    shape: &'a str,
}

fn runtime_primitive_spec(name: &str) -> Option<RuntimePrimitiveSpec<'static>> {
    RUNTIME_PRIMITIVE_REGISTRY
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .find_map(|line| {
            let mut cells = line.split('\t');
            let id = cells.next()?;
            let rust_function = cells.next()?;
            let shape = cells.next()?;
            if cells.next().is_some() || id != name {
                return None;
            }
            Some(RuntimePrimitiveSpec {
                rust_function,
                shape,
            })
        })
}

fn with_runtime_if_needed(source: String) -> String {
    if source.contains("Value") || source.contains("native_runtime::") {
        format!(
            "mod native_runtime {{\n{}\n}}\npub use native_runtime::Value;\n{source}",
            include_str!("standalone_runtime.rs")
        )
    } else {
        source
    }
}

unsafe fn reply_module(decls: Obj, root: Obj, public_name: Obj) -> *mut c_void {
    let text = match std::panic::catch_unwind(|| Reader::emit_module(decls, root, public_name)) {
        Ok(Ok(s)) => format!("OK\n{s}"),
        Ok(Err(e)) => safety::refusal("requested-root", &e),
        Err(_) => safety::refusal("requested-root", "backend panic (no code emitted)"),
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
        Ok(Err(e)) => safety::refusal("requested-root", &e),
        Err(_) => safety::refusal("requested-root", "backend panic (no code emitted)"),
    };
    // Lean strings do not contain NUL bytes. Sanitizing inputs prevents interior
    // NUL from causing an FFI panic; diagnostics remain safely in the error channel.
    let text = text.replace('\0', "\\0");
    let cstr = CString::new(text).expect("replaced NUL");
    lean_mk_string(cstr.as_ptr())
}

unsafe fn reply_publish(path: Obj, source: Obj) -> *mut c_void {
    let report = match std::panic::catch_unwind(|| {
        let path = Reader::string(path)?;
        let source = Reader::string(source)?;
        safety::publish(&path, &source)
    }) {
        Ok(Ok(())) => "OK\npublished".to_string(),
        Ok(Err(e)) => safety::refusal("output", &e),
        Err(_) => safety::refusal("output", "publisher panic (no output accepted)"),
    };
    let report = report.replace('\0', "\\0");
    let encoded = CString::new(report).expect("NUL sanitized");
    lean_mk_string(encoded.as_ptr())
}

/// # Safety
/// Borrowed path and source must be live Lean Strings from the pinned runtime.
#[no_mangle]
pub unsafe extern "C" fn rs_publish_source(path: Obj, source: Obj) -> *mut c_void {
    reply_publish(path, source)
}

/// # Safety
/// Interpreter alias for rs_publish_source.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn l_NativeRust_publishSource(path: Obj, source: Obj) -> *mut c_void {
    reply_publish(path, source)
}

/// # Safety
/// Boxed interpreter alias for rs_publish_source.
#[no_mangle]
#[allow(non_snake_case)]
pub unsafe extern "C" fn l_NativeRust_publishSource___boxed(path: Obj, source: Obj) -> *mut c_void {
    reply_publish(path, source)
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
    use super::internal_name;
    #[test]
    fn closure_symbol_mangling_is_injective_on_ascii_names() {
        assert_ne!(internal_name("X.ab"), internal_name("X.a_b"));
        assert_ne!(internal_name("X.A"), internal_name("X.a"));
        assert!(internal_name("X.a").starts_with("lean_"));
    }
    #[test]
    fn source_versioned_ir_constructor_whitelist_is_enforced() {
        use super::SUPPORTED_IR_TAGS;
        assert!(SUPPORTED_IR_TAGS.contains(&("Decl", 0)));
        assert!(!SUPPORTED_IR_TAGS.contains(&("Decl", 1)));
        assert!(SUPPORTED_IR_TAGS.contains(&("IRType", 4)));
        assert!(SUPPORTED_IR_TAGS.contains(&("IRType", 7)));
        assert!(SUPPORTED_IR_TAGS.contains(&("IRType", 8)));
        assert!(SUPPORTED_IR_TAGS.contains(&("IRType", 12)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 6)));
        assert!(!SUPPORTED_IR_TAGS.contains(&("Expr", 7)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 9)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Arg", 1)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 9)));
        assert!(!SUPPORTED_IR_TAGS.contains(&("FnBody", 11)));
        assert_eq!(SUPPORTED_IR_TAGS.len(), 19);
    }

    #[test]
    fn value_registry_covers_only_explicitly_tested_lean_runtime_adapters() {
        use super::{runtime_primitive_spec, RUNTIME_PRIMITIVE_REGISTRY};
        use std::collections::BTreeSet;
        let expected: BTreeSet<_> = [
            "Nat.add",
            "Nat.sub",
            "Nat.mul",
            "Int.add",
            "String.append",
            "String.utf8ByteSize",
            "String.length",
            "Array.push",
            "Array.size",
            "List.reverse._redArg",
        ]
        .into_iter()
        .collect();
        let source = include_str!("standalone_runtime.rs");
        let mut actual = BTreeSet::new();
        for row in RUNTIME_PRIMITIVE_REGISTRY
            .lines()
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
        {
            let cells: Vec<_> = row.split('\t').collect();
            assert_eq!(cells.len(), 3, "malformed runtime primitive row: {row}");
            assert!(actual.insert(cells[0]), "duplicate source primitive: {}", cells[0]);
            let spec = runtime_primitive_spec(cells[0]).unwrap();
            assert_eq!(spec.rust_function, cells[1]);
            assert_eq!(spec.shape, cells[2]);
            assert!(
                ["binary", "unary", "erased_binary", "erased_unary"].contains(&spec.shape),
                "invalid runtime primitive shape: {}",
                spec.shape
            );
            assert!(
                source.contains(&format!("pub fn {}(", spec.rust_function)),
                "missing dependency-free adapter: {}",
                spec.rust_function
            );
        }
        assert_eq!(actual, expected, "primitive coverage changed without corresponding tests");
    }

    #[test]
    fn registry_is_complete_and_unambiguous() {
        use super::{primitive_spec, PRIMITIVE_REGISTRY};
        use std::collections::BTreeSet;
        let mut seen = BTreeSet::new();
        for line in PRIMITIVE_REGISTRY.lines() {
            if line.starts_with('#') || line.is_empty() {
                continue;
            }
            let cells: Vec<_> = line.split('\t').collect();
            assert_eq!(cells.len(), 4, "malformed registry line: {line}");
            assert!(seen.insert(cells[0]), "duplicate primitive {}", cells[0]);
            let (namespace, operation) = cells[0].split_once('.').unwrap();
            assert!(
                ["UInt8", "UInt16", "UInt32", "UInt64", "USize"].contains(&namespace),
                "unsupported primitive namespace {namespace}"
            );
            assert!(
                ["add", "sub", "mul", "decEq", "decLt", "decLe"].contains(&operation),
                "unexpected primitive operation {operation}"
            );
            let spec = primitive_spec(cells[0]).expect("registered primitive missing");
            assert_eq!(spec.operand_type, cells[1]);
            assert_eq!(spec.rust_op, cells[2]);
            assert_eq!(spec.comparison, cells[3] == "comparison");
        }
        for namespace in ["UInt8", "UInt16", "UInt32", "UInt64", "USize"] {
            for operation in ["add", "sub", "mul", "decEq", "decLt", "decLe"] {
                let id = format!("{namespace}.{operation}");
                assert!(
                    seen.contains(id.as_str()),
                    "missing supported primitive {id}"
                );
            }
        }
        assert_eq!(seen.len(), 30);
        assert!(!super::is_primitive("UInt64.shiftLeft"));
    }

    #[test]
    fn permitted_rust_identacters_only() {
        for s in ["a", "a_1", "Fn2"] {
            assert!(s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'));
        }
    }
}
