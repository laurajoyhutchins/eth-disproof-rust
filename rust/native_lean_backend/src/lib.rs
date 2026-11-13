//! An in-process, strict Lean 4.34.1 IR -> Rust code emitter.
//!
//! This entry point receives `Lean.IR.Decl` *directly* as a borrowed Lean object.
//! It does not serialize or clone the IR. Only an explicitly accepted subset is
//! lowered; unknown instructions and types are errors, never substitutions.
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
                Ok(if p.is_empty() { s } else { format!("{p}.{s}") })
            }
            2 => {
                let p = Self::name(Self::field(x, 0)?, depth + 1)?;
                let n = Self::nat(Self::field(x, 1)?)?;
                Ok(format!("{p}.{n}"))
            }
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
    unsafe fn arg(x: Obj) -> Result<String, String> {
        match Self::tag(x)? {
            0 => Ok(format!("x_{}", Self::var(Self::field(x, 0)?)?)),
            1 => Err("erased value used as runtime operand".into()),
            t => Err(format!("unknown Arg constructor {t}")),
        }
    }
    unsafe fn ty(x: Obj) -> Result<&'static str, String> {
        // The tag ordering comes from the pinned Lean.Compiler.IR.Basic.
        match Self::tag(x)? {
            3 => Ok("u32"),
            4 => Ok("u64"),
            5 => Ok("usize"),
            t => Err(format!(
                "IR type tag {t} unsupported (currently u32/u64/usize only)"
            )),
        }
    }
    unsafe fn lit(x: Obj) -> Result<String, String> {
        match Self::tag(x)? {
            0 => Ok(Self::nat(Self::field(x, 0)?)?.to_string()),
            t => Err(format!("literal constructor {t} unsupported")),
        }
    }
    unsafe fn expr(x: Obj, var_ty: &str) -> Result<String, String> {
        match Self::tag(x)? {
            6 => {
                // fap
                let name = Self::name(Self::field(x, 0)?, 0)?;
                let args = Self::array(Self::field(x, 1)?)?;
                if args.len() != 2 {
                    return Err(format!("{name}: expected binary operands"));
                }
                let op = match (name.as_str(), var_ty) {
                    ("UInt64.add", "u64") | ("UInt32.add", "u32") | ("USize.add", "usize") => {
                        "wrapping_add"
                    }
                    ("UInt64.sub", "u64") | ("UInt32.sub", "u32") | ("USize.sub", "usize") => {
                        "wrapping_sub"
                    }
                    ("UInt64.mul", "u64") | ("UInt32.mul", "u32") | ("USize.mul", "usize") => {
                        "wrapping_mul"
                    }
                    _ => return Err(format!("unrecognized or mismatched call: {name}")),
                };
                Ok(format!(
                    "{}.{}({})",
                    Self::arg(args[0])?,
                    op,
                    Self::arg(args[1])?
                ))
            }
            11 => Ok(Self::lit(Self::field(x, 0)?)?),
            t => Err(format!("IR expression constructor {t} unsupported")),
        }
    }
    unsafe fn body(mut x: Obj, code: &mut String) -> Result<(), String> {
        let mut count = 0;
        loop {
            count += 1;
            if count > 1_000_000 {
                return Err("body instruction limit".into());
            }
            match Self::tag(x)? {
                0 => {
                    // vdecl(x, ty, expr, body)
                    let name = Self::var(Self::field(x, 0)?)?;
                    let ty = Self::ty(Self::field(x, 1)?)?;
                    let value = Self::expr(Self::field(x, 2)?, ty)?;
                    writeln!(code, "    let x_{name}: {ty} = {value};").unwrap();
                    x = Self::field(x, 3)?;
                }
                10 => {
                    // ret(Arg)
                    writeln!(code, "    {}", Self::arg(Self::field(x, 0)?)?).unwrap();
                    return Ok(());
                }
                t => return Err(format!("IR body constructor {t} unsupported")),
            }
        }
    }
    unsafe fn emit(decl: Obj, rust_name: Obj) -> Result<String, String> {
        if Self::tag(decl)? != 0 {
            return Err("extern declaration without executable body".into());
        }
        let declared_name = Self::name(Self::field(decl, 0)?, 0)?;
        let rust_name = Self::string(rust_name)?;
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
        if KEYWORDS.contains(&rust_name.as_str()) || rust_name == "_" {
            return Err("reserved Rust function name".into());
        }
        let params = Self::array(Self::field(decl, 1)?)?;
        let ret = Self::ty(Self::field(decl, 2)?)?;
        let body = Self::field(decl, 3)?;
        let clean_name = declared_name.replace(['\n', '\r'], "_");
        let mut result = format!("// Generated directly from Lean IR declaration: {clean_name}\n");
        write!(result, "pub fn {rust_name}(").unwrap();
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            let var = Self::var(Self::field(*param, 0)?)?;
            let ty = Self::ty(Self::field(*param, 1)?)?;
            write!(result, "x_{var}: {ty}").unwrap();
        }
        writeln!(result, ") -> {ret} {{").unwrap();
        Self::body(body, &mut result)?;
        result.push_str("}\n");
        Ok(result)
    }
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
    #[test]
    fn permitted_rust_identacters_only() {
        for s in ["a", "a_1", "Fn2"] {
            assert!(s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'));
        }
    }
}
