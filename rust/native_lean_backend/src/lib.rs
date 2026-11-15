//! An in-process, strict Lean 4.34.1 IR -> Rust code emitter.
//!
//! This entry point receives `Lean.IR.Decl` *directly* as a borrowed Lean object.
//! It does not serialize or clone the IR. Only an explicitly accepted subset is
//! lowered; unknown instructions and types are errors, never substitutions.
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{c_char, c_void, CStr, CString};
use std::fmt::Write;

mod safety;

// Generated from the complete reviewed pinned Lean IR constructor contract.
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
    fn lr_nat_decimal(x: Obj) -> *mut c_char;
    fn lr_free_string(x: *mut c_char);
    fn lr_string_size(x: Obj) -> usize;
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

#[derive(Clone, Copy)]
struct ImmutableCaseContext<'a> {
    lowering: LoweringContext<'a>,
    family: &'static str,
}

// Standalone immutable object model for the supported Lean IR subset.
// Rc cloning models shared immutable values; source inc/dec instructions are
// redundant only while mutation, isShared, reset and reuse remain unsupported.
const RUNTIME_SOURCE: &str = include_str!("runtime/immutable_value.rs");

const CONSTRUCTOR_SET_TEST_SOURCE: &str = r#"
#[cfg(test)]
mod __lean_constructor_set_tests {
    use super::__LeanValue;
    use std::rc::Rc;
    #[test]
    fn unique_reuses_allocation() {
        let original = __LeanValue::ctor(2, "PairLike.two", vec![__LeanValue::nat("3"), __LeanValue::nat("5")]);
        let before = Rc::as_ptr(&original.0);
        let updated = original.with_field(0, __LeanValue::nat("7"));
        assert!(std::ptr::eq(before, Rc::as_ptr(&updated.0)));
        assert_eq!(updated.field(0).nat_to_decimal(), "7");
    }
    #[test]
    fn shared_keeps_alias() {
        let original = __LeanValue::ctor(2, "PairLike.two", vec![__LeanValue::nat("3"), __LeanValue::nat("5")]);
        let alias = original.clone();
        let before = Rc::as_ptr(&original.0);
        let updated = original.with_field(1, __LeanValue::nat("11"));
        assert!(!std::ptr::eq(before, Rc::as_ptr(&updated.0)));
        assert_eq!(alias.field(1).nat_to_decimal(), "5");
        assert_eq!(updated.field(1).nat_to_decimal(), "11");
    }
    #[test]
    #[should_panic(expected = "constructor field set on non-constructor")]
    fn tagged_refuses() {
        let _ = __LeanValue::tagged(0).with_field(0, __LeanValue::nat("1"));
    }
}
"#;
const HEAP_JOIN_TEST_SOURCE: &str = r#"
#[cfg(test)]
mod __lean_heap_join_refinement_tests {
    use super::__LeanValue;
    #[test]
    fn constructor_heap_refines_tobject() {
        let value = __LeanValue::ctor(0, "Probe.ctor", vec![]);
        assert_eq!(value.require_constructor_object().tag(), 0);
    }
    #[test]
    #[should_panic(expected = "tobject join requires a heap constructor")]
    fn tagged_value_is_not_a_heap_constructor() {
        let _ = __LeanValue::tagged(0).require_constructor_object();
    }
    #[test]
    #[should_panic(expected = "tobject join requires a heap constructor")]
    fn erased_join_argument_is_not_a_heap_constructor() {
        let _ = __LeanValue::erased().require_constructor_object();
    }
}
"#;
const ARRAY_OWNERSHIP_TEST_SOURCE: &str = r#"
#[cfg(test)]
mod __lean_array_ownership_tests {
    use super::__LeanValue;
    use std::rc::Rc;

    #[test]
    fn unique_owner_reuses_array_allocation() {
        let empty = __LeanValue::empty_array(2);
        let original = Rc::as_ptr(&empty.0);
        let pushed = empty.array_push_owned(__LeanValue::tagged(7));
        assert!(std::ptr::eq(original, Rc::as_ptr(&pushed.0)));
        let original = Rc::as_ptr(&pushed.0);
        let updated = pushed.array_set_tagged_owned(0, __LeanValue::tagged(11));
        assert!(std::ptr::eq(original, Rc::as_ptr(&updated.0)));
        assert_eq!(updated.array_get_tagged(0).tagged_nat(), 11);
    }

    #[test]
    fn shared_owner_keeps_earlier_alias_unchanged() {
        let original = __LeanValue::empty_array(2)
            .array_push_owned(__LeanValue::tagged(3));
        let alias = original.clone();
        let allocation = Rc::as_ptr(&original.0);
        let updated = original.array_set_tagged_owned(0, __LeanValue::tagged(17));
        assert!(!std::ptr::eq(allocation, Rc::as_ptr(&updated.0)));
        assert_eq!(alias.array_get_tagged(0).tagged_nat(), 3);
        assert_eq!(updated.array_get_tagged(0).tagged_nat(), 17);
        let appended = alias.clone().array_push_owned(__LeanValue::tagged(19));
        assert_eq!(alias.array_size().nat_to_decimal(), "1");
        assert_eq!(appended.array_size().nat_to_decimal(), "2");
    }
}
"#;

fn is_value_type(ty: &str) -> bool {
    matches!(ty, "obj" | "tobj" | "tagged")
}

fn rust_type(ty: &str) -> &str {
    if is_value_type(ty) {
        "__LeanValue"
    } else {
        ty
    }
}

fn ir_type_compatible(found: &str, expected: &str) -> bool {
    found == expected || (expected == "tobj" && matches!(found, "obj" | "tagged"))
}

// Typed source constructor identities, not numeric tags alone, authorize
// immutable List/Option case lowering. This avoids List.nil==Option.none by
// accident even though both use the pinned Lean tagged-zero representation.
fn immutable_case_ctor(family: &str, index: usize, actual: &str) -> Result<usize, String> {
    let (expected, pointers) = match (family, index) {
        ("Option", 0) => ("Option.none", 0),
        ("Option", 1) => ("Option.some", 1),
        ("List", 0) => ("List.nil", 0),
        ("List", 1) => ("List.cons", 2),
        ("Sum", 0) => ("Sum.inl", 1),
        ("Sum", 1) => ("Sum.inr", 1),
        _ => {
            return Err(format!(
                "unsupported {family} object case constructor {actual} at tag {index}"
            ));
        }
    };
    if actual != expected {
        return Err(format!(
            "unsupported {family} object case constructor {actual} at tag {index}; expected {expected}"
        ));
    }
    Ok(pointers)
}

fn include_value_runtime(source: String) -> Result<String, String> {
    let code = if source.contains("__LeanValue") {
        // Runtime identity is shared by every generated package. Tests are
        // appended after functions so Clippy sees no items after a test module.
        let tests = if source.contains(".array_push(")
            || source.contains(".array_push_owned(")
            || source.contains(".array_set_tagged(")
            || source.contains(".array_set_tagged_owned(")
        {
            ARRAY_OWNERSHIP_TEST_SOURCE
        } else {
            ""
        };
        let set_tests = if source.contains(".with_field(") {
            CONSTRUCTOR_SET_TEST_SOURCE
        } else {
            ""
        };
        let heap_join_tests = if source.contains(".require_constructor_object()") {
            HEAP_JOIN_TEST_SOURCE
        } else {
            ""
        };
        format!("{RUNTIME_SOURCE}\n{source}\n{tests}\n{set_tests}\n{heap_join_tests}")
    } else {
        source
    };
    if code.len() > safety::MAX_OUTPUT_BYTES {
        return Err("complete standalone Rust source exceeds maximum output bytes".into());
    }
    Ok(code)
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
        let len = lr_string_size(x);
        if len == 0 || len > 1_048_577 {
            return Err("Lean String byte length outside supported bound".into());
        }
        let bytes = std::slice::from_raw_parts(ptr.cast::<u8>(), len - 1);
        String::from_utf8(bytes.to_vec()).map_err(|_| "invalid UTF-8".into())
    }
    // Convert an arbitrary-precision source Nat through Lean's pinned public
    // runtime API, never by interpreting GMP limbs or truncating to usize.
    unsafe fn decimal_nat(x: Obj) -> Result<String, String> {
        let raw = lr_nat_decimal(x);
        if raw.is_null() {
            return Err("large Nat literal rejected (invalid or over 4 KiB)".into());
        }
        let decoded = CStr::from_ptr(raw)
            .to_str()
            .map(str::to_owned)
            .map_err(|_| "invalid Nat literal decimal representation".to_owned());
        lr_free_string(raw);
        decoded
    }
    unsafe fn nat(x: Obj) -> Result<usize, String> {
        Self::scalar(x).map_err(|_| "large Nat unsupported by v0 compiler".into())
    }
    // Name paths retain an injective identity, not a lossy pretty-print.
    // Plain ASCII segments keep historical spelling for pinned primitives;
    // special UTF-8 strings use ~s<hex bytes>, numeric segments use ~n<nat>.
    unsafe fn name(x: Obj, depth: usize) -> Result<String, String> {
        if depth > 128 {
            return Err("name nesting limit".into());
        }
        match Self::tag(x)? {
            0 => Ok(String::new()),
            1 => {
                let parent = Self::name(Self::field(x, 0)?, depth + 1)?;
                let component = Self::string(Self::field(x, 1)?)?;
                let encoded = encode_name_str(&component)?;
                Ok(append_name_component(&parent, &encoded))
            }
            2 => {
                let parent = Self::name(Self::field(x, 0)?, depth + 1)?;
                let number = Self::nat(Self::field(x, 1)?)?;
                Ok(append_name_component(&parent, &format!("~n{number}")))
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
                if !ir_type_compatible(found, expected) {
                    return Err(format!("x_{id}: expected {expected}, got {found}"));
                }
                Ok(if is_value_type(found) {
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
            0 => Ok("f64"), // finite source-checked arithmetic, not float object semantics
            1 => Ok("u8"),
            2 => Ok("u16"),
            3 => Ok("u32"),
            4 => Ok("u64"),
            5 => Ok("usize"),
            7 => Ok("obj"),
            8 => Ok("tobj"),
            12 => Ok("tagged"),
            t => Err(format!(
                "IR type tag {t} unsupported (supported fixed integers and immutable values)"
            )),
        }
    }
    unsafe fn lit(x: Obj, ty: &str) -> Result<String, String> {
        match Self::checked_tag(x, "LitVal")? {
            0 => {
                // A decimal Nat constant in Lean.IR.LitVal.num can be an
                // unbounded runtime object. Preserve its exact source value.
                if matches!(ty, "obj" | "tobj") {
                    let value = Self::decimal_nat(Self::field(x, 0)?)?;
                    return Ok(format!("__LeanValue::nat_from_decimal(\"{value}\")"));
                }
                let n = Self::nat(Self::field(x, 0)?)?;
                if ty == "tagged" {
                    return Ok(format!("__LeanValue::tagged({n})"));
                }
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

    // Last-use analysis only permits moves through a straight-line tail.
    // Any join, branch, unknown expression, or reference bookkeeping for the
    // candidate is conservatively considered an additional use. This is a
    // performance optimization; it never extends accepted source semantics.
    unsafe fn arg_refs(x: Obj, id: usize) -> Result<bool, String> {
        Ok(match Self::checked_tag(x, "Arg")? {
            0 => Self::var(Self::field(x, 0)?)? == id,
            1 => false,
            _ => true,
        })
    }

    unsafe fn args_ref(args: Obj, id: usize) -> Result<bool, String> {
        for arg in Self::array(args)? {
            if Self::arg_refs(arg, id)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    unsafe fn expr_refs(x: Obj, id: usize) -> Result<bool, String> {
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

    unsafe fn straight_tail_unused(mut x: Obj, id: usize) -> Result<bool, String> {
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

    unsafe fn consumable_array(expr: Obj, tail: Obj) -> Result<Option<usize>, String> {
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
        Ok(Self::straight_tail_unused(tail, id)?.then_some(id))
    }

    unsafe fn expr(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
        functions: Option<&FunctionTable>,
        consumed_array: Option<usize>,
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
                        lowered.push(Self::arg(arg, env, ty)?);
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
    unsafe fn case_body(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> Result<(), String> {
        let type_name = Self::name(Self::field(x, 0)?, 0)?;
        match type_name.as_str() {
            "Option" | "List" | "Sum" | "tobj" | "obj" => {
                // The storage type may be erased to obj/tobj. Inspect the
                // actual source CtorInfo, never infer List from a numeric tag.
                let alts = Self::array(Self::field(x, 3)?)?;
                let mut family = None;
                for alt in alts {
                    if Self::checked_tag(alt, "Alt")? != 0 {
                        continue;
                    }
                    let info = Self::field(alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    family = Some(if name.starts_with("Option.") {
                        "Option"
                    } else if name.starts_with("List.") {
                        "List"
                    } else if name.starts_with("Sum.") {
                        "Sum"
                    } else {
                        if matches!(type_name.as_str(), "Option" | "List" | "Sum") {
                            return Err(format!(
                                "constructor {name} disagrees with source case family {type_name}"
                            ));
                        }
                        return Self::generic_object_case(x, code, depth, count, env, ret_ty, ctx);
                    });
                    break;
                }
                let family = family.ok_or("object case has no constructor identity")?;
                if matches!(type_name.as_str(), "Option" | "List" | "Sum") && type_name != family {
                    return Err(format!(
                        "object case source family {family} contradicts storage type {type_name}"
                    ));
                }
                Self::immutable_case(
                    x,
                    code,
                    depth,
                    count,
                    env,
                    ret_ty,
                    ImmutableCaseContext {
                        lowering: ctx,
                        family,
                    },
                )
            }
            _ => {
                let alts = Self::array(Self::field(x, 3)?)?;
                let mut has_bool_constructor = false;
                for alt in alts {
                    if Self::checked_tag(alt, "Alt")? == 0 {
                        let name = Self::name(Self::field(Self::field(alt, 0)?, 0)?, 0)?;
                        has_bool_constructor = name == "Bool.false" || name == "Bool.true";
                        break;
                    }
                }
                if has_bool_constructor {
                    if type_name != "UInt8" {
                        return Err("Bool constructor has unexpected IR storage type".into());
                    }
                    Self::boolean_case(x, code, depth, count, env, ret_ty, ctx)
                } else if is_value_type(Self::ty(Self::field(x, 2)?)?) {
                    Self::generic_object_case(x, code, depth, count, env, ret_ty, ctx)
                } else {
                    Self::scalar_enum_case(x, code, depth, count, env, ret_ty, ctx)
                }
            }
        }
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
        let repr = match Self::checked_tag(Self::field(x, 2)?, "IRType")? {
            1 => "u8",
            12 => return Err("object-tagged enum requires a typed object case adapter".into()),
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
            match Self::checked_tag(alt, "Alt")? {
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

    unsafe fn immutable_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        scoped: ImmutableCaseContext<'_>,
    ) -> Result<(), String> {
        let family = scoped.family;
        let ctx = scoped.lowering;
        if !is_value_type(Self::ty(Self::field(x, 2)?)?) {
            return Err(format!("{family} case scrutinee must be object-valued"));
        }
        let id = Self::var(Self::field(x, 1)?)?;
        if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
            return Err(format!("{family} case scrutinee is not object-valued"));
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.len() != 2 {
            return Err(format!(
                "{family} case requires exactly two constructor alternatives"
            ));
        }
        // A pinned two-constructor Option/List may have one source Alt.default.
        // Only the *other* source-checked constructor identity is admissible.
        let mut named_index = None;
        let mut defaults = 0usize;
        for alt in &alts {
            match Self::checked_tag(*alt, "Alt")? {
                0 => {
                    let info = Self::field(*alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    let idx = Self::nat(Self::field(info, 1)?)?;
                    immutable_case_ctor(family, idx, &name)?;
                    named_index = Some(idx);
                }
                1 => defaults += 1,
                _ => unreachable!(),
            }
        }
        if defaults > 1 || (defaults == 1 && named_index.is_none()) {
            return Err(format!("{family} case has unverified default alternatives"));
        }
        let missing_index = if defaults == 1 {
            Some(1 - named_index.unwrap())
        } else {
            None
        };
        let mut seen = [false; 2];
        writeln!(code, "    match x_{id}.tag() {{").unwrap();
        for alt in alts {
            let is_default = Self::checked_tag(alt, "Alt")? == 1;
            let (name, idx) = if is_default {
                let idx = missing_index.ok_or("unexpected default case alternative")?;
                let name = match (family, idx) {
                    ("Option", 0) => "Option.none",
                    ("Option", 1) => "Option.some",
                    ("List", 0) => "List.nil",
                    ("List", 1) => "List.cons",
                    _ => return Err(format!("{family} default case has unknown source layout")),
                };
                (name.to_owned(), idx)
            } else {
                let info = Self::field(alt, 0)?;
                (
                    Self::name(Self::field(info, 0)?, 0)?,
                    Self::nat(Self::field(info, 1)?)?,
                )
            };
            let expected_pointers = immutable_case_ctor(family, idx, &name)?;
            if seen[idx] {
                return Err(format!(
                    "duplicate {family} case constructor {name} at tag {idx}"
                ));
            }
            if !is_default {
                let info = Self::field(alt, 0)?;
                let pointer_fields = Self::nat(Self::field(info, 2)?)?;
                let usize_fields = Self::nat(Self::field(info, 3)?)?;
                let scalar_bytes = Self::nat(Self::field(info, 4)?)?;
                if pointer_fields != expected_pointers || usize_fields != 0 || scalar_bytes != 0 {
                    return Err(format!(
                        "{family} alternative {name} has unsupported field layout"
                    ));
                }
            }
            seen[idx] = true;
            writeln!(code, "        {idx} => {{").unwrap();
            if idx == 0 {
                if family == "List" {
                    writeln!(
                        code,
                        "            assert!(x_{id}.list_is_nil(), \"invalid List.nil representation\");"
                    )
                    .unwrap();
                } else if family == "Sum" {
                    writeln!(code, "            assert!(x_{id}.has_ctor(0, \"Sum.inl\", 1), \"invalid Sum.inl representation\");").unwrap();
                } else {
                    writeln!(
                        code,
                        "            assert!(x_{id}.has_tagged(0), \"invalid Option.none representation\");"
                    )
                    .unwrap();
                }
            } else if family == "List" {
                writeln!(
                    code,
                    "            assert!(x_{id}.list_is_cons(), \"invalid List.cons representation\");"
                )
                .unwrap();
            } else if family == "Sum" {
                writeln!(code, "            assert!(x_{id}.has_ctor(1, \"Sum.inr\", 1), \"invalid Sum.inr representation\");").unwrap();
            } else {
                writeln!(
                    code,
                    "            assert!(x_{id}.has_ctor(1, \"Option.some\", 1), \"invalid Option.some representation\");"
                )
                .unwrap();
            }
            let mut arm_env = env.clone();
            Self::body(
                Self::field(alt, if is_default { 0 } else { 1 })?,
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
            return Err(format!("incomplete {family} case"));
        }
        writeln!(code, "        _ => unreachable!(\"invalid {family} tag\"),").unwrap();
        writeln!(code, "    }}").unwrap();
        Ok(())
    }

    // A user inductive is accepted only through the actual Lean 4.34.1
    // constructor metadata. The family is source-derived and must agree for
    // every explicit arm; pointer and packed-scalar layouts cannot be mixed.
    unsafe fn generic_object_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> Result<(), String> {
        if !is_value_type(Self::ty(Self::field(x, 2)?)?) {
            return Err("user inductive case requires object-valued storage".into());
        }
        let id = Self::var(Self::field(x, 1)?)?;
        if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
            return Err("user inductive scrutinee is not object-valued".into());
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.is_empty() || alts.len() > 256 {
            return Err("user inductive alternatives exceed reviewed bounds".into());
        }
        let mut family: Option<String> = None;
        let mut seen = BTreeSet::new();
        let mut default = false;
        writeln!(code, "    match x_{id}.tag() {{").unwrap();
        for (position, alt) in alts.iter().enumerate() {
            match Self::checked_tag(*alt, "Alt")? {
                0 => {
                    if default {
                        return Err("constructor alternative after default".into());
                    }
                    let info = Self::field(*alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    let (parent, _) = name
                        .rsplit_once('.')
                        .ok_or_else(|| format!("constructor {name} has no family identity"))?;
                    if family.as_deref().is_some_and(|f| f != parent) {
                        return Err(format!("mixed user inductive families: {name}"));
                    }
                    family = Some(parent.to_owned());
                    let tag = Self::nat(Self::field(info, 1)?)?;
                    let pointers = Self::nat(Self::field(info, 2)?)?;
                    let usize_fields = Self::nat(Self::field(info, 3)?)?;
                    let scalar_bytes = Self::nat(Self::field(info, 4)?)?;
                    if tag >= 256
                        || pointers > 1024
                        || usize_fields != 0
                        || scalar_bytes != 0
                        || !seen.insert(tag)
                    {
                        return Err(format!(
                            "unsupported or duplicate constructor layout: {name}"
                        ));
                    }
                    writeln!(code, "        {tag} => {{").unwrap();
                    if pointers == 0 {
                        writeln!(code, "            assert!(x_{id}.has_tagged({tag}), \"invalid nullary constructor representation\");").unwrap();
                    } else {
                        writeln!(code, "            assert!(x_{id}.has_ctor({tag}, \"{name}\", {pointers}), \"invalid object constructor representation\");").unwrap();
                    }
                    let mut local = env.clone();
                    Self::body(
                        Self::field(*alt, 1)?,
                        code,
                        depth + 1,
                        count,
                        &mut local,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "        }}").unwrap();
                }
                1 => {
                    if default || position + 1 != alts.len() || family.is_none() {
                        return Err(
                            "user inductive default must be unique, last, and source-bound".into(),
                        );
                    }
                    default = true;
                    writeln!(code, "        _ => {{").unwrap();
                    let mut local = env.clone();
                    Self::body(
                        Self::field(*alt, 0)?,
                        code,
                        depth + 1,
                        count,
                        &mut local,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "        }}").unwrap();
                }
                t => return Err(format!("unknown user inductive alternative {t}")),
            }
        }
        if family.is_none() {
            return Err("user inductive lacks explicit constructor identity".into());
        }
        if !default {
            writeln!(
                code,
                "        _ => unreachable!(\"invalid Lean constructor tag\"),"
            )
            .unwrap();
        }
        writeln!(code, "    }}").unwrap();
        Ok(())
    }

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
            match Self::checked_tag(x, "FnBody")? {
                0 => {
                    // vdecl(x, ty, expr, body)
                    let name = Self::var(Self::field(x, 0)?)?;
                    let ty = Self::ty(Self::field(x, 1)?)?;
                    let expr = Self::field(x, 2)?;
                    // A lexical join or nested control-flow arm may capture
                    // this variable. Only top-level straight-line tails can
                    // transfer ownership to the Rc array fast path.
                    let consumed_array = if depth == 0 && ctx.joins.is_empty() {
                        Self::consumable_array(expr, Self::field(x, 3)?)?
                    } else {
                        None
                    };
                    let value = Self::expr(expr, ty, env, ctx.functions, consumed_array)?;
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
    unsafe fn emit(decl: Obj, rust_name: Obj) -> Result<String, String> {
        if lr_abi_probe() == 0 {
            return Err("Lean C ABI runtime probe failed".into());
        }
        let declaration = Self::name(Self::field(decl, 0)?, 0)?;
        let generated = Self::emit_function(decl, &Self::string(rust_name)?, None)
            .map_err(|reason| format!("declaration={declaration}; {reason}"))?;
        include_value_runtime(generated)
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
        // Preserve the explicit terminal forms from Lean IR, including in
        // nested join and branch bodies. This is intentional generated code.
        result.push_str("#[allow(clippy::needless_return)]\n");
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
            write!(result, "x_{var}: {}", rust_type(ty)).unwrap();
        }
        writeln!(result, ") -> {} {{", rust_type(ret)).unwrap();
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

// The path separators cannot occur inside a canonical component: plain
// ASCII components exclude '.', '~'; special strings and Nat segments use
// disjoint prefixed encodings. The original Lean.Name object crosses FFI.
fn append_name_component(parent: &str, component: &str) -> String {
    if parent.is_empty() {
        component.to_owned()
    } else {
        format!("{parent}.{component}")
    }
}

fn encode_name_str(component: &str) -> Result<String, String> {
    if component.len() > 4096 {
        return Err("Lean.Name string component exceeds safety cap".into());
    }
    if !component.is_empty()
        && !component.as_bytes()[0].is_ascii_digit()
        && component
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'!')
    {
        return Ok(component.to_owned());
    }
    let mut encoded = String::from("~s");
    for byte in component.as_bytes() {
        write!(&mut encoded, "{byte:02x}").unwrap();
    }
    Ok(encoded)
}

// Emitted Rust function names remain injective for all canonical Lean paths.
// Naming is injective over UTF-8 bytes and independent of declaration ordering.
fn internal_closure_name(lean_name: &str) -> String {
    format!("__pap_{}", internal_name(lean_name))
}

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
        while let Some(body) = pending.pop() {
            count += 1;
            if count > 100_000 {
                return Err("dependency IR traversal exceeded 100000 instructions".into());
            }
            match Self::checked_tag(body, "FnBody")? {
                0 => {
                    let expr = Self::field(body, 2)?;
                    if matches!(Self::checked_tag(expr, "Expr")?, 6 | 7) {
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
                        match Self::checked_tag(alt, "Alt")? {
                            0 => pending.push(Self::field(alt, 1)?),
                            1 => pending.push(Self::field(alt, 0)?),
                            t => return Err(format!("unknown alternative constructor {t}")),
                        }
                    }
                }
                2 => pending.push(Self::field(body, 3)?),
                5 => pending.push(Self::field(body, 5)?),
                6 | 7 => pending.push(Self::field(body, 2)?),
                8 => pending.push(Self::field(body, 1)?),
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
        let root = Self::name(root, 0)?;
        let public_name = Self::string(public_name)?;
        Self::emit_roots(decls, vec![(root, public_name)])
    }

    unsafe fn emit_module_many(decls: Obj, roots: Obj) -> Result<String, String> {
        let mut public_roots = Vec::new();
        for item in Self::array(roots)? {
            let root = Self::name(item, 0)?;
            // In v1 we expose the final Lean identifier as the Rust public API.
            // Any collisions (e.g. Foo.run and Bar.run) must refuse.
            let public = root.rsplit('.').next().unwrap_or("").to_owned();
            public_roots.push((root, public));
        }
        Self::emit_roots(decls, public_roots)
    }

    unsafe fn emit_roots(decls: Obj, roots: Vec<(String, String)>) -> Result<String, String> {
        if lr_abi_probe() == 0 {
            return Err("Lean C ABI runtime probe failed".into());
        }
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
        // Only callable object ABI declarations receive generated thunks.
        // No raw address is ever read out of a Lean or Rust heap object.
        for (name, sig) in &signatures {
            if sig.params.is_empty()
                || !sig.params.iter().all(|ty| is_value_type(ty))
                || !is_value_type(sig.result)
            {
                continue;
            }
            result.push_str("#[allow(dead_code)]\n");
            writeln!(
                result,
                "fn {}(args: Vec<__LeanValue>) -> __LeanValue {{",
                internal_closure_name(name)
            )
            .unwrap();
            writeln!(result, "    assert_eq!(args.len(), {});", sig.params.len()).unwrap();
            write!(result, "    {}(", internal_name(name)).unwrap();
            for i in 0..sig.params.len() {
                if i > 0 {
                    result.push_str(", ");
                }
                write!(result, "args[{i}].clone()").unwrap();
            }
            result.push_str(")\n}\n");
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
            // Preserve the original Lean root name as the public API; Rust's
            // naming lint must not force an observable symbol rename.
            result.push_str("#[allow(non_snake_case)]\n");
            write!(result, "pub fn {public_name}(").unwrap();
            for (i, ty) in sig.params.iter().enumerate() {
                if i > 0 {
                    result.push_str(", ");
                }
                write!(result, "p_{i}: {}", rust_type(ty)).unwrap();
            }
            write!(
                result,
                ") -> {} {{\n    {}(",
                rust_type(sig.result),
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
        include_value_runtime(result)
    }
}

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

// The supported Nat runtime is explicit, with no fallback to host arithmetic.
// Both dependency discovery and native codegen consult this exact whitelist.
fn is_nat_primitive(name: &str) -> bool {
    matches!(
        name,
        "Nat.add"
            | "Nat.sub"
            | "Nat.mul"
            | "Nat.div"
            | "Nat.mod"
            | "Nat.decEq"
            | "Nat.decLt"
            | "Nat.decLe"
    )
}

fn is_primitive(name: &str) -> bool {
    primitive_spec(name).is_some()
        || is_nat_primitive(name)
        || runtime_primitive_spec(name).is_some()
        || matches!(
            name,
            "Array.mkEmpty" | "Array.getInternal" | "Array.getInternalBorrowed" | "Array.set!"
        )
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

unsafe fn reply_module_many(decls: Obj, roots: Obj) -> *mut c_void {
    let text = match std::panic::catch_unwind(|| Reader::emit_module_many(decls, roots)) {
        Ok(Ok(s)) => format!("OK\n{s}"),
        Ok(Err(e)) => safety::refusal("requested-root", &e),
        Err(_) => safety::refusal("requested-root", "backend panic (no code emitted)"),
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
    use super::{
        append_name_component, encode_name_str, immutable_case_ctor, internal_name, RUNTIME_SOURCE,
        SUPPORTED_IR_TAGS,
    };
    #[test]
    fn list_and_option_cases_require_source_constructor_identity_and_layout() {
        assert_eq!(immutable_case_ctor("Option", 0, "Option.none").unwrap(), 0);
        assert_eq!(immutable_case_ctor("Option", 1, "Option.some").unwrap(), 1);
        assert_eq!(immutable_case_ctor("List", 0, "List.nil").unwrap(), 0);
        assert_eq!(immutable_case_ctor("List", 1, "List.cons").unwrap(), 2);
        assert_eq!(immutable_case_ctor("Sum", 0, "Sum.inl").unwrap(), 1);
        assert_eq!(immutable_case_ctor("Sum", 1, "Sum.inr").unwrap(), 1);
        for (family, index, name) in [
            ("Option", 0, "List.nil"),
            ("Option", 1, "List.cons"),
            ("List", 0, "Option.none"),
            ("List", 1, "Option.some"),
            ("List", 0, "Sum.inl"),
            ("List", 2, "List.cons"),
        ] {
            let err = immutable_case_ctor(family, index, name).unwrap_err();
            assert!(err.contains("unsupported"));
            assert!(err.contains(name));
        }
    }

    #[test]
    fn one_generated_value_abi_for_nat_objects_and_closures() {
        assert_eq!(RUNTIME_SOURCE.matches("pub struct __LeanValue(").count(), 1);
        assert_eq!(RUNTIME_SOURCE.matches("enum __LeanValueRepr").count(), 1);
        assert!(RUNTIME_SOURCE.contains("std::rc::Rc<__LeanValueRepr>"));
        assert!(RUNTIME_SOURCE.contains("__LeanBigNat"));
        assert!(RUNTIME_SOURCE.contains("Closure {"));
        assert!(RUNTIME_SOURCE.contains("fn pap("));
        assert!(RUNTIME_SOURCE.contains("fn apply("));
        assert_eq!(RUNTIME_SOURCE.matches("fn is_shared(").count(), 1);
        assert!(!RUNTIME_SOURCE.contains("fn mutate"));
    }

    #[test]
    fn closure_symbol_mangling_is_injective_on_ascii_names() {
        assert_ne!(internal_name("X.ab"), internal_name("X.a_b"));
        assert_ne!(internal_name("X.A"), internal_name("X.a"));
        assert!(internal_name("X.a").starts_with("lean_"));
    }
    #[test]
    fn structured_name_identity_is_injective() {
        assert_eq!(encode_name_str("Sched").unwrap(), "Sched");
        assert_eq!(encode_name_str("argLeastLoad").unwrap(), "argLeastLoad");
        assert_eq!(encode_name_str("a.b").unwrap(), "~s612e62");
        assert_eq!(encode_name_str("1").unwrap(), "~s31");
        assert_eq!(encode_name_str("").unwrap(), "~s");
        assert_eq!(encode_name_str("a\u{0}b").unwrap(), "~s610062");
        assert_ne!(encode_name_str("~n9").unwrap(), "~n9");
        assert_ne!(
            append_name_component("X", &encode_name_str("a.b").unwrap()),
            append_name_component("X.a", "b")
        );
        assert_ne!(
            append_name_component("X", "~n9"),
            append_name_component("X", "~s39")
        );
        assert!(encode_name_str(&"x".repeat(4097)).is_err());
    }

    #[test]
    fn supplemental_value_registry_has_no_second_nat_implementation() {
        let registry = super::RUNTIME_PRIMITIVE_REGISTRY;
        let expected = [
            "Int.add",
            "String.append",
            "String.utf8ByteSize",
            "String.length",
            "Array.push",
            "Array.size",
            "List.reverse._redArg",
        ];
        let mut seen = std::collections::BTreeSet::new();
        for line in registry
            .lines()
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
        {
            let fields: Vec<_> = line.split('\t').collect();
            assert_eq!(fields.len(), 3, "malformed adapter registry");
            assert!(seen.insert(fields[0]), "duplicate primitive {}", fields[0]);
            assert!(super::runtime_primitive_spec(fields[0]).is_some());
            assert!(super::RUNTIME_SOURCE.contains(&format!("fn {}(", fields[1])));
            assert!(!fields[0].starts_with("Nat."), "Nat must use mainline GMP");
        }
        assert_eq!(seen, expected.into_iter().collect());
        assert!(super::is_nat_primitive("Nat.add"));
        assert!(super::is_nat_primitive("Nat.div"));
    }

    #[test]
    fn permitted_rust_identacters_only() {
        for s in ["a", "a_1", "Fn2"] {
            assert!(s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'));
        }
    }
    #[test]
    fn constructor_whitelist_preserves_scoped_join_support() {
        assert!(SUPPORTED_IR_TAGS.contains(&("Decl", 0)));
        assert!(!SUPPORTED_IR_TAGS.contains(&("Decl", 1)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 6)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 11)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 7)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 8)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 0)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 3)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Expr", 5)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 5)));
        assert!(!SUPPORTED_IR_TAGS.contains(&("Expr", 1)));
        assert!(SUPPORTED_IR_TAGS.contains(&("IRType", 7)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 6)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 1)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 11)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 9)));
        assert!(SUPPORTED_IR_TAGS.contains(&("IRType", 0)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Alt", 1)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 2)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Arg", 1)));
        assert_eq!(SUPPORTED_IR_TAGS.len(), 35);
    }

    #[test]
    fn primitive_registry_is_complete_and_unambiguous() {
        use super::{primitive_spec, PRIMITIVE_REGISTRY};
        use std::collections::BTreeSet;
        let mut seen = BTreeSet::new();
        for line in PRIMITIVE_REGISTRY
            .lines()
            .filter(|s| !s.starts_with('#') && !s.is_empty())
        {
            let cells: Vec<_> = line.split('\t').collect();
            assert_eq!(cells.len(), 4);
            assert!(seen.insert(cells[0]));
            assert!(primitive_spec(cells[0]).is_some());
        }
        assert_eq!(seen.len(), 68);
        assert!(primitive_spec("UInt64.add").is_some());
        assert!(primitive_spec("USize.decLe").is_some());
        assert!(primitive_spec("Float.mul").is_some());
        assert!(primitive_spec("UInt64.shiftRight").is_some());
        assert!(primitive_spec("Int.add").is_none());
    }
}
