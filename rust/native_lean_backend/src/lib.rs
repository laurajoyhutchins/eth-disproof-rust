//! An in-process, strict Lean 4.34.1 IR -> Rust code emitter.
//!
//! This entry point receives `Lean.IR.Decl` *directly* as a borrowed Lean object.
//! It does not serialize or clone the IR. Only an explicitly accepted subset is
//! lowered; unknown instructions and types are errors, never substitutions.
use std::collections::BTreeMap;
use std::ffi::{c_char, c_void, CStr, CString};

mod names;
mod primitives;
mod reader;
mod safety;

use names::{append_name_component, encode_name_str, internal_name};
#[cfg(test)]
use primitives::{
    is_nat_primitive, primitive_spec, runtime_primitive_spec, PRIMITIVE_REGISTRY,
    RUNTIME_PRIMITIVE_REGISTRY,
};
use reader::Reader;

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
    fn lr_param_borrow(x: Obj) -> i32;
    fn lr_rc_flags(x: Obj) -> i32;
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
// Rc retains aliases for the bounded accepted value subset. Ownership-
// observable programs still require Lean/Rust cross-call conformance.
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
    fn array_size_uses_exact_tagged_nat_without_gmp_allocation() {
        let input = __LeanValue::array(vec![
            __LeanValue::tagged(11),
            __LeanValue::tagged(13),
            __LeanValue::tagged(17),
        ]);
        let size = input.array_size();
        assert!(size.has_tagged(3), "small array size must be a tagged Nat");
        assert_eq!(size.tagged_nat(), 3);
        assert_eq!(size.nat_to_decimal(), "3");
        assert_eq!(size, __LeanValue::nat_from_decimal("3"));
        assert_eq!(__LeanValue::nat_from_decimal("3"), size);
        let zero = __LeanValue::array(Vec::new()).array_size();
        assert_eq!(zero.tagged_nat(), 0);
        assert_eq!(zero, __LeanValue::nat_from_decimal("0"));
        assert_ne!(zero, __LeanValue::nat_from_decimal("1"));
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

const CLOSURE_INLINE_TEST_SOURCE: &str = r#"
#[cfg(test)]
mod __lean_closure_inline_tests {
    use super::{__LeanValue, __LeanValueRepr};

    fn plus(a: __LeanValue, b: __LeanValue) -> __LeanValue {
        __LeanValue::boxed_u64(a.unbox_u64().wrapping_add(b.unbox_u64()))
    }

    fn ternary(a: __LeanValue, b: __LeanValue, c: __LeanValue) -> __LeanValue {
        __LeanValue::boxed_u64(
            a.unbox_u64().wrapping_add(b.unbox_u64()).wrapping_add(c.unbox_u64())
        )
    }

    fn triple(args: Vec<__LeanValue>) -> __LeanValue {
        assert_eq!(args.len(), 3);
        __LeanValue::boxed_u64(
            args[0].unbox_u64()
                .wrapping_add(args[1].unbox_u64())
                .wrapping_add(args[2].unbox_u64())
        )
    }

    #[test]
    fn binary_pap_is_one_heap_object_without_capture_vec() {
        let f = __LeanValue::pap2(plus, __LeanValue::boxed_u64(11));
        assert!(matches!(f.0.as_ref(), __LeanValueRepr::Closure2 { .. }));
        assert_eq!(f.apply1(__LeanValue::boxed_u64(5)).unbox_u64(), 16);
        assert_eq!(f.apply1(__LeanValue::boxed_u64(7)).unbox_u64(), 18);
    }

    #[test]
    fn owned_last_use_moves_capture_but_shared_alias_remains_callable() {
        let unique = __LeanValue::pap2(plus, __LeanValue::boxed_u64(17));
        assert_eq!(unique.apply1_owned(__LeanValue::boxed_u64(2)).unbox_u64(), 19);
        let shared = __LeanValue::pap2(plus, __LeanValue::boxed_u64(20));
        let alias = shared.clone();
        assert_eq!(shared.apply1_owned(__LeanValue::boxed_u64(3)).unbox_u64(), 23);
        assert_eq!(alias.apply1(__LeanValue::boxed_u64(4)).unbox_u64(), 24);
        assert_eq!(alias.apply1_owned(__LeanValue::boxed_u64(5)).unbox_u64(), 25);
    }

    #[test]
    fn two_inline_captures_remain_ordered_and_alias_safe() {
        let original = __LeanValue::pap3(
            ternary, __LeanValue::boxed_u64(10), __LeanValue::boxed_u64(20)
        );
        assert!(matches!(original.0.as_ref(), __LeanValueRepr::Closure3 { .. }));
        assert_eq!(original.apply1(__LeanValue::boxed_u64(3)).unbox_u64(), 33);
        let alias = original.clone();
        assert_eq!(original.apply1_owned(__LeanValue::boxed_u64(5)).unbox_u64(), 35);
        assert_eq!(alias.apply1_owned(__LeanValue::boxed_u64(7)).unbox_u64(), 37);
        let unique = __LeanValue::pap3(
            ternary, __LeanValue::boxed_u64(1), __LeanValue::boxed_u64(2)
        );
        assert_eq!(unique.apply1_owned(__LeanValue::boxed_u64(3)).unbox_u64(), 6);
    }

    #[test]
    fn general_closure_partial_application_remains_source_ordered() {
        let base = __LeanValue::pap(triple, 3, vec![__LeanValue::boxed_u64(1)]);
        let partial = base.apply1(__LeanValue::boxed_u64(2));
        assert_eq!(partial.apply1_owned(__LeanValue::boxed_u64(3)).unbox_u64(), 6);
        assert_eq!(base.apply(vec![
            __LeanValue::boxed_u64(7), __LeanValue::boxed_u64(9)
        ]).unbox_u64(), 17);
    }

    #[test]
    #[should_panic(expected = "oversaturated binary source PAP")]
    fn specialized_closure_refuses_oversaturation() {
        let f = __LeanValue::pap2(plus, __LeanValue::boxed_u64(1));
        let _ = f.apply(vec![__LeanValue::boxed_u64(2), __LeanValue::boxed_u64(3)]);
    }
}
"#;

// Embedded at the end of generated code; tests must follow emitted declarations.
const ERASED_JOIN_TEST_SOURCE: &str = r#"
#[cfg(test)]
mod erased_join_safety_tests {
    use super::__LeanValue;

    #[test]
    #[should_panic(expected = "erased join value was read")]
    fn erased_constructor_predicate_refuses() {
        assert!(!__LeanValue::erased().has_ctor(0, "Unit", 0));
    }

    #[test]
    #[should_panic(expected = "erased join value was read")]
    fn erased_tagged_predicate_refuses() {
        assert!(!__LeanValue::erased().has_tagged(0));
    }

    #[test]
    #[should_panic(expected = "erased join value was read")]
    fn erased_equality_refuses() {
        assert_ne!(__LeanValue::erased(), __LeanValue::tagged(0));
    }

    #[test]
    #[should_panic(expected = "isShared requires a heap-backed Lean value")]
    fn tagged_immediate_sharedness_refuses() {
        let _ = __LeanValue::tagged(0).is_shared();
    }
}

"#;

// These tests intentionally distinguish compiler-internal Rust Rc aliases
// from source-program RC instructions. They do not claim equivalence for
// every Lean heap representation or indirect control-flow path.
const SOURCE_RC_TEST_SOURCE: &str = r#"
#[cfg(test)]
mod source_reference_count_tests {
    use super::__LeanValue;

    #[test]
    fn compiler_clones_do_not_change_source_exclusivity() {
        let x = __LeanValue::ctor(1, "Cell", vec![__LeanValue::tagged(2)]);
        let transient = x.clone();
        assert_eq!(x.is_shared(), 0);
        x.source_inc(1, true, false);
        assert_eq!(x.is_shared(), 1);
        assert_eq!(transient.is_shared(), 1);
        x.source_dec(1, true, false);
        assert_eq!(x.is_shared(), 0);
    }

    #[test]
    fn source_increment_delta_and_persistence() {
        let x = __LeanValue::array(Vec::new());
        x.source_inc(3, true, false);
        assert_eq!(x.1.get(), 4);
        x.source_inc(42, false, true);
        x.source_dec(1, true, true);
        assert_eq!(x.1.get(), 4);
        for _ in 0..3 { x.source_dec(1, true, false); }
        assert_eq!(x.is_shared(), 0);
    }

    #[test]
    fn source_decrement_releases_owned_child_references() {
        let child = __LeanValue::string("retained");
        child.source_inc(1, true, false);
        let parent = __LeanValue::ctor(1, "Parent", vec![child.clone()]);
        parent.source_dec(1, true, false);
        assert_eq!(parent.1.get(), 0);
        assert_eq!(child.1.get(), 1);
        assert_eq!(child.is_shared(), 0);
    }

    #[test]
    fn source_del_releases_only_shell_not_transferred_fields() {
        let child = __LeanValue::string("moved");
        let parent = __LeanValue::ctor(1, "Parent", vec![child.clone()]);
        parent.source_del();
        assert_eq!(parent.1.get(), 0);
        assert_eq!(child.1.get(), 1);
        assert_eq!(child.is_shared(), 0);
    }

    #[test]
    fn checked_immediate_refcount_events_are_noops() {
        let x = __LeanValue::tagged(17);
        x.source_inc(3, true, false);
        x.source_dec(1, true, false);
        assert_eq!(x.tagged_nat(), 17);
    }

    #[test]
    #[should_panic(expected = "source reference-count overflow")]
    fn source_increment_overflow_refuses() {
        let x = __LeanValue::array(Vec::new());
        x.source_inc(usize::MAX, true, false);
    }

    #[test]
    #[should_panic(expected = "source inc on released object")]
    fn source_use_after_release_refuses() {
        let x = __LeanValue::string("gone");
        x.source_dec(1, true, false);
        x.source_inc(1, true, false);
    }

    #[test]
    #[should_panic(expected = "source del requires unique object")]
    fn source_del_shared_refuses() {
        let x = __LeanValue::array(Vec::new());
        x.source_inc(1, true, false);
        x.source_del();
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
        let closure_tests =
            if source.contains("__LeanValue::pap2(") || source.contains("__LeanValue::pap3(") {
                CLOSURE_INLINE_TEST_SOURCE
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
        format!("{RUNTIME_SOURCE}\n{source}\n{tests}\n{closure_tests}\n{set_tests}\n{ERASED_JOIN_TEST_SOURCE}\n{heap_join_tests}\n{SOURCE_RC_TEST_SOURCE}")
    } else {
        source
    };
    if code.len() > safety::MAX_OUTPUT_BYTES {
        return Err("complete standalone Rust source exceeds maximum output bytes".into());
    }
    Ok(code)
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
        assert!(RUNTIME_SOURCE.contains("Closure2 {"));
        assert!(RUNTIME_SOURCE.contains("fn pap2("));
        assert!(RUNTIME_SOURCE.contains("fn pap3("));
        assert!(RUNTIME_SOURCE.contains("fn apply1("));
        assert!(RUNTIME_SOURCE.contains("fn apply1_owned("));
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
