//! An in-process, strict Lean 4.34.1 IR -> Rust code emitter.
//!
//! This entry point receives `Lean.IR.Decl` *directly* as a borrowed Lean object.
//! It does not serialize or clone the IR. Only an explicitly accepted subset is
//! lowered; unknown instructions and types are errors, never substitutions.
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{c_char, c_void, CString};
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

// Standalone immutable object model for the supported Lean IR subset.
// Rc cloning models shared immutable values; source inc/dec instructions are
// redundant only while mutation, isShared, reset and reuse remain unsupported.
const RUNTIME_SOURCE: &str = r#"
#[derive(Clone, Debug)]
pub struct __LeanValue(std::rc::Rc<__LeanValueRepr>);

#[derive(Debug)]
enum __LeanValueRepr {
    Tagged(usize),
    U8(u8), U16(u16), U32(u32), U64(u64), USize(usize),
    Ctor { tag: usize, name: &'static str, fields: Vec<__LeanValue> },
    // Immutable first-class functions, represented by a statically generated
    // object-argument thunk and an Rc-shared vector of captured values.
    Closure {
        arity: usize,
        captures: Vec<__LeanValue>,
        invoke: fn(Vec<__LeanValue>) -> __LeanValue,
    },
    Nat(__LeanBigNat),
}

// Nat is arbitrary precision in Lean. GMP is an established, maintained
// arithmetic library, linked into standalone generated Rust. The backend
// never truncates Nat to a machine-sized integer.
#[repr(C)]
#[derive(Debug)]
struct __LeanMpz {
    alloc: std::ffi::c_int,
    size: std::ffi::c_int,
    limbs: *mut std::ffi::c_ulong,
}

#[link(name = "gmp")]
unsafe extern "C" {
    #[link_name = "__gmpz_init"]
    fn __gmpz_init(value: *mut __LeanMpz);
    #[link_name = "__gmpz_clear"]
    fn __gmpz_clear(value: *mut __LeanMpz);
    #[link_name = "__gmpz_set_ui"]
    fn __gmpz_set_ui(value: *mut __LeanMpz, n: std::ffi::c_ulong);
    #[link_name = "__gmpz_set_str"]
    fn __gmpz_set_str(value: *mut __LeanMpz, text: *const std::ffi::c_char, base: std::ffi::c_int) -> std::ffi::c_int;
    #[link_name = "__gmpz_sizeinbase"]
    fn __gmpz_sizeinbase(value: *const __LeanMpz, base: std::ffi::c_int) -> usize;
    #[link_name = "__gmpz_get_str"]
    fn __gmpz_get_str(buffer: *mut std::ffi::c_char, base: std::ffi::c_int, value: *const __LeanMpz) -> *mut std::ffi::c_char;
    #[link_name = "__gmpz_add"]
    fn __gmpz_add(out: *mut __LeanMpz, a: *const __LeanMpz, b: *const __LeanMpz);
    #[link_name = "__gmpz_sub"]
    fn __gmpz_sub(out: *mut __LeanMpz, a: *const __LeanMpz, b: *const __LeanMpz);
    #[link_name = "__gmpz_mul"]
    fn __gmpz_mul(out: *mut __LeanMpz, a: *const __LeanMpz, b: *const __LeanMpz);
    #[link_name = "__gmpz_tdiv_q"]
    fn __gmpz_tdiv_q(out: *mut __LeanMpz, a: *const __LeanMpz, b: *const __LeanMpz);
    #[link_name = "__gmpz_tdiv_r"]
    fn __gmpz_tdiv_r(out: *mut __LeanMpz, a: *const __LeanMpz, b: *const __LeanMpz);
    #[link_name = "__gmpz_set"]
    fn __gmpz_set(out: *mut __LeanMpz, a: *const __LeanMpz);
    #[link_name = "__gmpz_cmp"]
    fn __gmpz_cmp(a: *const __LeanMpz, b: *const __LeanMpz) -> std::ffi::c_int;
}

#[derive(Debug)]
struct __LeanBigNat { value: __LeanMpz }

impl __LeanBigNat {
    fn zero() -> Self {
        // GMP initializes the owned representation in place.
        let mut value = std::mem::MaybeUninit::<__LeanMpz>::uninit();
        unsafe {
            __gmpz_init(value.as_mut_ptr());
            Self { value: value.assume_init() }
        }
    }
    fn ptr(&self) -> *const __LeanMpz { &self.value }
    fn from_usize(n: usize) -> Self {
        let mut value = Self::zero();
        unsafe { __gmpz_set_ui(&mut value.value, n as std::ffi::c_ulong); }
        value
    }
    fn from_decimal(text: &str) -> Self {
        assert!(!text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()), "invalid Nat decimal input");
        let cstr = std::ffi::CString::new(text).expect("decimal input has no NUL");
        let mut value = Self::zero();
        let rc = unsafe { __gmpz_set_str(&mut value.value, cstr.as_ptr(), 10) };
        assert_eq!(rc, 0, "invalid Nat decimal input");
        value
    }
    fn decimal(&self) -> String {
        let cap = unsafe { __gmpz_sizeinbase(self.ptr(), 10) }.checked_add(3).expect("Nat decimal output too large");
        let mut bytes = vec![0 as std::ffi::c_char; cap];
        unsafe {
            __gmpz_get_str(bytes.as_mut_ptr(), 10, self.ptr());
            std::ffi::CStr::from_ptr(bytes.as_ptr()).to_str().expect("GMP decimal UTF-8").to_owned()
        }
    }
    fn binary(lhs: &Self, rhs: &Self, op: &str) -> Self {
        let mut out = Self::zero();
        unsafe {
            match op {
                "add" => __gmpz_add(&mut out.value, lhs.ptr(), rhs.ptr()),
                "sub" => {
                    // Lean Nat.sub saturates at zero. GMP signed subtraction does not.
                    if __gmpz_cmp(lhs.ptr(), rhs.ptr()) >= 0 {
                        __gmpz_sub(&mut out.value, lhs.ptr(), rhs.ptr());
                    }
                }
                "mul" => __gmpz_mul(&mut out.value, lhs.ptr(), rhs.ptr()),
                "div" | "mod" => {
                    // Lean totalizes division by zero: x / 0 = 0, x % 0 = x.
                    if __gmpz_cmp(rhs.ptr(), out.ptr()) == 0 {
                        if op == "mod" { __gmpz_set(&mut out.value, lhs.ptr()); }
                    } else if op == "div" {
                        __gmpz_tdiv_q(&mut out.value, lhs.ptr(), rhs.ptr());
                    } else {
                        __gmpz_tdiv_r(&mut out.value, lhs.ptr(), rhs.ptr());
                    }
                }
                _ => unreachable!("unrecognized Nat primitive"),
            }
        }
        out
    }
}
impl Drop for __LeanBigNat {
    fn drop(&mut self) { unsafe { __gmpz_clear(&mut self.value); } }
}

enum __LeanNatOperand<'a> {
    Borrowed(&'a __LeanBigNat),
    Temporary(__LeanBigNat),
}
impl __LeanNatOperand<'_> {
    fn as_ref(&self) -> &__LeanBigNat {
        match self {
            Self::Borrowed(v) => v,
            Self::Temporary(v) => v,
        }
    }
}

#[allow(dead_code)]
impl __LeanValue {
    fn tagged(v: usize) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::Tagged(v))) }
    fn boxed_u8(v: u8) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U8(v))) }
    fn boxed_u16(v: u16) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U16(v))) }
    fn boxed_u32(v: u32) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U32(v))) }
    fn boxed_u64(v: u64) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U64(v))) }
    fn boxed_usize(v: usize) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::USize(v))) }
    pub fn nat_from_decimal(value: &str) -> Self {
        Self(std::rc::Rc::new(__LeanValueRepr::Nat(__LeanBigNat::from_decimal(value))))
    }
    pub fn nat_to_decimal(&self) -> String {
        self.nat_operand().as_ref().decimal()
    }
    fn nat_operand(&self) -> __LeanNatOperand<'_> {
        match self.0.as_ref() {
            __LeanValueRepr::Tagged(value) => __LeanNatOperand::Temporary(__LeanBigNat::from_usize(*value)),
            __LeanValueRepr::Nat(value) => __LeanNatOperand::Borrowed(value),
            _ => panic!("Nat primitive received non-Nat object"),
        }
    }
    fn nat_binary(&self, other: &Self, operation: &str) -> Self {
        let lhs = self.nat_operand();
        let rhs = other.nat_operand();
        let result = __LeanBigNat::binary(lhs.as_ref(), rhs.as_ref(), operation);
        Self(std::rc::Rc::new(__LeanValueRepr::Nat(result)))
    }
    fn nat_cmp(&self, other: &Self) -> i32 {
        let lhs = self.nat_operand();
        let rhs = other.nat_operand();
        unsafe { __gmpz_cmp(lhs.as_ref().ptr(), rhs.as_ref().ptr()) }
    }
    fn ctor(tag: usize, name: &'static str, fields: Vec<Self>) -> Self {
        Self(std::rc::Rc::new(__LeanValueRepr::Ctor { tag, name, fields }))
    }
    fn tag(&self) -> usize {
        match self.0.as_ref() {
            __LeanValueRepr::Tagged(v) => *v,
            __LeanValueRepr::Ctor { tag, .. } => *tag,
            _ => panic!("tried to case-analyze a boxed scalar"),
        }
    }
    fn has_ctor(&self, tag: usize, name: &str, arity: usize) -> bool {
        matches!(self.0.as_ref(), __LeanValueRepr::Ctor {tag: t, name: n, fields}
            if *t == tag && *n == name && fields.len() == arity)
    }
    fn has_tagged(&self, value: usize) -> bool {
        matches!(self.0.as_ref(), __LeanValueRepr::Tagged(v) if *v == value)
    }
    fn field(&self, index: usize) -> Self {
        match self.0.as_ref() {
            __LeanValueRepr::Ctor { fields, .. } => fields.get(index).expect("constructor field absent").clone(),
            _ => panic!("projection from a non-constructor"),
        }
    }
    fn unbox_u8(&self) -> u8 { match self.0.as_ref() {__LeanValueRepr::U8(x) => *x, _ => panic!("incorrect boxed u8") } }
    fn unbox_u16(&self) -> u16 { match self.0.as_ref() {__LeanValueRepr::U16(x) => *x, _ => panic!("incorrect boxed u16") } }
    fn unbox_u32(&self) -> u32 { match self.0.as_ref() {__LeanValueRepr::U32(x) => *x, _ => panic!("incorrect boxed u32") } }
    fn unbox_u64(&self) -> u64 { match self.0.as_ref() {__LeanValueRepr::U64(x) => *x, _ => panic!("incorrect boxed u64") } }
    fn unbox_usize(&self) -> usize { match self.0.as_ref() {__LeanValueRepr::USize(x) => *x, _ => panic!("incorrect boxed usize") } }

    fn pap(invoke: fn(Vec<Self>) -> Self, arity: usize, captures: Vec<Self>) -> Self {
        assert!(arity > 0 && captures.len() < arity, "invalid source PAP arity");
        Self(std::rc::Rc::new(__LeanValueRepr::Closure { arity, captures, invoke }))
    }

    // Preserve declaration-order captures and permit additional partial
    // application. No mutation or runtime lookup of untrusted pointers.
    fn apply(&self, args: Vec<Self>) -> Self {
        match self.0.as_ref() {
            __LeanValueRepr::Closure { arity, captures, invoke } => {
                assert!(!args.is_empty(), "empty source AP");
                let mut all = captures.clone();
                all.extend(args);
                assert!(all.len() <= *arity, "oversaturated source AP");
                if all.len() == *arity {
                    invoke(all)
                } else {
                    Self::pap(*invoke, *arity, all)
                }
            }
            _ => panic!("tried to apply a non-function Lean value"),
        }
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

fn include_value_runtime(source: String) -> String {
    if source.contains("__LeanValue") {
        format!("{RUNTIME_SOURCE}\n{source}")
    } else {
        source
    }
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
    unsafe fn expr(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
        functions: Option<&FunctionTable>,
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
                            return Err("constructor with pointer/scalar layout is unsupported".into());
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
                if !matches!(name.as_str(), "Option.none" | "Option.some" | "Prod.mk") {
                    return Err(format!(
                        "constructor {name} is not in the verified runtime subset"
                    ));
                }
                let expected_arity = match name.as_str() {
                    "Option.none" => (0, 0),
                    "Option.some" => (1, 1),
                    "Prod.mk" => (0, 2),
                    _ => unreachable!(),
                };
                if (tag, fields.len()) != expected_arity
                    || size != fields.len()
                    || usize_count != 0
                    || ssize != 0
                {
                    return Err(format!("constructor {name} layout unsupported"));
                }
                if name == "Option.none" {
                    if var_ty != "tagged" {
                        return Err("Option.none must be tagged in pinned IR".into());
                    }
                    return Ok("__LeanValue::tagged(0)".into());
                }
                if var_ty != "obj" {
                    return Err("heap constructor has unexpected IR result type".into());
                }
                let mut args = Vec::new();
                for arg in fields {
                    args.push(Self::arg(arg, env, "tobj")?);
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
                if args.len() != 2 {
                    return Err(format!("{name}: expected binary operands"));
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
            "Option" | "tobj" | "obj" => Self::option_case(x, code, depth, count, env, ret_ty, ctx),
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

    unsafe fn option_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> Result<(), String> {
        if !is_value_type(Self::ty(Self::field(x, 2)?)?) {
            return Err("Option case scrutinee must be object-valued".into());
        }
        let id = Self::var(Self::field(x, 1)?)?;
        if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
            return Err("Option case scrutinee not object-valued".into());
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.len() != 2 {
            return Err("Option case requires exactly two constructors".into());
        }
        let mut seen = [false; 2];
        writeln!(code, "    match x_{id}.tag() {{").unwrap();
        for alt in alts {
            if Self::tag(alt)? != 0 {
                return Err("Option default alternative unsupported".into());
            }
            let info = Self::field(alt, 0)?;
            let ctor = Self::name(Self::field(info, 0)?, 0)?;
            let idx = Self::nat(Self::field(info, 1)?)?;
            let expected = match idx {
                0 => "Option.none",
                1 => "Option.some",
                _ => return Err("invalid Option constructor index".into()),
            };
            if expected != ctor || seen[idx] {
                return Err("incorrect Option constructor metadata".into());
            }
            let pointer_fields = Self::nat(Self::field(info, 2)?)?;
            let usize_fields = Self::nat(Self::field(info, 3)?)?;
            let scalar_bytes = Self::nat(Self::field(info, 4)?)?;
            if pointer_fields != idx || usize_fields != 0 || scalar_bytes != 0 {
                return Err(format!(
                    "Option alternative {ctor} has unsupported field layout"
                ));
            }
            seen[idx] = true;
            writeln!(code, "        {idx} => {{").unwrap();
            if idx == 0 {
                writeln!(code, "            assert!(x_{id}.has_tagged(0), \"invalid Option.none representation\");").unwrap();
            } else {
                writeln!(code, "            assert!(x_{id}.has_ctor(1, \"Option.some\", 1), \"invalid Option.some representation\");").unwrap();
            }
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
            return Err("incomplete Option case".into());
        }
        writeln!(code, "        _ => unreachable!(\"invalid Option tag\"),").unwrap();
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
                    let value = Self::expr(Self::field(x, 2)?, ty, env, ctx.functions)?;
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
                        lowered.push(Self::arg(arg, env, ty)?);
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
        Ok(include_value_runtime(Self::emit_function(
            decl,
            &Self::string(rust_name)?,
            None,
        )?))
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
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
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
        Ok(include_value_runtime(result))
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
    primitive_spec(name).is_some() || is_nat_primitive(name)
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
    use super::{append_name_component, encode_name_str, internal_name, SUPPORTED_IR_TAGS};
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
        assert!(!SUPPORTED_IR_TAGS.contains(&("Expr", 1)));
        assert!(SUPPORTED_IR_TAGS.contains(&("IRType", 7)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 6)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 1)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 11)));
        assert!(SUPPORTED_IR_TAGS.contains(&("FnBody", 9)));
        assert!(SUPPORTED_IR_TAGS.contains(&("IRType", 0)));
        assert!(SUPPORTED_IR_TAGS.contains(&("Alt", 1)));
        assert!(!SUPPORTED_IR_TAGS.contains(&("FnBody", 2)));
        assert_eq!(SUPPORTED_IR_TAGS.len(), 30);
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
