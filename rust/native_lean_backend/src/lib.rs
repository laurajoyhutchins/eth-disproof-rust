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
    fn lr_nat_decimal(x: Obj) -> *mut c_char;
    fn lr_free_string(x: *mut c_char);
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
// The GMP implementation is injected only for generated code that actually
// invokes Nat primitives. Constructor-only programs must not link libgmp.
const VALUE_RUNTIME_SOURCE: &str = r#"
#[derive(Clone, Debug)]
pub struct __LeanValue(std::rc::Rc<__LeanValueRepr>);

#[derive(Debug)]
enum __LeanValueRepr {
    Tagged(usize),
    U8(u8), U16(u16), U32(u32), U64(u64), USize(usize),
    Ctor { tag: usize, name: &'static str, fields: Vec<__LeanValue> },
    Array(Vec<__LeanValue>),
    Erased, // Physically erased optimized-join argument, never valid to read.
    // __NAT_RUNTIME_VARIANT__
}

#[allow(dead_code)]
impl __LeanValue {
    fn tagged(v: usize) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::Tagged(v))) }
    fn erased() -> Self { Self(std::rc::Rc::new(__LeanValueRepr::Erased)) }
    fn is_shared(&self) -> u8 { u8::from(std::rc::Rc::strong_count(&self.0) > 1) }
    fn with_field(mut self, index: usize, value: Self) -> Self {
        if let Some(__LeanValueRepr::Ctor { fields, .. }) = std::rc::Rc::get_mut(&mut self.0) {
            *fields.get_mut(index).expect("constructor set: missing field") = value;
            return self;
        }
        match self.0.as_ref() {
            __LeanValueRepr::Ctor { tag, name, fields } => {
                let mut updated = fields.clone();
                *updated.get_mut(index).expect("constructor set: missing field") = value;
                Self::ctor(*tag, name, updated)
            }
            _ => panic!("constructor set on non-constructor or erased value"),
        }
    }
    fn boxed_u8(v: u8) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U8(v))) }
    fn boxed_u16(v: u16) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U16(v))) }
    fn boxed_u32(v: u32) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U32(v))) }
    fn boxed_u64(v: u64) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U64(v))) }
    fn boxed_usize(v: usize) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::USize(v))) }
    fn tagged_nat(&self) -> usize {
        match self.0.as_ref() {
            __LeanValueRepr::Tagged(n) => *n,
            _ => panic!("expected a statically tagged Nat"),
        }
    }
    fn empty_array(capacity: usize) -> Self {
        // Capacity is a performance hint, not part of observable array state.
        // Avoid attempting a huge eager allocation from a valid runtime Nat.
        let items = Vec::with_capacity(capacity.min(1024));
        Self(std::rc::Rc::new(__LeanValueRepr::Array(items)))
    }
    // Ownership-aware COW. The lowering passes the last IR use by move;
    // on aliases it retains the original and clones the Vec shallowly.
    // All elements remain immutable, Rc-shared Lean values.
    fn array_push(mut self, value: Self) -> Self {
        if let Some(__LeanValueRepr::Array(items)) = std::rc::Rc::get_mut(&mut self.0) {
            items.push(value);
            return self;
        }
        match self.0.as_ref() {
            __LeanValueRepr::Array(items) => {
                let mut updated = items.clone();
                updated.push(value);
                Self(std::rc::Rc::new(__LeanValueRepr::Array(updated)))
            }
            _ => panic!("Array.push on non-array object"),
        }
    }
    fn array_size(&self) -> Self {
        match self.0.as_ref() {
            __LeanValueRepr::Array(items) => Self::tagged(items.len()),
            _ => panic!("Array.size on non-array object"),
        }
    }
    fn array_get(&self, index: usize) -> Self {
        match self.0.as_ref() {
            __LeanValueRepr::Array(items) => items.get(index).expect("Array.getInternal: out of bounds").clone(),
            _ => panic!("Array.getInternal on non-array object"),
        }
    }
    fn array_set(mut self, index: usize, value: Self) -> Self {
        if let Some(__LeanValueRepr::Array(items)) = std::rc::Rc::get_mut(&mut self.0) {
            *items.get_mut(index).expect("Array.set!: out of bounds") = value;
            return self;
        }
        match self.0.as_ref() {
            __LeanValueRepr::Array(items) => {
                let mut updated = items.clone();
                *updated.get_mut(index).expect("Array.set!: out of bounds") = value;
                Self(std::rc::Rc::new(__LeanValueRepr::Array(updated)))
            }
            _ => panic!("Array.set! on non-array object"),
        }
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
}

"#;

const ARRAY_RUNTIME_TEST_SOURCE: &str = r#"
// These tests run against the actual emitted runtime, not a separately
// reimplemented model. Pointer identity verifies the unique-owner fast path;
// the shared test checks that the old observable value remains unchanged.
#[cfg(test)]
mod __lean_array_ownership_tests {
    use super::__LeanValue;
    use std::rc::Rc;

    #[test]
    fn unique_owner_reuses_array_allocation() {
        let empty = __LeanValue::empty_array(2);
        let before = Rc::as_ptr(&empty.0);
        let pushed = empty.array_push(__LeanValue::tagged(7));
        assert!(std::ptr::eq(before, Rc::as_ptr(&pushed.0)));
        let before = Rc::as_ptr(&pushed.0);
        let updated = pushed.array_set(0, __LeanValue::tagged(11));
        assert!(std::ptr::eq(before, Rc::as_ptr(&updated.0)));
        assert_eq!(updated.array_get(0).tagged_nat(), 11);
    }

    #[test]
    fn shared_owner_copies_before_update() {
        let old = __LeanValue::empty_array(2).array_push(__LeanValue::tagged(3));
        let alias = old.clone();
        let original = Rc::as_ptr(&old.0);
        let updated = old.array_set(0, __LeanValue::tagged(17));
        assert!(!std::ptr::eq(original, Rc::as_ptr(&updated.0)));
        assert_eq!(alias.array_get(0).tagged_nat(), 3);
        assert_eq!(updated.array_get(0).tagged_nat(), 17);
    }
}
"#;

const CTOR_RUNTIME_TEST_SOURCE: &str = r#"
#[cfg(test)]
mod __lean_constructor_ownership_tests {
    use super::__LeanValue;
    use std::rc::Rc;

    #[test]
    fn unique_constructor_field_update_reuses_allocation() {
        let first = __LeanValue::ctor(2, "Fixture.Record.pair", vec![
            __LeanValue::tagged(3), __LeanValue::tagged(4)
        ]);
        assert_eq!(first.is_shared(), 0);
        let previous = Rc::as_ptr(&first.0);
        let changed = first.with_field(0, __LeanValue::tagged(7));
        assert!(std::ptr::eq(previous, Rc::as_ptr(&changed.0)));
        assert_eq!(changed.field(0).tagged_nat(), 7);
        assert_eq!(changed.field(1).tagged_nat(), 4);
    }

    #[test]
    fn shared_constructor_field_update_preserves_alias() {
        let first = __LeanValue::ctor(2, "Fixture.Record.pair", vec![
            __LeanValue::tagged(3), __LeanValue::tagged(4)
        ]);
        let alias = first.clone();
        assert_eq!(first.is_shared(), 1);
        let previous = Rc::as_ptr(&first.0);
        let changed = first.with_field(1, __LeanValue::tagged(8));
        assert!(!std::ptr::eq(previous, Rc::as_ptr(&changed.0)));
        assert_eq!(alias.field(1).tagged_nat(), 4);
        assert_eq!(changed.field(1).tagged_nat(), 8);
    }

    #[test]
    #[should_panic(expected = "constructor set on non-constructor or erased value")]
    fn erased_join_payload_is_poison() {
        __LeanValue::erased().with_field(0, __LeanValue::tagged(9));
    }
}
"#;

const NAT_RUNTIME_SOURCE: &str = r#"// Nat is arbitrary precision in Lean. GMP is an established, maintained
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
    if !source.contains("__LeanValue") {
        return source;
    }
    // Detect actual generated Nat primitive calls rather than importing GMP
    // merely because an immutable constructor is represented by __LeanValue.
    let needs_nat = source.contains(".nat_binary(")
        || source.contains(".nat_cmp(")
        || source.contains("::nat_from_decimal(");
    let core = VALUE_RUNTIME_SOURCE.replace(
        "// __NAT_RUNTIME_VARIANT__",
        if needs_nat { "Nat(__LeanBigNat)," } else { "" },
    );
    // Tests come *after* generated functions: strict Clippy disallows
    // ordinary items following a test module.
    let mut tests = String::new();
    if source.contains(".array_push(") || source.contains(".array_set(") {
        tests.push_str(ARRAY_RUNTIME_TEST_SOURCE);
    }
    if source.contains(".with_field(") || source.contains(".is_shared()") {
        tests.push_str(CTOR_RUNTIME_TEST_SOURCE);
    }
    if needs_nat {
        format!("{core}\n{NAT_RUNTIME_SOURCE}\n{source}\n{tests}")
    } else {
        format!("{core}\n{source}\n{tests}")
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
    unsafe fn decimal_nat(x: Obj) -> Result<String, String> {
        let raw = lr_nat_decimal(x);
        if raw.is_null() {
            return Err("large Nat literal rejected (invalid or over 4 KiB)".into());
        }
        let result = CStr::from_ptr(raw)
            .to_str()
            .map_err(|_| "invalid Nat literal decimal representation".to_owned())
            .map(str::to_owned);
        lr_free_string(raw);
        result
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
                    || !s
                        .bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'!')
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
                if !ir_type_compatible(found, expected) {
                    return Err(format!("x_{id}: expected {expected}, got {found}"));
                }
                Ok(if is_value_type(found) {
                    format!("x_{id}.clone()")
                } else {
                    format!("x_{id}")
                })
            }
            1 => Err("erased value is only permitted as a guarded join payload".into()),
            t => Err(format!("unknown Arg constructor {t}")),
        }
    }
    unsafe fn ty(x: Obj) -> Result<&'static str, String> {
        // The tag ordering comes from the pinned Lean.Compiler.IR.Basic.
        match Self::tag(x)? {
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
        match Self::tag(x)? {
            0 => {
                // Boxed Nat literals can exceed machine word size. Decode
                // them through Lean's own pinned runtime, never through
                // truncating to a Rust usize/u64.
                if ty == "obj" || ty == "tobj" {
                    let decimal = Self::decimal_nat(Self::field(x, 0)?)?;
                    return Ok(format!("__LeanValue::nat_from_decimal(\"{decimal}\")"));
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
    unsafe fn arg_uses(x: Obj, id: usize) -> Result<bool, String> {
        Ok(Self::tag(x)? == 0 && Self::var(Self::field(x, 0)?)? == id)
    }
    unsafe fn args_use(args: Obj, id: usize) -> Result<bool, String> {
        for arg in Self::array(args)? {
            if Self::arg_uses(arg, id)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    // Unknown forms conservatively count as uses: this pass is only an
    // optimization and must never expand the accepted IR language.
    unsafe fn expr_uses(x: Obj, id: usize) -> Result<bool, String> {
        Ok(match Self::tag(x)? {
            0 => Self::args_use(Self::field(x, 1)?, id)?, // ctor
            1 | 2 => true, // reset/reuse are not in the supported subset
            3 => Self::var(Self::field(x, 1)?)? == id,
            4 => Self::var(Self::field(x, 1)?)? == id,
            5 => Self::var(Self::field(x, 2)?)? == id,
            6 | 7 => Self::args_use(Self::field(x, 1)?, id)?,
            8 => true, // ap not supported
            9 => Self::var(Self::field(x, 1)?)? == id,
            10 | 12 => Self::var(Self::field(x, 0)?)? == id,
            11 => false, // literal
            _ => true,
        })
    }
    unsafe fn body_uses(mut x: Obj, id: usize, depth: usize) -> Result<bool, String> {
        if depth > 128 {
            return Ok(true);
        }
        let mut remaining = 100_000usize;
        loop {
            if remaining == 0 {
                return Ok(true);
            }
            remaining -= 1;
            match Self::tag(x)? {
                0 => {
                    if Self::expr_uses(Self::field(x, 2)?, id)? {
                        return Ok(true);
                    }
                    x = Self::field(x, 3)?;
                }
                1 => {
                    if Self::body_uses(Self::field(x, 2)?, id, depth + 1)? {
                        return Ok(true);
                    }
                    x = Self::field(x, 3)?;
                }
                2..=5 => return Ok(true), // mutating forms are not yet supported
                6 | 7 => x = Self::field(x, 2)?, // compact Lean runtime layout for inc/dec
                8 => x = Self::field(x, 1)?, // non-observable del
                9 => {
                    if Self::var(Self::field(x, 1)?)? == id {
                        return Ok(true);
                    }
                    for alt in Self::array(Self::field(x, 3)?)? {
                        let body = match Self::tag(alt)? {
                            0 => Self::field(alt, 1)?,
                            1 => Self::field(alt, 0)?,
                            _ => return Ok(true),
                        };
                        if Self::body_uses(body, id, depth + 1)? {
                            return Ok(true);
                        }
                    }
                    return Ok(false);
                }
                10 => return Self::arg_uses(Self::field(x, 0)?, id),
                11 => return Self::args_use(Self::field(x, 1)?, id),
                12 => return Ok(false),
                _ => return Ok(true),
            }
        }
    }
    unsafe fn consumable_array(expr: Obj, tail: Obj) -> Result<Option<usize>, String> {
        if Self::tag(expr)? != 6 {
            return Ok(None);
        }
        let name = Self::name(Self::field(expr, 0)?, 0)?;
        if name != "Array.push" && name != "Array.set!" {
            return Ok(None);
        }
        let args = Self::array(Self::field(expr, 1)?)?;
        if args.len() != if name == "Array.push" { 3 } else { 4 } {
            return Ok(None);
        }
        if Self::tag(args[1])? != 0 {
            return Ok(None);
        }
        let id = Self::var(Self::field(args[1], 0)?)?;
        // A source used twice within the same primitive invocation must be
        // cloned before one of the uses can be consumed.
        for arg in args.iter().skip(2) {
            if Self::arg_uses(*arg, id)? {
                return Ok(None);
            }
        }
        if Self::body_uses(tail, id, 0)? {
            return Ok(None);
        }
        Ok(Some(id))
    }
    // Consume a compiled callee's object argument at its last IR use.
    // Without this, an unnecessary Rc clone at the call site changes the
    // observable optimization path of the callee's isShared check.
    unsafe fn consumable_call_object(
        expr: Obj,
        tail: Obj,
        env: &BTreeMap<usize, &'static str>,
        functions: Option<&FunctionTable>,
    ) -> Result<Option<usize>, String> {
        if Self::tag(expr)? != 6 {
            return Ok(None);
        }
        let name = Self::name(Self::field(expr, 0)?, 0)?;
        if functions.is_none_or(|f| !f.contains_key(&name)) {
            return Ok(None);
        }
        let args = Self::array(Self::field(expr, 1)?)?;
        for &candidate in &args {
            if Self::tag(candidate)? != 0 {
                continue;
            }
            let id = Self::var(Self::field(candidate, 0)?)?;
            if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
                continue;
            }
            let mut duplicates = 0;
            for arg in &args {
                if Self::arg_uses(*arg, id)? {
                    duplicates += 1;
                }
            }
            if duplicates == 1 && !Self::body_uses(tail, id, 0)? {
                return Ok(Some(id));
            }
        }
        Ok(None)
    }
    unsafe fn expr(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
        functions: Option<&FunctionTable>,
        consumed_array: Option<usize>,
    ) -> Result<String, String> {
        match Self::tag(x)? {
            0 => {
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
                // Any Lean inductive constructor with pointer-only fields is
                // representable by our typed Rc-backed constructor model.
                // The exact CtorInfo layout is checked instead of assuming
                // that source-language arity equals the runtime layout.
                if name.is_empty() || !name.contains('.') {
                    return Err("constructor has no supported qualified identity".into());
                }
                if usize_count != 0 || ssize != 0 || size != fields.len() || size > 1024 {
                    return Err(format!(
                        "constructor {name} has an unsupported scalar or field layout"
                    ));
                }
                if size == 0 {
                    if var_ty != "tagged" {
                        return Err(format!("zero-field constructor {name} is not tagged"));
                    }
                    return Ok(format!("__LeanValue::tagged({tag})"));
                }
                if var_ty != "obj" {
                    return Err(format!("constructor {name} expected object result"));
                }
                let mut args = Vec::with_capacity(fields.len());
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
            9 => {
                // box(scalar type, variable)
                if !is_value_type(var_ty) {
                    return Err("boxed scalar result must be object-valued".into());
                }
                let ty = Self::ty(Self::field(x, 0)?)?;
                if is_value_type(ty) {
                    return Err("box expects a scalar IR type".into());
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
                        if let Some(id) = consumed_array {
                            if Self::arg_uses(arg, id)? {
                                lowered.push(format!("x_{id}"));
                                continue;
                            }
                        }
                        lowered.push(Self::arg(arg, env, ty)?);
                    }
                    return Ok(format!("{}({})", internal_name(&name), lowered.join(", ")));
                }
                // A deliberately narrow, allocation-safe Array primitive
                // subset. Type/proof arguments are erased by Lean; check the
                // exact erased slots rather than silently dropping arguments.
                // The generated methods use persistent value semantics so
                // that updates never mutate a previously shared array.
                if name.starts_with("Array.") {
                    let erased = |i: usize| -> Result<(), String> {
                        if Self::tag(args[i])? == 1 {
                            Ok(())
                        } else {
                            Err(format!(
                                "{name}: expected an erased type/proof argument at {i}"
                            ))
                        }
                    };
                    let check = |arity: usize, ty: &str| -> Result<(), String> {
                        if args.len() != arity || var_ty != ty {
                            return Err(format!("{name}: wrong arity or IR result type"));
                        }
                        Ok(())
                    };
                    return match name.as_str() {
                        "Array.mkEmpty" => {
                            check(2, "obj")?;
                            erased(0)?;
                            let capacity = Self::arg(args[1], env, "tagged")?;
                            Ok(format!("__LeanValue::empty_array({capacity}.tagged_nat())"))
                        }
                        "Array.push" => {
                            check(3, "obj")?;
                            erased(0)?;
                            let array = if let Some(id) = consumed_array {
                                format!("x_{id}")
                            } else {
                                Self::arg(args[1], env, "obj")?
                            };
                            let item = Self::arg(args[2], env, "tobj")?;
                            Ok(format!("{array}.array_push({item})"))
                        }
                        "Array.size" => {
                            check(2, "tagged")?;
                            erased(0)?;
                            let array = Self::arg(args[1], env, "obj")?;
                            Ok(format!("{array}.array_size()"))
                        }
                        "Array.getInternal" | "Array.getInternalBorrowed" => {
                            check(4, "tobj")?;
                            erased(0)?;
                            erased(3)?;
                            let array = Self::arg(args[1], env, "obj")?;
                            let index = Self::arg(args[2], env, "tagged")?;
                            Ok(format!("{array}.array_get({index}.tagged_nat())"))
                        }
                        "Array.set!" => {
                            check(4, "obj")?;
                            erased(0)?;
                            let array = if let Some(id) = consumed_array {
                                format!("x_{id}")
                            } else {
                                Self::arg(args[1], env, "obj")?
                            };
                            let index = Self::arg(args[2], env, "tagged")?;
                            let item = Self::arg(args[3], env, "tobj")?;
                            Ok(format!("{array}.array_set({index}.tagged_nat(), {item})"))
                        }
                        _ => Err(format!("unrecognized Array primitive: {name}")),
                    };
                }
                if args.len() != 2 {
                    return Err(format!("{name}: expected binary operands"));
                }
                let mut both_tagged = true;
                if matches!(name.as_str(), "Nat.decEq" | "Nat.decLt" | "Nat.decLe") {
                    for arg in &args {
                        if Self::tag(*arg)? != 0 {
                            both_tagged = false;
                            break;
                        }
                        let id = Self::var(Self::field(*arg, 0)?)?;
                        if env.get(&id) != Some(&"tagged") {
                            both_tagged = false;
                            break;
                        }
                    }
                } else {
                    both_tagged = false;
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
                if matches!(
                    name.as_str(),
                    "Nat.add"
                        | "Nat.sub"
                        | "Nat.mul"
                        | "Nat.div"
                        | "Nat.mod"
                        | "Nat.decEq"
                        | "Nat.decLt"
                        | "Nat.decLe"
                ) {
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
                let (op, comparison) = match name.as_str() {
                    "UInt8.add" | "UInt16.add" | "UInt32.add" | "UInt64.add" | "USize.add" => {
                        ("wrapping_add", false)
                    }
                    "UInt8.sub" | "UInt16.sub" | "UInt32.sub" | "UInt64.sub" | "USize.sub" => {
                        ("wrapping_sub", false)
                    }
                    "UInt8.mul" | "UInt16.mul" | "UInt32.mul" | "UInt64.mul" | "USize.mul" => {
                        ("wrapping_mul", false)
                    }
                    "UInt8.decEq" | "UInt16.decEq" | "UInt32.decEq" | "UInt64.decEq"
                    | "USize.decEq" => ("==", true),
                    "UInt8.decLt" | "UInt16.decLt" | "UInt32.decLt" | "UInt64.decLt"
                    | "USize.decLt" => ("<", true),
                    "UInt8.decLe" | "UInt16.decLe" | "UInt32.decLe" | "UInt64.decLe"
                    | "USize.decLe" => ("<=", true),
                    _ => return Err(format!("unrecognized primitive call: {name}")),
                };
                let expected_ty = match name.split('.').next() {
                    Some("UInt8") => "u8",
                    Some("UInt16") => "u16",
                    Some("UInt32") => "u32",
                    Some("UInt64") => "u64",
                    Some("USize") => "usize",
                    _ => return Err(format!("invalid primitive namespace: {name}")),
                };
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
            11 => Ok(Self::lit(Self::field(x, 0)?, var_ty)?),
            12 => {
                if var_ty != "u8" {
                    return Err("isShared must yield uint8".into());
                }
                let id = Self::var(Self::field(x, 0)?)?;
                if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
                    return Err("isShared expects a value object".into());
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
            "UInt8" => Self::boolean_case(x, code, depth, count, env, ret_ty, ctx),
            "Option" | "Sum" | "tobj" | "obj" => {
                Self::algebraic_case(x, code, depth, count, env, ret_ty, ctx)
            }
            _ => Err(format!("unsupported case type {type_name}")),
        }
    }

    // Constructor family is determined from the *actual pinned IR metadata*,
    // not guessed from a generic `obj` scrutinee's runtime tag.
    unsafe fn algebraic_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> Result<(), String> {
        if !is_value_type(Self::ty(Self::field(x, 2)?)?) {
            return Err("algebraic case scrutinee must be object-valued".into());
        }
        let id = Self::var(Self::field(x, 1)?)?;
        if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
            return Err("algebraic case scrutinee not object-valued".into());
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.is_empty() || alts.len() > 256 {
            return Err("algebraic case alternative count outside supported range".into());
        }
        let mut seen_tags = BTreeSet::new();
        let mut family: Option<String> = None;
        let mut saw_default = false;
        writeln!(code, "    match x_{id}.tag() {{").unwrap();
        for (index, alt) in alts.iter().enumerate() {
            match Self::tag(*alt)? {
                0 => {
                    if saw_default {
                        return Err("constructor alternative follows default".into());
                    }
                    let info = Self::field(*alt, 0)?;
                    let ctor = Self::name(Self::field(info, 0)?, 0)?;
                    let (parent, _) = ctor
                        .rsplit_once('.')
                        .ok_or_else(|| format!("invalid constructor family for {ctor}"))?;
                    if !family.as_ref().is_none_or(|f| f == parent) {
                        return Err(format!(
                            "mixed constructor families in algebraic case: {ctor}"
                        ));
                    }
                    family = Some(parent.to_owned());
                    let tag = Self::nat(Self::field(info, 1)?)?;
                    if !seen_tags.insert(tag) {
                        return Err(format!("duplicate constructor index {tag}"));
                    }
                    let ptrs = Self::nat(Self::field(info, 2)?)?;
                    let usize_fields = Self::nat(Self::field(info, 3)?)?;
                    let scalar_bytes = Self::nat(Self::field(info, 4)?)?;
                    if usize_fields != 0 || scalar_bytes != 0 || ptrs > 1024 {
                        return Err(format!("unsupported constructor field layout: {ctor}"));
                    }
                    writeln!(code, "        {tag} => {{").unwrap();
                    if ptrs == 0 {
                        writeln!(code, "            assert!(x_{id}.has_tagged({tag}), \"invalid tagged constructor\");").unwrap();
                    } else {
                        writeln!(code, "            assert!(x_{id}.has_ctor({tag}, \"{ctor}\", {ptrs}), \"invalid constructor representation\");").unwrap();
                    }
                    let mut arm_env = env.clone();
                    Self::body(
                        Self::field(*alt, 1)?,
                        code,
                        depth + 1,
                        count,
                        &mut arm_env,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "        }}").unwrap();
                }
                1 => {
                    if saw_default || index != alts.len() - 1 {
                        return Err("algebraic default must be unique and last".into());
                    }
                    saw_default = true;
                    writeln!(code, "        _ => {{").unwrap();
                    let mut arm_env = env.clone();
                    Self::body(
                        Self::field(*alt, 0)?,
                        code,
                        depth + 1,
                        count,
                        &mut arm_env,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "        }}").unwrap();
                }
                t => return Err(format!("unknown algebraic alternative constructor {t}")),
            }
        }
        if family.is_none() {
            return Err("algebraic case lacks constructor identity metadata".into());
        }
        if !saw_default {
            writeln!(
                code,
                "        _ => unreachable!(\"unknown Lean constructor tag\"),"
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
                    let consumed_array = if ctx.joins.is_empty() {
                        Self::consumable_array(expr, Self::field(x, 3)?)?.or(
                            Self::consumable_call_object(
                                expr,
                                Self::field(x, 3)?,
                                env,
                                ctx.functions,
                            )?,
                        )
                    } else {
                        // An earlier lexical join closure may borrow this value.
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
                    // Lean IR set requires unique ownership. Generated Rust
                    // keeps the observable value semantics with COW, even if
                    // Rust's ownership counts differ from Lean's RC schedule.
                    let id = Self::var(Self::field(x, 0)?)?;
                    let ty = env
                        .get(&id)
                        .ok_or("set on undefined constructor variable")?;
                    if !is_value_type(ty) {
                        return Err("set on non-object variable".into());
                    }
                    let index = Self::nat(Self::field(x, 1)?)?;
                    if index >= 1024 {
                        return Err("constructor set field index exceeds cap".into());
                    }
                    let value = Self::arg(Self::field(x, 2)?, env, "tobj")?;
                    writeln!(
                        code,
                        "    let x_{id} = x_{id}.with_field({index}, {value});"
                    )
                    .unwrap();
                    // A field write proves heap-constructor representation.
                    env.insert(id, "obj");
                    x = Self::field(x, 3)?;
                }
                6..=8 => {
                    // Rc-backed emitted values own their references;
                    // Lean's inc/dec/del bookkeeping is non-observable for
                    // supported pure value semantics; exact RC traces are not claimed.
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
                        if Self::tag(arg)? == 1 {
                            if !is_value_type(ty) {
                                return Err("erased scalar join argument not supported".into());
                            }
                            // A guard-dependent parameter is physically
                            // absent in this path. Any accidental read must
                            // trap, never silently yield an arbitrary object.
                            lowered.push("__LeanValue::erased()".into());
                        } else {
                            lowered.push(Self::arg(arg, env, ty)?);
                        }
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
                2 => pending.push(Self::field(body, 3)?),
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

fn is_primitive(name: &str) -> bool {
    matches!(
        name,
        "Nat.add"
            | "Array.mkEmpty"
            | "Array.push"
            | "Array.size"
            | "Array.getInternal"
            | "Array.getInternalBorrowed"
            | "Array.set!"
            | "Nat.sub"
            | "Nat.mul"
            | "Nat.div"
            | "Nat.mod"
            | "Nat.decEq"
            | "Nat.decLt"
            | "Nat.decLe"
            | "UInt8.add"
            | "UInt16.add"
            | "UInt32.add"
            | "UInt64.add"
            | "USize.add"
            | "UInt8.sub"
            | "UInt16.sub"
            | "UInt32.sub"
            | "UInt64.sub"
            | "USize.sub"
            | "UInt8.mul"
            | "UInt16.mul"
            | "UInt32.mul"
            | "UInt64.mul"
            | "USize.mul"
            | "UInt8.decEq"
            | "UInt16.decEq"
            | "UInt32.decEq"
            | "UInt64.decEq"
            | "USize.decEq"
            | "UInt8.decLt"
            | "UInt16.decLt"
            | "UInt32.decLt"
            | "UInt64.decLt"
            | "USize.decLt"
            | "UInt8.decLe"
            | "UInt16.decLe"
            | "UInt32.decLe"
            | "UInt64.decLe"
            | "USize.decLe"
    )
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
    use super::internal_name;
    #[test]
    fn closure_symbol_mangling_is_injective_on_ascii_names() {
        assert_ne!(internal_name("X.ab"), internal_name("X.a_b"));
        assert_ne!(internal_name("X.A"), internal_name("X.a"));
        assert!(internal_name("X.a").starts_with("lean_"));
    }
    #[test]
    fn nat_runtime_is_injected_only_when_needed() {
        let obj_only =
            super::include_value_runtime("pub fn keep(x: __LeanValue) -> __LeanValue { x }".into());
        assert!(obj_only.contains("pub struct __LeanValue"));
        assert!(!obj_only.contains("__gmpz_init"));
        assert!(!obj_only.contains("Nat(__LeanBigNat)"));

        let with_nat_ops = super::include_value_runtime(
            "pub fn add(x: __LeanValue, y: __LeanValue) -> __LeanValue { x.nat_binary(&y, \"add\") }".into(),
        );
        assert!(with_nat_ops.contains("__gmpz_init"));
        assert!(with_nat_ops.contains("Nat(__LeanBigNat)"));

        let with_literal = super::include_value_runtime(
            "pub fn constant() -> __LeanValue { __LeanValue::nat_from_decimal(\"123\") }".into(),
        );
        assert!(with_literal.contains("__gmpz_init"));
    }
    #[test]
    fn permitted_rust_identacters_only() {
        for s in ["a", "a_1", "Fn2"] {
            assert!(s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'));
        }
    }
}
