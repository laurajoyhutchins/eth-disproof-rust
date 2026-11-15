
// Rust Rc tracks actual memory safety. The second Rc tracks the reference
// count observed by Lean IR, independently of transient Rust value clones.
// A direct Rust clone is not a source IR.inc instruction.
#[derive(Debug)]
pub struct __LeanValue(
    std::rc::Rc<__LeanValueRepr>,
    std::rc::Rc<std::cell::Cell<usize>>,
);

#[derive(Debug)]
enum __LeanValueRepr {
    Tagged(usize),
    Erased, // Physically absent optimized join parameter; any read must trap.
    U8(u8), U16(u16), U32(u32), U64(u64), USize(usize),
    Ctor { tag: usize, name: &'static str, fields: Vec<__LeanValue> },
    // Verified Lean 4.34.1 SyncModel.PullIn.mk: four pointer fields and
    // eight packed source Bool bytes. Not general mutable-heap support.
    PullIn { fields: Vec<__LeanValue>, bytes: [u8; 8] },
    // Immutable first-class functions, represented by a statically generated
    // object-argument thunk and an Rc-shared vector of captured values.
    Closure {
        arity: usize,
        captures: Vec<__LeanValue>,
        invoke: fn(Vec<__LeanValue>) -> __LeanValue,
    },
    // Most source PAPs in the verified closure corpus bind one argument of
    // a binary function. Store it directly in the existing Rc allocation:
    // no separate Vec allocation, lookup table, or change to source semantics.
    Closure2 {
        capture: __LeanValue,
        invoke: fn(__LeanValue, __LeanValue) -> __LeanValue,
    },
    // Actual Lean 4.34.1 boxed lambda IR often has two bound arguments and
    // one remaining AP operand (e.g. FunctionValues.runIndirect). The
    // captures live in the Rc object instead of a separate Vec allocation.
    Closure3 {
        first: __LeanValue,
        second: __LeanValue,
        invoke: fn(__LeanValue, __LeanValue, __LeanValue) -> __LeanValue,
    },
    Nat(__LeanBigNat),
    Int(__LeanBigNat),
    Str(String),
    Array(Vec<__LeanValue>),
    List(Vec<__LeanValue>),
}

// A public Clone represents a second owned Lean reference. Generated
// compiler temporaries instead call compiler_alias, which has no source RC
// effect. This distinction is essential at exported function boundaries.
impl Clone for __LeanValue {
    fn clone(&self) -> Self {
        self.source_inc(1, true, false);
        self.compiler_alias()
    }
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
    fn compiler_alias(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }

    fn from_repr(repr: __LeanValueRepr) -> Self {
        // Every newly allocated source heap object owns one Lean reference.
        // Tagged immediates are exempt from source reference counting.
        Self(
            std::rc::Rc::new(repr),
            std::rc::Rc::new(std::cell::Cell::new(1)),
        )
    }

    fn source_heap(&self) -> bool {
        !matches!(self.0.as_ref(), __LeanValueRepr::Tagged(_) | __LeanValueRepr::Erased)
    }

    // These methods implement the source IR bookkeeping on a *separate*
    // logical counter. Compiler-internal Rust Rc clones do not alter it.
    #[track_caller]
    fn source_inc(&self, n: usize, check_ref: bool, persistent: bool) {
        self.assert_not_erased();
        if persistent { return; }
        if !self.source_heap() {
            assert!(check_ref, "unchecked source inc on a tagged immediate");
            return;
        }
        let old = self.1.get();
        assert!(old > 0, "source inc on released object");
        self.1.set(old.checked_add(n).expect("source reference-count overflow"));
    }

    #[track_caller]
    fn source_dec(&self, n: usize, check_ref: bool, persistent: bool) {
        self.assert_not_erased();
        if persistent { return; }
        if !self.source_heap() {
            assert!(check_ref, "unchecked source dec on a tagged immediate");
            return;
        }
        // Lean's pinned LLVM backend accepts only a single reference
        // decrement. Reject unsupported non-unit decrements.
        assert_eq!(n, 1, "Lean 4.34.1 source dec requires n = 1");
        let old = self.1.get();
        assert!(old > 0, "source dec on released object");
        self.1.set(old - 1);
        if old == 1 {
            // Cascade source-owned field releases iteratively. Deep Lean
            // lists must not require one native Rust stack frame per cell.
            let mut pending = Vec::new();
            self.source_enqueue_children(&mut pending);
            while let Some(child) = pending.pop() {
                if !child.source_heap() {
                    continue;
                }
                let count = child.1.get();
                assert!(count > 0, "source child release on exhausted reference");
                child.1.set(count - 1);
                if count == 1 {
                    child.source_enqueue_children(&mut pending);
                }
            }
        }
    }

    // The Lean del instruction calls lean_del_object, which releases the
    // container shell, not its already transferred child references.
    #[track_caller]
    fn source_del(&self) {
        self.assert_not_erased();
        // lean_del_object checks the tagged-pointer bit and is a no-op for
        // immediate values. Heap deletion frees only the container shell.
        if !self.source_heap() { return; }
        assert_eq!(self.1.replace(0), 1, "source del requires unique object");
    }

    fn source_enqueue_children(&self, pending: &mut Vec<Self>) {
        match self.0.as_ref() {
            __LeanValueRepr::Ctor { fields, .. }
            | __LeanValueRepr::PullIn { fields, .. }
            | __LeanValueRepr::Array(fields)
            | __LeanValueRepr::List(fields) => {
                pending.extend(fields.iter().map(Self::compiler_alias));
            }
            __LeanValueRepr::Closure { captures, .. } => {
                pending.extend(captures.iter().map(Self::compiler_alias));
            }
            __LeanValueRepr::Closure2 { capture, .. } => pending.push(capture.compiler_alias()),
            __LeanValueRepr::Closure3 { first, second, .. } => {
                pending.push(first.compiler_alias());
                pending.push(second.compiler_alias());
            }
            _ => {}
        }
    }

    // Lean constructor pointer-field set: unique mutation, alias-safe COW.
    // Rc ownership is used only to choose a safe implementation path.
    // This is not a claim of identical Lean/Rust reference-count traces.
    fn assert_not_erased(&self) {
        assert!(!matches!(self.0.as_ref(), __LeanValueRepr::Erased), "erased join value was read");
    }
    fn is_shared(&self) -> u8 {
        self.assert_not_erased();
        // Tagged immediates have no Lean heap reference count. A Rust Rc
        // allocation for the tagged adapter must not make them observable.
        assert!(
            !matches!(self.0.as_ref(), __LeanValueRepr::Tagged(_)),
            "isShared requires a heap-backed Lean value"
        );
        assert!(self.1.get() > 0, "isShared on released source object");
        u8::from(self.1.get() != 1)
    }
    fn with_field(mut self, index: usize, value: Self) -> Self {
        if let Some(__LeanValueRepr::Ctor { fields, .. }) = std::rc::Rc::get_mut(&mut self.0) {
            *fields.get_mut(index).expect("constructor set: invalid pointer index") = value;
            return self;
        }
        match self.0.as_ref() {
            __LeanValueRepr::Ctor { tag, name, fields } => {
                let mut updated = fields.clone();
                *updated.get_mut(index).expect("constructor set: invalid pointer index") = value;
                Self::ctor(*tag, name, updated)
            }
            _ => panic!("constructor field set on non-constructor"),
        }
    }
    // Lean IR tobj is a heap object OR a tagged value. Refine it to an
    // obj only when the actual runtime representation is a constructor.
    // Other heap representations need their own source-checked contract.
    // This guard is also the backstop against reading an erased join arg.
    fn require_constructor_object(self) -> Self {
        assert!(
            matches!(
                self.0.as_ref(),
                __LeanValueRepr::Ctor { .. } | __LeanValueRepr::PullIn { .. }
            ),
            "tobject join requires a heap constructor"
        );
        self
    }
    fn erased() -> Self { Self::from_repr(__LeanValueRepr::Erased) }
    fn tagged(v: usize) -> Self { Self::from_repr(__LeanValueRepr::Tagged(v)) }
    fn boxed_u8(v: u8) -> Self { Self::from_repr(__LeanValueRepr::U8(v)) }
    fn boxed_u16(v: u16) -> Self { Self::from_repr(__LeanValueRepr::U16(v)) }
    fn boxed_u32(v: u32) -> Self { Self::from_repr(__LeanValueRepr::U32(v)) }
    pub fn boxed_u64(v: u64) -> Self { Self::from_repr(__LeanValueRepr::U64(v)) }
    fn boxed_usize(v: usize) -> Self { Self::from_repr(__LeanValueRepr::USize(v)) }

    pub fn nat(text: &str) -> Self { Self::nat_from_decimal(text) }
    pub fn int(text: &str) -> Self {
        let digits = text.strip_prefix('-').unwrap_or(text);
        assert!(!digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()), "invalid Int decimal input");
        let cstr = std::ffi::CString::new(text).expect("decimal Int cannot contain NUL");
        let mut value = __LeanBigNat::zero();
        let rc = unsafe { __gmpz_set_str(&mut value.value, cstr.as_ptr(), 10) };
        assert_eq!(rc, 0, "invalid GMP signed decimal input");
        Self::from_repr(__LeanValueRepr::Int(value))
    }
    pub fn string(value: &str) -> Self {
        Self::from_repr(__LeanValueRepr::Str(value.to_owned()))
    }
    pub fn array(values: Vec<Self>) -> Self {
        Self::from_repr(__LeanValueRepr::Array(values))
    }

    // `Array.mkEmpty` has an unobservable capacity hint. Keep
    // allocation bounded even if the original Nat is enormous.
    fn empty_array(capacity: usize) -> Self {
        Self::array(Vec::with_capacity(capacity.min(1024)))
    }
    fn tagged_nat(&self) -> usize {
        // The Lean IR variable may be statically tagged while the canonical
        // standalone Value representation contains a GMP-backed Nat.
        // Read the *exact* numeric value; never truncate an arbitrary Nat.
        match self.0.as_ref() {
            __LeanValueRepr::Tagged(n) => *n,
            __LeanValueRepr::Nat(n) => n
                .decimal()
                .parse::<usize>()
                .expect("source Nat index does not fit usize"),
            _ => panic!("expected a source-verified small Nat"),
        }
    }
    fn array_get_tagged(&self, index: usize) -> Self {
        let __LeanValueRepr::Array(values) = self.0.as_ref()
        else { panic!("Array.getInternal expected an Array"); };
        values.get(index).expect("source Array.getInternal index out of bounds").clone()
    }
    // Lean's lean_array_uget_borrowed returns a borrowed element with no
    // refcount increment; lean_array_uget owns its result and does increment.
    fn array_get_tagged_borrowed(&self, index: usize) -> Self {
        let __LeanValueRepr::Array(values) = self.0.as_ref()
        else { panic!("Array.getInternalBorrowed expected an Array"); };
        values.get(index).expect("source Array.getInternalBorrowed index out of bounds")
            .compiler_alias()
    }

    // A persistent copy preserves all observable prior references. The
    // ownership-aware optimization is a separate reviewed concern.
    fn array_set_tagged(&self, index: usize, value: Self) -> Self {
        let __LeanValueRepr::Array(values) = self.0.as_ref()
        else { panic!("Array.set! expected an Array"); };
        let mut updated = values.clone();
        *updated.get_mut(index).expect("source Array.set! index out of bounds") = value;
        Self::array(updated)
    }
    fn pull_in_ctor(fields: Vec<Self>) -> Self {
        assert_eq!(fields.len(), 4, "source PullIn requires four object fields");
        Self::from_repr(__LeanValueRepr::PullIn {
            fields,
            bytes: [0; 8],
        })
    }
    fn pull_in_set_u8(self, pointers: usize, offset: usize, value: u8) -> Self {
        assert_eq!(pointers, 4, "source PullIn object width");
        assert!(offset < 8 && value <= 1, "source PullIn Bool byte");
        // Lean sset demands RC=1. Consume an unaliased Rc and refuse shared
        // pointers rather than silently changing their mutation semantics.
        let mut repr = std::rc::Rc::try_unwrap(self.0)
            .expect("Lean sset requires unshared source constructor");
        let __LeanValueRepr::PullIn { bytes, .. } = &mut repr
        else { panic!("Lean sset target is not PullIn") };
        bytes[offset] = value;
        Self(std::rc::Rc::new(repr), self.1)
    }
    fn pull_in_sproj_u8(&self, pointers: usize, offset: usize) -> u8 {
        assert_eq!(pointers, 4, "source PullIn object width");
        assert!(offset < 8, "source PullIn Bool byte offset");
        let __LeanValueRepr::PullIn { bytes, .. } = self.0.as_ref()
        else { panic!("Lean sproj source is not PullIn") };
        bytes[offset]
    }
    pub fn list(values: Vec<Self>) -> Self {
        Self::from_repr(__LeanValueRepr::List(values))
    }
    // Generated Lean List.cons is a two-pointer immutable constructor.
    // Retain O(1) cons and sharing rather than copying the tail on construction.
    // Vec-backed lists remain accepted as the existing source-runtime List
    // adapter's owned input/output representation.
    fn list_cons(head: Self, tail: Self) -> Self {
        assert!(tail.list_is_nil() || tail.list_is_cons(), "List.cons tail must be a List");
        Self::ctor(1, "List.cons", vec![head, tail])
    }
    fn list_is_nil(&self) -> bool {
        match self.0.as_ref() {
            __LeanValueRepr::Tagged(0) => true,
            __LeanValueRepr::List(values) => values.is_empty(),
            _ => false,
        }
    }
    fn list_is_cons(&self) -> bool {
        match self.0.as_ref() {
            __LeanValueRepr::Ctor { tag: 1, name: "List.cons", fields } =>
                fields.len() == 2,
            __LeanValueRepr::List(values) => !values.is_empty(),
            _ => false,
        }
    }
    // Source-defined list operators must accept both immutable cons cells
    // and the preexisting Vec-backed, persistent List runtime adapter.
    // The resource cap is explicit; no recursive traversal or hidden mutation.
    fn list_items(&self) -> Vec<Self> {
        let mut items = Vec::new();
        let mut cursor = self.compiler_alias();
        loop {
            let next = match cursor.0.as_ref() {
                __LeanValueRepr::Tagged(0) => None,
                __LeanValueRepr::List(values) => {
                    items.extend(values.iter().cloned());
                    None
                }
                __LeanValueRepr::Ctor { tag: 1, name: "List.cons", fields }
                    if fields.len() == 2 => {
                    items.push(fields[0].clone());
                    Some(fields[1].compiler_alias())
                }
                _ => panic!("List operation received unsupported value representation"),
            };
            assert!(items.len() <= 1_000_000, "List conversion exceeds bounded runtime policy");
            match next {
                Some(tail) => cursor = tail,
                None => break,
            }
        }
        items
    }
    fn int_add(&self, rhs: &Self) -> Self {
        let (__LeanValueRepr::Int(a), __LeanValueRepr::Int(b)) =
            (self.0.as_ref(), rhs.0.as_ref())
        else { panic!("Int.add expects two signed GMP Int objects"); };
        let mut out = __LeanBigNat::zero();
        unsafe { __gmpz_add(&mut out.value, a.ptr(), b.ptr()); }
        Self::from_repr(__LeanValueRepr::Int(out))
    }
    fn string_append(&self, rhs: &Self) -> Self {
        let (__LeanValueRepr::Str(a), __LeanValueRepr::Str(b)) =
            (self.0.as_ref(), rhs.0.as_ref())
        else { panic!("String.append expects UTF-8 String values"); };
        Self::string(&format!("{a}{b}"))
    }
    fn string_bytes(&self) -> Self {
        let __LeanValueRepr::Str(value) = self.0.as_ref()
        else { panic!("String.utf8ByteSize expects String"); };
        Self::nat_from_decimal(&value.len().to_string())
    }
    fn string_chars(&self) -> Self {
        let __LeanValueRepr::Str(value) = self.0.as_ref()
        else { panic!("String.length expects String"); };
        Self::nat_from_decimal(&value.chars().count().to_string())
    }
    fn array_push(&self, value: &Self) -> Self {
        let __LeanValueRepr::Array(values) = self.0.as_ref()
        else { panic!("Array.push expects Array"); };
        let mut next = values.clone();
        next.push(value.clone());
        Self::array(next)
    }

    // Transfer the final IR use of an Array into its next value. Shared
    // references are detected dynamically, so aliases preserve prior values.
    #[allow(dead_code)]
    fn array_push_owned(mut self, value: Self) -> Self {
        if let Some(__LeanValueRepr::Array(values)) = std::rc::Rc::get_mut(&mut self.0) {
            values.push(value);
            return self;
        }
        let __LeanValueRepr::Array(values) = self.0.as_ref()
        else { panic!("Array.push expects Array"); };
        let mut next = values.clone();
        next.push(value);
        Self::array(next)
    }
    #[allow(dead_code)]
    fn array_set_tagged_owned(mut self, index: usize, value: Self) -> Self {
        if let Some(__LeanValueRepr::Array(values)) = std::rc::Rc::get_mut(&mut self.0) {
            *values.get_mut(index).expect("source Array.set! index out of bounds") = value;
            return self;
        }
        let __LeanValueRepr::Array(values) = self.0.as_ref()
        else { panic!("Array.set! expected an Array"); };
        let mut updated = values.clone();
        *updated.get_mut(index).expect("source Array.set! index out of bounds") = value;
        Self::array(updated)
    }
    fn array_size(&self) -> Self {
        let __LeanValueRepr::Array(values) = self.0.as_ref()
        else { panic!("Array.size expects Array"); };
        // Lean's array length is a small Nat on pinned x86-64. The old
        // implementation allocated a GMP integer and formatted the length
        // in decimal on every size probe, including Array.getD bounds checks.
        // Keep a total fallback at the tagged Nat cutoff rather than truncate.
        let len = values.len();
        if len <= usize::MAX >> 1 {
            Self::tagged(len)
        } else {
            Self::nat_from_decimal(&len.to_string())
        }
    }
    fn list_reverse(&self) -> Self {
        let mut values = self.list_items();
        values.reverse();
        Self::list(values)
    }
    pub fn nat_from_decimal(value: &str) -> Self {
        Self::from_repr(__LeanValueRepr::Nat(__LeanBigNat::from_decimal(value)))
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
        Self::from_repr(__LeanValueRepr::Nat(result))
    }
    fn nat_cmp(&self, other: &Self) -> i32 {
        let lhs = self.nat_operand();
        let rhs = other.nat_operand();
        unsafe { __gmpz_cmp(lhs.as_ref().ptr(), rhs.as_ref().ptr()) }
    }
    fn ctor(tag: usize, name: &'static str, fields: Vec<Self>) -> Self {
        Self::from_repr(__LeanValueRepr::Ctor { tag, name, fields })
    }
    fn tag(&self) -> usize {
        match self.0.as_ref() {
            __LeanValueRepr::Tagged(v) => *v,
            __LeanValueRepr::Ctor { tag, .. } => *tag,
            __LeanValueRepr::PullIn { .. } => 0,
            __LeanValueRepr::List(values) => usize::from(!values.is_empty()),
            _ => panic!("tried to case-analyze a boxed scalar"),
        }
    }
    fn has_ctor(&self, tag: usize, name: &str, arity: usize) -> bool {
        self.assert_not_erased();
        match self.0.as_ref() {
            __LeanValueRepr::Ctor {tag: t, name: n, fields} =>
                *t == tag && *n == name && fields.len() == arity,
            __LeanValueRepr::List(values) =>
                tag == 1 && name == "List.cons" && arity == 2 && !values.is_empty(),
            _ => false,
        }
    }
    fn has_tagged(&self, value: usize) -> bool {
        self.assert_not_erased();
        matches!(self.0.as_ref(), __LeanValueRepr::Tagged(v) if *v == value)
    }
    fn field(&self, index: usize) -> Self {
        match self.0.as_ref() {
            __LeanValueRepr::Ctor { fields, .. } =>
                fields.get(index).expect("constructor field absent").compiler_alias(),
            __LeanValueRepr::PullIn { fields, .. } =>
                fields.get(index).expect("PullIn field absent").compiler_alias(),
            __LeanValueRepr::List(values) if !values.is_empty() => match index {
                0 => values[0].compiler_alias(),
                1 => Self::list(values[1..].to_vec()),
                _ => panic!("List.cons has exactly two fields"),
            },
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
        Self::from_repr(__LeanValueRepr::Closure { arity, captures, invoke })
    }

    fn pap2(invoke: fn(Self, Self) -> Self, capture: Self) -> Self {
        Self::from_repr(__LeanValueRepr::Closure2 { capture, invoke })
    }

    fn pap3(invoke: fn(Self, Self, Self) -> Self, first: Self, second: Self) -> Self {
        Self::from_repr(__LeanValueRepr::Closure3 { first, second, invoke })
    }

    // Preserve declaration-order captures, support repeated applications
    // through aliases, and retain general partially applied source functions.
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
            __LeanValueRepr::Closure2 { capture, invoke } => {
                assert_eq!(args.len(), 1, "oversaturated binary source PAP");
                invoke(capture.clone(), args.into_iter().next().unwrap())
            }
            __LeanValueRepr::Closure3 { first, second, invoke } => {
                assert_eq!(args.len(), 1, "oversaturated ternary source PAP");
                invoke(first.clone(), second.clone(), args.into_iter().next().unwrap())
            }
            _ => panic!("tried to apply a non-function Lean value"),
        }
    }

    // A single-argument indirect application is frequent in source Lean.
    // Avoid allocating a temporary Vec for an inline binary PAP. Generic
    // closures retain the existing verified vector-based ABI and behavior.
    fn apply1(&self, arg: Self) -> Self {
        match self.0.as_ref() {
            __LeanValueRepr::Closure2 { capture, invoke } => invoke(capture.clone(), arg),
            __LeanValueRepr::Closure3 { first, second, invoke } => {
                invoke(first.clone(), second.clone(), arg)
            }
            __LeanValueRepr::Closure { .. } => self.apply(vec![arg]),
            _ => panic!("tried to apply a non-function Lean value"),
        }
    }

    // Consume a closure only when the emitter proves that *no* possible
    // continuation or join reads it. If another Rc alias exists, recover the
    // shared representation and use the borrowed path. Only uniquely owned
    // closure captures can be moved into a generated source function.
    fn apply1_owned(self, arg: Self) -> Self {
        let Self(repr, logical) = self;
        match std::rc::Rc::try_unwrap(repr) {
            Ok(__LeanValueRepr::Closure2 { capture, invoke }) => invoke(capture, arg),
            Ok(__LeanValueRepr::Closure3 { first, second, invoke }) => {
                invoke(first, second, arg)
            }
            Ok(__LeanValueRepr::Closure { arity, mut captures, invoke }) => {
                captures.push(arg);
                assert!(captures.len() <= arity, "oversaturated source AP");
                if captures.len() == arity {
                    invoke(captures)
                } else {
                    Self::pap(invoke, arity, captures)
                }
            }
            Ok(_) => panic!("tried to apply a non-function Lean value"),
            Err(shared) => Self(shared, logical).apply1(arg),
        }
    }
}

impl PartialEq for __LeanValue {
    fn eq(&self, other: &Self) -> bool {
        self.assert_not_erased();
        other.assert_not_erased();
        use __LeanValueRepr::*;
        match (self.0.as_ref(), other.0.as_ref()) {
            (Nat(a), Nat(b)) | (Int(a), Int(b)) =>
                unsafe { __gmpz_cmp(a.ptr(), b.ptr()) == 0 },
            // Lean's small Nat is an immediate tagged value. A source Nat
            // may also be produced by an arbitrary-precision GMP primitive.
            // Compare numeric meaning, not just the Rust storage variant.
            (Tagged(_), Nat(_)) | (Nat(_), Tagged(_)) => self.nat_cmp(other) == 0,
            (Str(a), Str(b)) => a == b,
            (Array(a), Array(b)) | (List(a), List(b)) => a == b,
            (Tagged(a), Tagged(b)) => a == b,
            (U8(a), U8(b)) => a == b,
            (U16(a), U16(b)) => a == b,
            (U32(a), U32(b)) => a == b,
            (U64(a), U64(b)) => a == b,
            (USize(a), USize(b)) => a == b,
            (Ctor {tag:a, name:an, fields:af}, Ctor {tag:b, name:bn, fields:bf}) =>
                a == b && an == bn && af == bf,
            (PullIn {fields:a, bytes:ab}, PullIn {fields:b, bytes:bb}) =>
                a == b && ab == bb,
            (Closure { .. }, Closure { .. })
            | (Closure2 { .. }, Closure2 { .. })
            | (Closure3 { .. }, Closure3 { .. })
            | (Closure { .. }, Closure2 { .. })
            | (Closure2 { .. }, Closure { .. })
            | (Closure { .. }, Closure3 { .. })
            | (Closure3 { .. }, Closure { .. })
            | (Closure2 { .. }, Closure3 { .. })
            | (Closure3 { .. }, Closure2 { .. }) => std::rc::Rc::ptr_eq(&self.0, &other.0),
            _ => false,
        }
    }
}
impl Eq for __LeanValue {}
