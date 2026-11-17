//! FFI reference handles backed by the *actual* pinned Lean C runtime.
//! This is a runtime-boundary witness, not yet the generated IR emitter's runtime.
#![deny(unsafe_op_in_unsafe_fn)]
use std::{marker::PhantomData, ptr::NonNull};

#[repr(C)]
pub struct LeanObject {
    _opaque: [u8; 0],
}

unsafe extern "C" {
    fn lr_exec_box_small(n: usize) -> *mut LeanObject;
    fn lr_exec_ctor2(tag: u8, a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject;
    fn lr_exec_inc(p: *mut LeanObject);
    fn lr_exec_dec(p: *mut LeanObject);
    fn lr_exec_is_scalar(p: *const LeanObject) -> i32;
    fn lr_exec_unbox(p: *const LeanObject) -> usize;
    fn lr_exec_tag(p: *const LeanObject) -> i32;
    fn lr_exec_arity(p: *const LeanObject) -> usize;
    fn lr_exec_field(p: *const LeanObject, index: usize) -> *mut LeanObject;
    fn lr_exec_rc(p: *const LeanObject) -> u64;
    fn lr_exec_exclusive(p: *const LeanObject) -> i32;
}

/// An owned Lean reference. Rust Drop decrements Lean's *physical* source count.
/// The raw pointer must be returned by the pinned runtime with one owned credit.
pub struct Owned(NonNull<LeanObject>);

/// The field owner must remain alive until this borrowed reference is finished.
pub struct Borrowed<'a>(NonNull<LeanObject>, PhantomData<&'a Owned>);

impl Owned {
    /// Lean tagged small natural; deliberately refuse unrepresentable tags.
    pub fn small(n: usize) -> Self {
        assert!(n <= (usize::MAX >> 1), "tagged Lean Nat overflow");
        let p = unsafe { lr_exec_box_small(n) };
        Self(NonNull::new(p).expect("Lean tagged zero must be non-null"))
    }

    /// Constructor assumes ownership of the two incoming references, including
    /// any heap-backed fields. No additional inc is invented here.
    pub fn ctor2(tag: u8, a: Self, b: Self) -> Self {
        let first = a.0.as_ptr();
        let second = b.0.as_ptr();
        std::mem::forget(a);
        std::mem::forget(b);
        let p = unsafe { lr_exec_ctor2(tag, first, second) };
        Self(NonNull::new(p).expect("Lean allocator returned null"))
    }

    pub fn borrow(&self) -> Borrowed<'_> {
        Borrowed(self.0, PhantomData)
    }

    pub fn field(&self, n: usize) -> Option<Borrowed<'_>> {
        let p = unsafe { lr_exec_field(self.0.as_ptr(), n) };
        NonNull::new(p).map(|x| Borrowed(x, PhantomData))
    }

    pub fn is_heap(&self) -> bool {
        unsafe { lr_exec_is_scalar(self.0.as_ptr()) == 0 }
    }

    pub fn tag(&self) -> Option<u8> {
        let tag = unsafe { lr_exec_tag(self.0.as_ptr()) };
        u8::try_from(tag).ok()
    }

    pub fn arity(&self) -> Option<usize> {
        self.is_heap().then(|| unsafe { lr_exec_arity(self.0.as_ptr()) })
    }

    pub fn physical_rc(&self) -> Option<u64> {
        self.is_heap().then(|| unsafe { lr_exec_rc(self.0.as_ptr()) })
    }

    pub fn exclusive(&self) -> bool {
        unsafe { lr_exec_exclusive(self.0.as_ptr()) == 1 }
    }
}

impl<'a> Borrowed<'a> {
    pub fn small_value(&self) -> Option<usize> {
        (unsafe { lr_exec_is_scalar(self.0.as_ptr()) == 1 })
            .then(|| unsafe { lr_exec_unbox(self.0.as_ptr()) })
    }

    /// Retention crosses an explicit source-owned reference boundary.
    pub fn retain(&self) -> Owned {
        unsafe { lr_exec_inc(self.0.as_ptr()) };
        Owned(self.0)
    }
}

impl Drop for Owned {
    fn drop(&mut self) {
        unsafe { lr_exec_dec(self.0.as_ptr()) };
    }
}

/// Standalone Rust invocation using Lean C allocation, projection, retain and
/// release. This checks the adapter against the real original-Lean C result,
/// but is NOT a compiler-emitted Rust entry point.
#[no_mangle]
pub extern "C" fn lr_rust_lean_c_trace(n: usize) -> u64 {
    if n >= (usize::MAX >> 2) { return u64::MAX; }
    let node = Owned::ctor2(1, Owned::small(n), Owned::small(n + 1));
    let mut mask = 0u64;
    if node.is_heap() { mask |= 1; }
    if node.tag() == Some(1) { mask |= 2; }
    if node.arity() == Some(2) { mask |= 4; }
    if node.field(0).and_then(|b| b.small_value()) == Some(n) { mask |= 8; }
    if node.field(1).and_then(|b| b.small_value()) == Some(n + 1) { mask |= 16; }
    if node.physical_rc() == Some(1) { mask |= 32; }

    let alias = node.borrow().retain();
    if node.physical_rc() == Some(2) { mask |= 64; }
    if !node.exclusive() { mask |= 128; }
    drop(alias);
    if node.physical_rc() == Some(1) { mask |= 256; }
    if node.exclusive() { mask |= 512; }
    mask
}
