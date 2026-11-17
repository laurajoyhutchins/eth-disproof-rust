// Physical Lean C execution backend for a tiny, explicitly admitted IR subset.
// Selected by rustc --cfg lean_c_runtime. Not a replacement for general G1.
// The emitter's source expressions are identical in both runtime builds.
#[cfg(lean_c_runtime)]
#[repr(C)]
pub struct __LeanCObject { _opaque: [u8; 0] }

#[cfg(lean_c_runtime)]
unsafe extern "C" {
    fn lr_exec_box_small(n: usize) -> *mut __LeanCObject;
    fn lr_exec_ctor2(tag: u8, a: *mut __LeanCObject, b: *mut __LeanCObject) -> *mut __LeanCObject;
    fn lr_exec_inc(p: *mut __LeanCObject);
    fn lr_exec_dec(p: *mut __LeanCObject);
    fn lr_exec_is_scalar(p: *const __LeanCObject) -> i32;
    fn lr_exec_unbox(p: *const __LeanCObject) -> usize;
    fn lr_exec_tag(p: *const __LeanCObject) -> i32;
    fn lr_exec_arity(p: *const __LeanCObject) -> usize;
    fn lr_exec_field(p: *const __LeanCObject, index: usize) -> *mut __LeanCObject;
    fn lr_exec_rc(p: *const __LeanCObject) -> u64;
    fn lr_exec_exclusive(p: *const __LeanCObject) -> i32;
}

#[cfg(lean_c_runtime)]
#[derive(Debug)]
struct __LeanCSlot {
    ptr: std::ptr::NonNull<__LeanCObject>,
    // These are *owned credits held by this wrapper*, not a simulated Lean
    // RC. Every transition is sent to the original Lean C implementation.
    credits: std::cell::Cell<usize>,
}

#[cfg(lean_c_runtime)]
impl Drop for __LeanCSlot {
    fn drop(&mut self) {
        while self.credits.get() != 0 {
            self.credits.set(self.credits.get() - 1);
            unsafe { lr_exec_dec(self.ptr.as_ptr()) };
        }
    }
}

#[cfg(lean_c_runtime)]
#[derive(Debug)]
pub struct __LeanValue(std::rc::Rc<__LeanCSlot>);

#[cfg(lean_c_runtime)]
#[allow(dead_code)]
impl __LeanValue {
    /// The caller transfers precisely one live Lean reference. No retained
    /// count can be inferred from Rust pointer aliases.
    pub unsafe fn from_owned_raw(ptr: *mut __LeanCObject) -> Self {
        let ptr = std::ptr::NonNull::new(ptr).expect("null Lean source value");
        Self(std::rc::Rc::new(__LeanCSlot {
            ptr, credits: std::cell::Cell::new(1),
        }))
    }

    /// The return-value ABI transfers one owned source credit to Lean C.
    pub fn into_raw_owned(self) -> *mut __LeanCObject {
        let slot = std::rc::Rc::try_unwrap(self.0)
            .expect("Lean C return still has an outstanding Rust alias");
        assert_eq!(slot.credits.get(), 1, "expected exactly one source ownership credit");
        let ptr = slot.ptr.as_ptr();
        slot.credits.set(0);
        ptr
    }

    fn raw(&self) -> *mut __LeanCObject { self.0.ptr.as_ptr() }
    fn scalar(&self) -> bool { unsafe { lr_exec_is_scalar(self.raw()) != 0 } }

    fn readable(&self) {
        assert!(self.0.credits.get() != 0, "Lean C value used after source release");
    }

    // The emitter's compiler_alias does not correspond to a source IR.inc.
    fn compiler_alias(&self) -> Self { Self(std::rc::Rc::clone(&self.0)) }

    fn tagged(n: usize) -> Self {
        assert!(n <= usize::MAX >> 1, "Lean small Nat out of representable range");
        unsafe { Self::from_owned_raw(lr_exec_box_small(n)) }
    }

    fn has_tagged(&self, value: usize) -> bool {
        self.readable();
        self.scalar() && unsafe { lr_exec_unbox(self.raw()) } == value
    }

    fn tag(&self) -> usize {
        self.readable();
        if self.scalar() { unsafe { lr_exec_unbox(self.raw()) } }
        else { usize::try_from(unsafe { lr_exec_tag(self.raw()) }).expect("invalid Lean C tag") }
    }

    fn has_ctor(&self, tag: usize, name: &str, arity: usize) -> bool {
        self.readable();
        if name != "RuntimeHeap.Pair.mk" || self.scalar() { return false; }
        usize::try_from(unsafe { lr_exec_tag(self.raw()) }).ok() == Some(tag)
            && unsafe { lr_exec_arity(self.raw()) } == arity
    }

    fn field(&self, n: usize) -> Self {
        self.readable();
        assert!(!self.scalar(), "field projection from scalar");
        let field = unsafe { lr_exec_field(self.raw(), n) };
        assert!(!field.is_null(), "missing Lean C constructor field");
        assert!(unsafe { lr_exec_is_scalar(field) } != 0,
                "heap field projection requires source-bound retain proof");
        // Scalar projection does not add an owned heap reference in Lean.
        Self::tagged(unsafe { lr_exec_unbox(field) })
    }

    fn ctor(tag: usize, name: &'static str, fields: Vec<Self>) -> Self {
        assert_eq!((tag, name, fields.len()), (1, "RuntimeHeap.Pair.mk", 2),
                   "unsupported Lean C constructor family or layout");
        for field in &fields {
            field.readable();
            assert!(field.scalar(),
                "heap-child ownership transfer requires source IR proof");
        }
        let ptr = unsafe {
            lr_exec_ctor2(tag as u8, fields[0].raw(), fields[1].raw())
        };
        unsafe { Self::from_owned_raw(ptr) }
    }

    fn source_inc(&self, n: usize, checked: bool, persistent: bool) {
        self.readable();
        assert!(!persistent, "persistent Lean ownership not verified");
        if self.scalar() {
            assert!(checked, "unchecked source inc of tagged immediate");
            return;
        }
        let new = self.0.credits.get().checked_add(n).expect("source RC overflow");
        for _ in 0..n { unsafe { lr_exec_inc(self.raw()) }; }
        self.0.credits.set(new);
    }

    fn source_dec(&self, n: usize, checked: bool, persistent: bool) {
        self.readable();
        assert!(!persistent, "persistent Lean ownership not verified");
        if self.scalar() {
            assert!(checked, "unchecked source dec of tagged immediate");
            return;
        }
        assert_eq!(n, 1, "only source dec(1) admitted");
        let current = self.0.credits.get();
        self.0.credits.set(current.checked_sub(1).expect("source ownership underflow"));
        unsafe { lr_exec_dec(self.raw()) };
    }

    fn is_shared(&self) -> u8 {
        self.readable();
        assert!(!self.scalar(), "sharing a scalar is unsupported");
        u8::from(unsafe { lr_exec_exclusive(self.raw()) } == 0)
    }

    fn nat_to_decimal(&self) -> String {
        self.readable();
        assert!(self.scalar(), "large Lean Nat needs original C bignum admission");
        unsafe { lr_exec_unbox(self.raw()) }.to_string()
    }
}
