// Physical Lean C execution backend for a tiny, explicitly admitted IR subset.
// Select via Cargo feature lean-c-runtime or the equivalent rustc --cfg. Not general G1.
// The emitter's source expressions are identical in both runtime builds.
#[allow(unexpected_cfgs)]
#[cfg(feature = "lean-c-runtime")]
#[repr(C)]
pub struct __LeanCObject { _opaque: [u8; 0] }

#[allow(unexpected_cfgs)]
#[cfg(feature = "lean-c-runtime")]
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

#[allow(unexpected_cfgs)]
#[cfg(feature = "lean-c-runtime")]
#[derive(Debug)]
struct __LeanCSlot {
    ptr: std::ptr::NonNull<__LeanCObject>,
    // These are *owned credits held by this wrapper*, not a simulated Lean
    // RC. Every transition is sent to the original Lean C implementation.
    credits: std::cell::Cell<usize>,
    // A projection borrows the original C field: a weak parent tracking
    // source liveness, never an extra Lean C reference.
    parent: Option<std::rc::Weak<__LeanCSlot>>,
    // The source's borrowed C argument is live only for this FFI call.
    // It does NOT contribute an owned refcount credit or a Lean dec.
    external_borrow: bool,
}

#[allow(unexpected_cfgs)]
#[cfg(feature = "lean-c-runtime")]
impl Drop for __LeanCSlot {
    fn drop(&mut self) {
        while self.credits.get() != 0 {
            self.credits.set(self.credits.get() - 1);
            unsafe { lr_exec_dec(self.ptr.as_ptr()) };
        }
    }
}

#[allow(unexpected_cfgs)]
#[cfg(feature = "lean-c-runtime")]
#[derive(Debug)]
pub struct __LeanValue(std::rc::Rc<__LeanCSlot>);

#[allow(unexpected_cfgs)]
#[cfg(feature = "lean-c-runtime")]
#[allow(dead_code)]
impl __LeanValue {
    /// The caller transfers precisely one live Lean reference. No retained
    /// count can be inferred from Rust pointer aliases.
    pub unsafe fn from_owned_raw(ptr: *mut __LeanCObject) -> Self {
        let ptr = std::ptr::NonNull::new(ptr).expect("null Lean source value");
        Self(std::rc::Rc::new(__LeanCSlot {
            ptr, credits: std::cell::Cell::new(1), parent: None,
            external_borrow: false,
        }))
    }

    /// Unboxed original Lean C functions can take a borrowed object argument.
    /// This wrapper is valid only while the C caller holds the source object
    /// live. In particular, Rust Drop must NOT invent a source decrement.
    /// A returned owned object still requires an explicit source IR inc.
    pub unsafe fn from_borrowed_raw(ptr: *mut __LeanCObject) -> Self {
        let ptr = std::ptr::NonNull::new(ptr).expect("null borrowed Lean source value");
        Self(std::rc::Rc::new(__LeanCSlot {
            ptr, credits: std::cell::Cell::new(0), parent: None,
            external_borrow: true,
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

    fn slot_live(slot: &__LeanCSlot) -> bool {
        slot.credits.get() > 0 || slot.external_borrow ||
            slot.parent.as_ref()
                .and_then(std::rc::Weak::upgrade)
                .is_some_and(|owner| Self::slot_live(&owner))
    }

    fn readable(&self) {
        // Check the source-credit chain BEFORE dereferencing a borrowed C
        // pointer. A compiler_alias or Rust Rc strong reference is not a
        // source-owned credit, and cannot revive a freed child.
        assert!(Self::slot_live(&self.0), "Lean C value used after source release");
    }

    fn into_transferred_field(self) -> *mut __LeanCObject {
        self.readable();
        let old = self.0.credits.get();
        let new = old.checked_sub(1)
            .expect("source constructor field missing owned transfer credit");
        let ptr = self.raw();
        // The parent now owns this exact source credit. Neither a Rust Drop
        // nor an invented lean_inc/lean_dec may accompany the transfer.
        self.0.credits.set(new);
        ptr
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
        if !matches!(name, "RuntimeHeap.Pair.mk" | "RuntimeHeap.Box.mk")
            || self.scalar() { return false; }
        usize::try_from(unsafe { lr_exec_tag(self.raw()) }).ok() == Some(tag)
            && unsafe { lr_exec_arity(self.raw()) } == arity
    }

    fn field(&self, n: usize) -> Self {
        self.readable();
        assert!(!self.scalar(), "field projection from scalar");
        let field = unsafe { lr_exec_field(self.raw(), n) };
        assert!(!field.is_null(), "missing Lean C constructor field");
        if unsafe { lr_exec_is_scalar(field) } != 0 {
            // Tagged immediate fields have no physical refcount.
            return Self::tagged(unsafe { lr_exec_unbox(field) });
        }
        // The C pointer is borrowed. No increment is performed here.
        // Generated Lean IR must issue source_inc before this field can be
        // returned as an owned object across parent release.
        Self(std::rc::Rc::new(__LeanCSlot {
            ptr: std::ptr::NonNull::new(field).expect("null Lean C field"),
            credits: std::cell::Cell::new(0),
            parent: Some(std::rc::Rc::downgrade(&self.0)),
            external_borrow: false,
        }))
    }

    fn ctor(tag: usize, name: &'static str, fields: Vec<Self>) -> Self {
        assert!(
            matches!((tag, name, fields.len()),
                (1, "RuntimeHeap.Pair.mk", 2) | (1, "RuntimeHeap.Box.mk", 2)),
            "unsupported Lean C constructor family or layout"
        );
        // Each source field contributes one owned reference to the new C
        // constructor. Heap children are not cloned or incremented here.
        let mut owned = fields.into_iter();
        let a = owned.next().expect("first field").into_transferred_field();
        let b = owned.next().expect("second field").into_transferred_field();
        let ptr = unsafe { lr_exec_ctor2(tag as u8, a, b) };
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
