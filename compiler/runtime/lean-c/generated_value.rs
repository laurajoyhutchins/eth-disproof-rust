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
    fn lr_exec_set_field(p: *mut __LeanCObject, index: usize, value: *mut __LeanCObject);
    fn lr_exec_del(p: *mut __LeanCObject);
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
    parent_index: Option<usize>,
    // A field's physical credit can be released before the parent shell
    // is recycled or deleted. Such a stale pointer must never be read
    // or decremented a second time.
    spent_fields: std::cell::RefCell<std::collections::BTreeSet<usize>>,
    released_projection: std::cell::Cell<bool>,
    erased: std::cell::Cell<bool>,
    // The source's borrowed C argument is live only for this FFI call.
    // It does NOT contribute an owned refcount credit or a Lean dec.
    external_borrow: bool,
    // Borrowed projections are weak handles, not physical Lean RC credits.
    borrowed_fields: std::cell::RefCell<Vec<(usize, std::rc::Weak<__LeanCSlot>)>>,
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
            parent_index: None,
            spent_fields: std::cell::RefCell::new(std::collections::BTreeSet::new()),
            released_projection: std::cell::Cell::new(false),
            erased: std::cell::Cell::new(false),
            external_borrow: false,
            borrowed_fields: std::cell::RefCell::new(Vec::new()),
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
            parent_index: None,
            spent_fields: std::cell::RefCell::new(std::collections::BTreeSet::new()),
            released_projection: std::cell::Cell::new(false),
            erased: std::cell::Cell::new(false),
            external_borrow: true,
            borrowed_fields: std::cell::RefCell::new(Vec::new()),
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
        !slot.released_projection.get() && !slot.erased.get() &&
        (slot.credits.get() > 0 || slot.external_borrow ||
            slot.parent.as_ref()
                .and_then(std::rc::Weak::upgrade)
                .is_some_and(|owner| Self::slot_live(&owner)))
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

    fn erased() -> Self {
        // Lean's erased join token is represented as scalar box(0), but
        // cannot be inspected as an ordinary Nat. Only source_del admits it.
        let token = Self::tagged(0);
        token.0.erased.set(true);
        token
    }

    fn require_constructor_object(self) -> Self {
        self.readable();
        assert!(!self.scalar(), "source join requires heap constructor");
        self
    }

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
        assert!(!self.0.spent_fields.borrow().contains(&n),
                "read of already released constructor field");
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
        let borrowed = Self(std::rc::Rc::new(__LeanCSlot {
            ptr: std::ptr::NonNull::new(field).expect("null Lean C field"),
            credits: std::cell::Cell::new(0),
            parent: Some(std::rc::Rc::downgrade(&self.0)),
            parent_index: Some(n),
            spent_fields: std::cell::RefCell::new(std::collections::BTreeSet::new()),
            released_projection: std::cell::Cell::new(false),
            erased: std::cell::Cell::new(false),
            external_borrow: false,
            borrowed_fields: std::cell::RefCell::new(Vec::new()),
        }));
        self.0.borrowed_fields.borrow_mut()
            .push((n, std::rc::Rc::downgrade(&borrowed.0)));
        borrowed
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

    // The compiler proves this exceptional field credit using its
    // original Box.mk case, isShared(false) branch, and join analysis.
    // The runtime independently verifies physical exclusivity and the
    // exact old stamp slot. It performs NO lean_inc.
    fn adopt_exclusive_box_stamp(&self) {
        assert!(!self.0.external_borrow && self.0.credits.get() == 0,
                "borrowed stamp already owns a source credit");
        let parent = self.0.parent.as_ref().and_then(std::rc::Weak::upgrade)
            .expect("stamp release requires live parent");
        assert_eq!(self.0.parent_index, Some(1), "only Box stamp slot admitted");
        assert_eq!(parent.credits.get(), 1, "parent is not source-unique");
        assert!(!parent.external_borrow && !parent.erased.get(), "invalid parent owner");
        let raw = parent.ptr.as_ptr();
        assert!(unsafe { lr_exec_exclusive(raw) } != 0, "parent physically shared");
        assert_eq!(unsafe { lr_exec_tag(raw) }, 1, "stamp parent tag mismatch");
        assert_eq!(unsafe { lr_exec_arity(raw) }, 2, "stamp parent arity mismatch");
        assert_eq!(unsafe { lr_exec_field(raw, 1) }, self.raw(), "stamp slot identity mismatch");
        assert!(!parent.spent_fields.borrow().contains(&1), "stamp slot already released");
        let live_stamp_views = parent.borrowed_fields.borrow().iter()
            .filter(|(index, view)| *index == 1 && view.upgrade().is_some())
            .count();
        assert_eq!(live_stamp_views, 1, "ambiguous borrowed stamp owner");
        parent.spent_fields.borrow_mut().insert(1);
        self.0.credits.set(1);
    }

    fn source_dec(&self, n: usize, checked: bool, persistent: bool) {
        self.readable();
        assert!(!persistent, "persistent Lean ownership not verified");
        if self.scalar() {
            assert!(checked, "unchecked source dec of tagged immediate");
            return;
        }
        assert_eq!(n, 1, "only source dec(1) admitted");
        let transferred = self.0.credits.get() == 0;
        if transferred {
            assert!(checked, "unchecked projection credit transfer");
            self.adopt_exclusive_box_stamp();
        }
        let current = self.0.credits.get();
        self.0.credits.set(current.checked_sub(1).expect("source ownership underflow"));
        if transferred {
            self.0.released_projection.set(true);
        }
        unsafe { lr_exec_dec(self.raw()) };
    }

    // Bounded FnBody.del primitive: Box.mk has one heap Pair in field 0
    // and one tagged immediate field. The shell must be unique, and an
    // existing projection receives the parent's child-owned credit.
    // No source increment or recursive child destructor is performed.
    fn shell_del_child(&self) -> Option<std::rc::Rc<__LeanCSlot>> {
        if self.scalar() || self.0.external_borrow || self.0.credits.get() != 1 {
            return None;
        }
        if unsafe { lr_exec_rc(self.raw()) } != 1 ||
           unsafe { lr_exec_tag(self.raw()) } != 1 ||
           unsafe { lr_exec_arity(self.raw()) } != 2 {
            return None;
        }
        let first = unsafe { lr_exec_field(self.raw(), 0) };
        let second = unsafe { lr_exec_field(self.raw(), 1) };
        // A heap-valued stamp may already have been physically released
        // by source_dec on the exclusive reset path. Do not dereference
        // its now-stale pointer; shell deletion cannot release it again.
        let stamp_spent = self.0.spent_fields.borrow().contains(&1);
        if first.is_null() || second.is_null() ||
           unsafe { lr_exec_is_scalar(first) } != 0 ||
           (!stamp_spent && unsafe { lr_exec_is_scalar(second) } == 0) {
            return None;
        }
        let projections: Vec<_> = self.0.borrowed_fields.borrow().iter()
            .filter(|(index, _)| *index == 0)
            .filter_map(|(_, child)| child.upgrade()).collect();
        if projections.len() != 1 { return None; }
        let child = std::rc::Rc::clone(&projections[0]);
        if child.ptr.as_ptr() != first || child.credits.get() != 0 ||
           child.external_borrow || unsafe { lr_exec_rc(first) } != 1 {
            return None;
        }
        Some(child)
    }

    fn source_del(&self) {
        if self.0.erased.get() || self.scalar() {
            // lean_del_object(box(0)) is a no-op; no source credit.
            return;
        }
        self.readable();
        let child = self.shell_del_child().expect(
            "source del refused: unique owned Box shell and one live unretained child required"
        );
        // Transfer the source credit held by the parent field. No lean_inc.
        child.credits.set(1);
        self.0.credits.set(0);
        self.0.spent_fields.borrow_mut().clear();
        unsafe { lr_exec_del(self.raw()) };
    }

    fn with_field(self, index: usize, value: Self) -> Self {
        self.readable();
        assert_eq!(index, 1, "only boxed stamp reuse admitted");
        assert!(!self.scalar(), "constructor field set on non-constructor");
        assert_eq!(self.0.credits.get(), 1, "reuse requires one source parent credit");
        assert!(unsafe { lr_exec_exclusive(self.raw()) } != 0, "cannot reuse shared Box");
        assert_eq!(unsafe { lr_exec_tag(self.raw()) }, 1, "reuse requires Box.mk");
        assert_eq!(unsafe { lr_exec_arity(self.raw()) }, 2, "reuse requires two fields");
        let old = unsafe { lr_exec_field(self.raw(), 1) };
        let was_spent = self.0.spent_fields.borrow().contains(&1);
        assert!(was_spent || unsafe { lr_exec_is_scalar(old) } != 0,
                "heap stamp must be released before replacement");
        let transferred = value.into_transferred_field();
        unsafe { lr_exec_set_field(self.raw(), 1, transferred) };
        self.0.spent_fields.borrow_mut().remove(&1);
        for (slot, view) in self.0.borrowed_fields.borrow().iter() {
            if *slot == 1 {
                if let Some(view) = view.upgrade() {
                    view.released_projection.set(true);
                }
            }
        }
        self
    }

    fn nat_cmp(&self, other: &Self) -> i32 {
        self.readable();
        other.readable();
        assert!(self.scalar() && other.scalar(),
                "physical Lean C Nat comparison beyond tagged inputs unsupported");
        let a = unsafe { lr_exec_unbox(self.raw()) };
        let b = unsafe { lr_exec_unbox(other.raw()) };
        i32::from(a > b) - i32::from(a < b)
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
