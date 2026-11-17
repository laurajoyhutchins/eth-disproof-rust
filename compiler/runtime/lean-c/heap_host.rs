// Host-only C ABI entry points. The implementations invoked here are the
// unmodified functions emitted from RuntimeHeapKernels.lean compiler IR.
#[no_mangle]
pub extern "C" fn lr_heap_generated_make(
    a: *mut __LeanCObject, b: *mut __LeanCObject,
) -> *mut __LeanCObject {
    let left = unsafe { __LeanValue::from_owned_raw(a) };
    let right = unsafe { __LeanValue::from_owned_raw(b) };
    make(left, right).into_raw_owned()
}
#[no_mangle]
pub extern "C" fn lr_heap_generated_first(
    pair: *mut __LeanCObject,
) -> *mut __LeanCObject {
    // Pinned C l_RuntimeHeap_first does not decrement its parent.
    let p = unsafe { __LeanValue::from_borrowed_raw(pair) };
    first(p).into_raw_owned()
}
#[no_mangle]
pub extern "C" fn lr_heap_generated_observe(
    a: *mut __LeanCObject, b: *mut __LeanCObject,
) -> *mut __LeanCObject {
    let left = unsafe { __LeanValue::from_owned_raw(a) };
    let right = unsafe { __LeanValue::from_owned_raw(b) };
    observe(left, right).into_raw_owned()
}


#[no_mangle]
pub extern "C" fn lr_heap_generated_nest(
    a: *mut __LeanCObject, b: *mut __LeanCObject, stamp: *mut __LeanCObject,
) -> *mut __LeanCObject {
    let left = unsafe { __LeanValue::from_owned_raw(a) };
    let right = unsafe { __LeanValue::from_owned_raw(b) };
    let label = unsafe { __LeanValue::from_owned_raw(stamp) };
    nest(left, right, label).into_raw_owned()
}

#[no_mangle]
pub extern "C" fn lr_heap_generated_payload(
    parent: *mut __LeanCObject,
) -> *mut __LeanCObject {
    // Original unboxed l_RuntimeHeap_payload borrows its parent and
    // calls lean_inc on the projected child. Its ___boxed wrapper, not
    // this unboxed function, performs the caller's final lean_dec.
    let parent = unsafe { __LeanValue::from_borrowed_raw(parent) };
    payload(parent).into_raw_owned()
}

// Explicit test-host primitive using the original compiler-emitted nest.
// The shell-only del here is not yet emitted by a source FnBody.del.
// Admission probe: no mutation, no source refcount change, no trap.
// The real source-del call still refuses if this eligibility test fails.
#[no_mangle]
pub extern "C" fn lr_heap_runtime_shell_eligible(
    parent: *mut __LeanCObject, project: u8,
) -> u8 {
    let owned = unsafe { __LeanValue::from_owned_raw(parent) };
    let child = if project != 0 { Some(owned.field(0)) } else { None };
    let allowed = owned.shell_del_child().is_some();
    drop(child);
    assert_eq!(owned.into_raw_owned(), parent);
    u8::from(allowed)
}

#[no_mangle]
pub extern "C" fn lr_heap_runtime_shell_take(
    parent: *mut __LeanCObject,
) -> *mut __LeanCObject {
    let owned = unsafe { __LeanValue::from_owned_raw(parent) };
    let child = owned.field(0);
    owned.source_del();
    child.into_raw_owned()
}

#[no_mangle]
pub extern "C" fn lr_heap_generated_nested_first(
    a: *mut __LeanCObject, b: *mut __LeanCObject, stamp: *mut __LeanCObject,
) -> *mut __LeanCObject {
    let left = unsafe { __LeanValue::from_owned_raw(a) };
    let right = unsafe { __LeanValue::from_owned_raw(b) };
    let label = unsafe { __LeanValue::from_owned_raw(stamp) };
    nestedFirst(left, right, label).into_raw_owned()
}
