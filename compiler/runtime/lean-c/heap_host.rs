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
    let p = unsafe { __LeanValue::from_owned_raw(pair) };
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
    let parent = unsafe { __LeanValue::from_owned_raw(parent) };
    payload(parent).into_raw_owned()
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
