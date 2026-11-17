// C ABI glue only: call the unchanged Reader-generated source function.
// The third Lean parameter is borrowed. No reference count transition or
// shell-only deletion is written in this host.
#[no_mangle]
pub extern "C" fn lr_heap_generated_source_del_extract(
    parent: *mut __LeanCObject,
    stamp: *mut __LeanCObject,
    threshold: *mut __LeanCObject,
) -> *mut __LeanCObject {
    let original = unsafe { __LeanValue::from_owned_raw(parent) };
    let replacement = unsafe { __LeanValue::from_owned_raw(stamp) };
    let borrowed = unsafe { __LeanValue::from_borrowed_raw(threshold) };
    rebuildOrExtractByPayload(original, replacement, borrowed).into_raw_owned()
}
