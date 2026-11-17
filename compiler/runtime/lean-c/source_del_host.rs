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

// A non-mutating refusal probe, independent from the Reader-generated
// source-del function. The C oracle uses this only on *unmodified*
// parent state to assert that unsafe shapes are not admitted.
#[no_mangle]
pub extern "C" fn lr_heap_source_del_shell_eligible(
    parent: *mut __LeanCObject,
) -> u8 {
    let owned = unsafe { __LeanValue::from_owned_raw(parent) };
    let child = owned.field(0);
    let eligible = owned.shell_del_child().is_some();
    drop(child);
    assert_eq!(owned.into_raw_owned(), parent);
    u8::from(eligible)
}
