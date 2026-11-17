/* Execution-time adapter for Rust-owned Lean runtime handles.
 * Distinct from compiler/frontend/ffi/abi.c, which reads borrowed IR.
 * No synthetic Rust Rc count, replacement allocator or compiler fallback.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>

lean_obj_res lr_exec_box_small(size_t n) { return lean_box(n); }
lean_obj_res lr_exec_ctor2(uint8_t tag, lean_obj_arg a, lean_obj_arg b) {
    lean_object *node = lean_alloc_ctor(tag, 2, 0);
    lean_ctor_set(node, 0, a);
    lean_ctor_set(node, 1, b);
    return node;
}
void lr_exec_inc(lean_obj_arg p) { lean_inc(p); }
void lr_exec_dec(lean_obj_arg p) { lean_dec(p); }
/* FnBody.del is shell-only. The source must have transferred all children. */
void lr_exec_del(lean_obj_arg p) { lean_del_object(p); }
int lr_exec_is_scalar(b_lean_obj_arg p) {
    return p && lean_is_scalar((lean_object*)p) ? 1 : 0;
}
size_t lr_exec_unbox(b_lean_obj_arg p) { return lean_unbox((lean_object*)p); }
int lr_exec_tag(b_lean_obj_arg p) {
    return p && lean_is_ctor((lean_object*)p) ? (int)lean_obj_tag((lean_object*)p) : -1;
}
size_t lr_exec_arity(b_lean_obj_arg p) {
    return p && lean_is_ctor((lean_object*)p) ? lean_ctor_num_objs((lean_object*)p) : 0;
}
b_lean_obj_res lr_exec_field(b_lean_obj_arg p, size_t n) {
    if (!p || !lean_is_ctor((lean_object*)p) ||
        n >= lean_ctor_num_objs((lean_object*)p)) return NULL;
    return lean_ctor_get((lean_object*)p, (unsigned)n);
}
uint64_t lr_exec_rc(b_lean_obj_arg p) {
    if (!p || lean_is_scalar((lean_object*)p) || !lean_is_st((lean_object*)p))
        return UINT64_MAX;
    int rc = lean_internal_get_rc((lean_object*)p);
    return rc >= 1 ? (uint64_t)rc : UINT64_MAX;
}
int lr_exec_exclusive(b_lean_obj_arg p) {
    return p && !lean_is_scalar((lean_object*)p) &&
           lean_is_exclusive((lean_object*)p) ? 1 : 0;
}
