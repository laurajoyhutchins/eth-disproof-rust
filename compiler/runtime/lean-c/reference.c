/* Independent original-Lean source compiled to C as the oracle.
 * Rust accesses the same pinned Lean C runtime via abi.c, not via Rust Rc.
 */
#include <lean/lean.h>
#include <stdint.h>
extern lean_obj_res l_OwnershipObjectTrace_create(lean_obj_arg);
extern uint64_t lr_rust_lean_c_trace(size_t);

static uint64_t original_lean_trace(size_t n) {
    lean_object *node = l_OwnershipObjectTrace_create(lean_box(n));
    uint64_t mask = 0;
    if (!lean_is_scalar(node)) mask |= 1;
    if (lean_is_ctor(node) && lean_obj_tag(node) == 1) mask |= 2;
    if (lean_is_ctor(node) && lean_ctor_num_objs(node) == 2) mask |= 4;
    if (lean_is_ctor(node) && lean_is_scalar(lean_ctor_get(node, 0)) &&
        lean_unbox(lean_ctor_get(node, 0)) == n) mask |= 8;
    if (lean_is_ctor(node) && lean_is_scalar(lean_ctor_get(node, 1)) &&
        lean_unbox(lean_ctor_get(node, 1)) == n + 1) mask |= 16;
    if (lean_is_st(node) && lean_internal_get_rc(node) == 1) mask |= 32;

    lean_inc(node);
    if (lean_is_st(node) && lean_internal_get_rc(node) == 2) mask |= 64;
    if (!lean_is_exclusive(node)) mask |= 128;
    lean_dec(node);
    if (lean_is_st(node) && lean_internal_get_rc(node) == 1) mask |= 256;
    if (lean_is_exclusive(node)) mask |= 512;
    lean_dec(node);
    return mask;
}

/* Lean's own IO/main owns the runtime lifecycle. Return 0 only if both
 * independent paths observe the same complete physical checkpoint mask.
 */
lean_obj_res lr_runtime_crosscheck(lean_obj_arg n_obj) {
    if (!lean_is_scalar(n_obj)) { lean_dec(n_obj); return lean_box(2); }
    size_t n = lean_unbox(n_obj);
    if (n >= (SIZE_MAX >> 2)) return lean_box(3);
    uint64_t original = original_lean_trace(n);
    uint64_t rust = lr_rust_lean_c_trace(n);
    return lean_box(original == 1023 && rust == original ? 0 : 1);
}
