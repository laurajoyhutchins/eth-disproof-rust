/* Independent C oracle: original compiled Lean make/observe and exact
 * Reader-generated Rust make/first/observe against the SAME Lean C runtime.
 * The Rust code is not hand-translated; see check-generated-heap.sh.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
extern lean_obj_res l_RuntimeHeap_make(lean_obj_arg, lean_obj_arg);
extern lean_obj_res l_RuntimeHeap_observe(lean_obj_arg, lean_obj_arg);
extern lean_obj_res lr_heap_generated_make(lean_obj_arg, lean_obj_arg);
extern lean_obj_res lr_heap_generated_first(lean_obj_arg);
extern lean_obj_res lr_heap_generated_observe(lean_obj_arg, lean_obj_arg);

static int valid_pair(lean_object* x, size_t a, size_t b) {
    if (!lean_is_ctor(x) || lean_obj_tag(x) != 1 || lean_ctor_num_objs(x) != 2)
        return 0;
    lean_object* l = lean_ctor_get(x, 0);
    lean_object* r = lean_ctor_get(x, 1);
    return lean_is_scalar(l) && lean_is_scalar(r) &&
           lean_unbox(l) == a && lean_unbox(r) == b;
}

static int source_rc(lean_object* x) {
    return lean_is_st(x) ? lean_internal_get_rc(x) : -1;
}

lean_obj_res lr_heap_compare(lean_obj_arg a, lean_obj_arg b) {
    if (!lean_is_scalar(a) || !lean_is_scalar(b)) return lean_box(2);
    size_t x = lean_unbox(a), y = lean_unbox(b);
    lean_object *original = l_RuntimeHeap_make(lean_box(x), lean_box(y));
    lean_object *generated = lr_heap_generated_make(lean_box(x), lean_box(y));
    int result = 0;
    if (!valid_pair(original, x, y) || !valid_pair(generated, x, y) ||
        original == generated || source_rc(original) != 1 ||
        source_rc(generated) != 1 ||
        !lean_is_exclusive(original) || !lean_is_exclusive(generated)) {
        result = 3; goto cleanup;
    }
    lean_inc(original);
    lean_inc(generated);
    if (source_rc(original) != 2 || source_rc(generated) != 2 ||
        lean_is_exclusive(original) || lean_is_exclusive(generated)) {
        result = 4; goto cleanup_shared;
    }
cleanup_shared:
    lean_dec(original);
    lean_dec(generated);
    if (result != 0) goto cleanup;
    if (source_rc(original) != 1 || source_rc(generated) != 1 ||
        !lean_is_exclusive(original) || !lean_is_exclusive(generated)) {
        result = 5; goto cleanup;
    }
    lean_object* from_source = l_RuntimeHeap_observe(lean_box(x), lean_box(y));
    lean_object* from_emitted = lr_heap_generated_observe(lean_box(x), lean_box(y));
    if (!lean_is_scalar(from_source) || !lean_is_scalar(from_emitted) ||
        lean_unbox(from_source) != x || lean_unbox(from_emitted) != x) {
        result = 6;
    }
    lean_dec(from_source);
    lean_dec(from_emitted);
    if (result != 0) goto cleanup;
    // This consumes one owned reference of the emitted root. The source
    // RC transitions inside the exact generated projection remain observable.
    lean_object* projected = lr_heap_generated_first(generated);
    generated = NULL;
    if (!lean_is_scalar(projected) || lean_unbox(projected) != x) result = 7;
    lean_dec(projected);
cleanup:
    lean_dec(original);
    if (generated) lean_dec(generated);
    return lean_box(result);
}
