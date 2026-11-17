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


/* Nested source-generated destructor and retained projection comparison.
 * The source Lean compiler and Reader see the SAME original definitions.
 * A shared parent forces an owned child projection, and the child must
 * survive release of the final parent-owned reference.
 */
extern lean_obj_res l_RuntimeHeap_nest(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res l_RuntimeHeap_payload(lean_obj_arg);
extern lean_obj_res l_RuntimeHeap_nestedFirst(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res lr_heap_generated_nest(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res lr_heap_generated_payload(lean_obj_arg);
extern lean_obj_res lr_heap_generated_nested_first(lean_obj_arg, lean_obj_arg, lean_obj_arg);

static int valid_nested(lean_object *parent, size_t a, size_t b, size_t stamp) {
    if (!lean_is_ctor(parent) || lean_obj_tag(parent) != 1 ||
        lean_ctor_num_objs(parent) != 2) return 0;
    lean_object *child = lean_ctor_get(parent, 0);
    lean_object *label = lean_ctor_get(parent, 1);
    return valid_pair(child, a, b) && lean_is_scalar(label) &&
           lean_unbox(label) == stamp && source_rc(parent) == 1 &&
           source_rc(child) == 1 && lean_is_exclusive(child);
}

lean_obj_res lr_heap_compare_nested(lean_obj_arg a, lean_obj_arg b, lean_obj_arg stamp) {
    if (!lean_is_scalar(a) || !lean_is_scalar(b) || !lean_is_scalar(stamp))
        return lean_box(2);
    size_t x = lean_unbox(a), y = lean_unbox(b), n = lean_unbox(stamp);
    lean_object *original = l_RuntimeHeap_nest(lean_box(x), lean_box(y), lean_box(n));
    lean_object *emitted = lr_heap_generated_nest(lean_box(x), lean_box(y), lean_box(n));
    int status = 0;
    if (!valid_nested(original, x, y, n) || !valid_nested(emitted, x, y, n) ||
        original == emitted) { status = 3; goto finish; }
    lean_object *old_child = lean_ctor_get(original, 0);
    lean_object *new_child = lean_ctor_get(emitted, 0);

    /* The projection consumes one reference of a shared parent. Its
     * independent owned child reference must therefore be retained.
     * Observe the physical child RC before and after parent release. */
    lean_inc(original);
    lean_inc(emitted);
    if (source_rc(original) != 2 || source_rc(emitted) != 2) {
        status = 4; goto finish_shared;
    }
    lean_object *old_projected = l_RuntimeHeap_payload(original);
    lean_object *new_projected = lr_heap_generated_payload(emitted);
    /* Both calls consume exactly one of the two original parent credits. */
    if (old_projected != old_child || new_projected != new_child ||
        source_rc(original) != 1 || source_rc(emitted) != 1 ||
        source_rc(old_projected) != 2 || source_rc(new_projected) != 2) {
        if (old_projected != old_child) status = 51;
        else if (new_projected != new_child) status = 52;
        else if (source_rc(original) != 1) status = 60 + source_rc(original);
        else if (source_rc(emitted) != 1) status = 70 + source_rc(emitted);
        else if (source_rc(old_projected) != 2) status = 80 + source_rc(old_projected);
        else status = 90 + source_rc(new_projected);
    }
    lean_dec(original);
    lean_dec(emitted);
    original = NULL;
    emitted = NULL;
    if (status == 0 && (source_rc(old_projected) != 1 ||
        source_rc(new_projected) != 1 ||
        !valid_pair(old_projected, x, y) ||
        !valid_pair(new_projected, x, y))) status = 6;
    lean_dec(old_projected);
    lean_dec(new_projected);
    if (status != 0) return lean_box(status);

    /* Unique parent now exercises the source's shell-reuse/destruction
     * branch. No borrowed child may dangle or acquire an invented retain. */
    original = l_RuntimeHeap_nest(lean_box(x), lean_box(y), lean_box(n));
    emitted = lr_heap_generated_nest(lean_box(x), lean_box(y), lean_box(n));
    old_child = lean_ctor_get(original, 0);
    new_child = lean_ctor_get(emitted, 0);
    old_projected = l_RuntimeHeap_payload(original);
    new_projected = lr_heap_generated_payload(emitted);
    original = NULL;
    emitted = NULL;
    if (old_projected != old_child || new_projected != new_child ||
        source_rc(old_projected) != 1 || source_rc(new_projected) != 1 ||
        !valid_pair(old_projected, x, y) ||
        !valid_pair(new_projected, x, y)) status = 7;
    lean_dec(old_projected);
    lean_dec(new_projected);
    if (status != 0) return lean_box(status);

    lean_object *source_value =
        l_RuntimeHeap_nestedFirst(lean_box(x), lean_box(y), lean_box(n));
    lean_object *rust_value =
        lr_heap_generated_nested_first(lean_box(x), lean_box(y), lean_box(n));
    if (!lean_is_scalar(source_value) || !lean_is_scalar(rust_value) ||
        lean_unbox(source_value) != x || lean_unbox(rust_value) != x) status = 8;
    lean_dec(source_value);
    lean_dec(rust_value);
    return lean_box(status);

finish_shared:
    /* Retain/release imbalance is a failing test, never a receipt. */
    lean_dec(original); lean_dec(emitted);
finish:
    lean_dec(original); lean_dec(emitted);
    return lean_box(status);
}
