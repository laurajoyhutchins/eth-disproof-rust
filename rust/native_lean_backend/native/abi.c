/* Thin accessors: let Lean's exact-version lean.h own its tagged-object layout.
 * All references are borrowed; this file never mutates or retains Lean objects.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

int lr_is_scalar(b_lean_obj_arg o) { return o != NULL && lean_is_scalar((lean_object *)o); }
size_t lr_scalar_value(b_lean_obj_arg o) { return lean_unbox((lean_object *)o); }
int lr_is_ctor(b_lean_obj_arg o) { return o != NULL && lean_is_ctor((lean_object *)o); }
int lr_tag(b_lean_obj_arg o) { return o != NULL && !lean_is_scalar((lean_object *)o) ? lean_obj_tag((lean_object *)o) : -1; }
size_t lr_field_count(b_lean_obj_arg o) { return o && lean_is_ctor((lean_object *)o) ? lean_ctor_num_objs((lean_object *)o) : 0; }
b_lean_obj_res lr_field(b_lean_obj_arg o, size_t n) {
    if (!o || !lean_is_ctor((lean_object *)o) || n >= lean_ctor_num_objs((lean_object *)o)) return NULL;
    return lean_ctor_get((lean_object *)o, (unsigned)n);
}
size_t lr_array_len(b_lean_obj_arg o) { return o && lean_is_array((lean_object *)o) ? lean_array_size((lean_object *)o) : 0; }
b_lean_obj_res lr_array_at(b_lean_obj_arg o, size_t n) {
    if (!o || !lean_is_array((lean_object *)o) || n >= lean_array_size((lean_object *)o)) return NULL;
    return lean_array_get_core((lean_object *)o,n);
}
int lr_is_array(b_lean_obj_arg o) { return o && lean_is_array((lean_object *)o); }
int lr_is_string(b_lean_obj_arg o) { return o && lean_is_string((lean_object *)o); }
const char *lr_string_ptr(b_lean_obj_arg o) { return o && lean_is_string((lean_object *)o) ? lean_string_cstr((lean_object *)o) : NULL; }
/* Includes all bytes before the trailing runtime terminator, even embedded NUL. */
size_t lr_string_bytes_len(b_lean_obj_arg o) { return o && lean_is_string((lean_object *)o) ? lean_string_size(o) - 1 : 0; }

/* Executed in the actual Lean host, not against a synthetic Rust layout.
 * The header supplies tag, scalar, ctor allocation and field access APIs.
 * Compiler-IR tag compatibility is separately exercised by the Lean fixtures.
 */
int lr_abi_probe(void) {
    lean_object *node = lean_alloc_ctor(17, 2, 0);
    lean_ctor_set(node, 0, lean_box(7));
    lean_ctor_set(node, 1, lean_box(9));
    int good = lean_is_ctor(node)
        && !lean_is_scalar(node)
        && lean_obj_tag(node) == 17
        && lean_ctor_num_objs(node) == 2
        && lean_is_scalar(lean_ctor_get(node, 0))
        && lean_unbox(lean_ctor_get(node, 0)) == 7
        && lean_unbox(lean_ctor_get(node, 1)) == 9;
    lean_dec(node);
    lean_object *str = lean_mk_string("abi-probe");
    good = good && lean_is_string(str)
        && strcmp(lean_string_cstr(str), "abi-probe") == 0;
    lean_dec(str);
    lean_object *embedded = lean_mk_string("x");
    embedded = lean_string_push(embedded, 0);
    embedded = lean_string_push(embedded, 'y');
    good = good && lean_string_size(embedded) == 4
        && memcmp(lean_string_cstr(embedded), "x\0y", 3) == 0;
    lean_dec(embedded);
    return good;
}
