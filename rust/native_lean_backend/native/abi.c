/* Thin accessors: let Lean's exact-version lean.h own its tagged-object layout.
 * All references are borrowed; this file never mutates or retains Lean objects.
 */
#include <lean/lean.h>
#include <stdint.h>

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
