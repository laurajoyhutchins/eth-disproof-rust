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

/* Convert a borrowed arbitrary-precision Lean Nat to decimal without peeking
 * into Lean's internal big-number representation. This uses the public
 * lean_nat_{div,mod} accessors from the exactly pinned lean.h and owns only
 * its temporary quotient/remainder objects. Call lr_free_string on success.
 * The bound is deliberately conservative: compiler constants above 4 KiB
 * of bigint storage are refused rather than materialized accidentally.
 */
#include <stdlib.h>
char *lr_nat_decimal(b_lean_obj_arg n) {
    if (!n) return NULL;
    size_t bytes = lean_nat_size_in_bytes(n);
    if (bytes > 4096 || bytes > (SIZE_MAX - 8) / 3) return NULL;
    size_t cap = bytes * 3 + 8;
    char *digits = malloc(cap);
    if (!digits) return NULL;
    lean_object *cur = (lean_object *) n;
    lean_inc(cur);
    size_t len = 0;
    while (!lean_nat_eq(cur, lean_box(0))) {
        lean_object *r = lean_nat_mod(cur, lean_box(10));
        size_t digit = lean_is_scalar(r) ? lean_unbox(r) : lean_uint64_of_nat(r);
        lean_dec(r);
        if (digit > 9 || len >= cap - 1) {
            lean_dec(cur);
            free(digits);
            return NULL;
        }
        digits[len++] = (char) ('0' + digit);
        lean_object *next = lean_nat_div(cur, lean_box(10));
        lean_dec(cur);
        cur = next;
    }
    lean_dec(cur);
    if (len == 0) digits[len++] = '0';
    for (size_t i = 0; i < len / 2; i++) {
        char swap = digits[i];
        digits[i] = digits[len - 1 - i];
        digits[len - 1 - i] = swap;
    }
    digits[len] = 0;
    return digits;
}
void lr_free_string(char *ptr) { free(ptr); }
