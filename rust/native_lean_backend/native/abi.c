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
/* Lean 4.34.1 IR.Param has two pointer fields (x, ty) and a packed
 * Bool borrow flag following them. Do not infer borrowing from Rust clones.
 * A malformed source representation is explicitly rejected. */
int lr_param_borrow(b_lean_obj_arg o) {
    if (!o || !lean_is_ctor((lean_object *)o) ||
        lean_obj_tag((lean_object *)o) != 0 ||
        lean_ctor_num_objs((lean_object *)o) != 2) return -1;
    uint8_t value = lean_ctor_get_uint8((lean_object *)o, 2 * sizeof(void *));
    return value <= 1 ? (int)value : -1;
}

/* Pinned Lean 4.34.1 FnBody.inc/dec: three object fields and two
 * consecutive packed Bool flags, check and persistent. A persistent RC
 * operation is omitted by Lean's own LCNF C emitter. Fail closed if the
 * source constructor or packed values do not match the pinned layout. */
int lr_ir_rc_flags(b_lean_obj_arg o) {
    if (!o || !lean_is_ctor((lean_object *)o)) return -1;
    unsigned tag = lean_obj_tag((lean_object *)o);
    if ((tag != 6 && tag != 7) || lean_ctor_num_objs((lean_object *)o) != 3) return -1;
    uint8_t checked = lean_ctor_get_uint8((lean_object *)o, 3 * sizeof(void *));
    uint8_t persistent = lean_ctor_get_uint8((lean_object *)o, 3 * sizeof(void *) + 1);
    if (checked > 1 || persistent > 1) return -1;
    return (int)checked | ((int)persistent << 1);
}

size_t lr_array_len(b_lean_obj_arg o) { return o && lean_is_array((lean_object *)o) ? lean_array_size((lean_object *)o) : 0; }
b_lean_obj_res lr_array_at(b_lean_obj_arg o, size_t n) {
    if (!o || !lean_is_array((lean_object *)o) || n >= lean_array_size((lean_object *)o)) return NULL;
    return lean_array_get_core((lean_object *)o,n);
}
int lr_is_array(b_lean_obj_arg o) { return o && lean_is_array((lean_object *)o); }
int lr_is_string(b_lean_obj_arg o) { return o && lean_is_string((lean_object *)o); }
const char *lr_string_ptr(b_lean_obj_arg o) { return o && lean_is_string((lean_object *)o) ? lean_string_cstr((lean_object *)o) : NULL; }

/* Executed in the actual Lean host, not against a synthetic Rust layout.
 * The header supplies tag, scalar, ctor allocation and field access APIs.
 * Compiler-IR tag compatibility is separately exercised by the Lean fixtures.
 */
/* Independent pinned Lean C runtime control for source-owned reference
 * transitions through a direct call, both branch outcomes, and actual
 * partially applied closure calls. Each bit records !lean_is_exclusive(root).
 * No synthetic count or Rust Rc handle participates in this control.
 */
static void lr_rc_control_retain(lean_object *x) { lean_inc(x); }
static void lr_rc_control_branch_release(lean_object *x, int active) {
    if (active) lean_dec(x);
}
static lean_obj_res lr_rc_control_callback(lean_obj_arg captured, lean_obj_arg arg) {
    lean_dec(captured); /* apply_1 transfers one owned capture to the callee */
    lean_dec(arg);
    return lean_box(0);
}
static unsigned lr_source_rc_control_mask(void) {
    unsigned mask = 0;
    lean_object *root = lean_alloc_ctor(17, 0, 0);
#define LR_SAMPLE(bit) do { if (!lean_is_exclusive(root)) mask |= 1u << (bit); } while (0)
    LR_SAMPLE(0);                   /* one root owner */
    lr_rc_control_retain(root);
    LR_SAMPLE(1);                   /* direct call added owner */
    lr_rc_control_branch_release(root, 0);
    LR_SAMPLE(2);                   /* branch without release */
    lr_rc_control_branch_release(root, 1);
    LR_SAMPLE(3);                   /* branch released added owner */

    lean_inc(root);                 /* closure owns a root reference */
    lean_object *unique = lean_alloc_closure((void *)lr_rc_control_callback, 2, 1);
    lean_closure_set(unique, 0, root);
    LR_SAMPLE(4);                   /* capture */
    lean_object *ret = lean_apply_1(unique, lean_box(0));
    lean_dec(ret);
    LR_SAMPLE(5);                   /* unique closure consumed, capture released */

    lean_inc(root);
    lean_object *shared = lean_alloc_closure((void *)lr_rc_control_callback, 2, 1);
    lean_closure_set(shared, 0, root);
    lean_inc(shared);               /* retain a second closure reference */
    LR_SAMPLE(6);
    ret = lean_apply_1(shared, lean_box(0));
    lean_dec(ret);
    LR_SAMPLE(7);                   /* retained closure still holds capture */
    lean_dec(shared);
    LR_SAMPLE(8);                   /* final closure release frees capture */
    lean_dec(root);
#undef LR_SAMPLE
    return mask;
}

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
    /* Bits 1,2,4,6,7 are shared; all other checkpoints exclusive.
     * A compiler replacement must match the actual C runtime control.
     */
    good = good && lr_source_rc_control_mask() == 214u;
    lean_object *str = lean_mk_string("abi-probe");
    good = good && lean_is_string(str)
        && strcmp(lean_string_cstr(str), "abi-probe") == 0;
    lean_dec(str);
    return good;
}

/* Include terminating NUL in byte length so Rust can distinguish names with
 * embedded zeros rather than accepting a truncated declaration identity. */
size_t lr_string_size(b_lean_obj_arg o) { return o && lean_is_string((lean_object *)o) ? lean_string_size(o) : 0; }

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
