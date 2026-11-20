/* Independent original-Lean-C versus exact Reader-generated Rust/C.
 * Both calls consume one parent and replacement Nat reference; the
 * threshold is borrowed. No source ownership operations are replaced by
 * equivalent-looking host code. Parent stamps may be heap Nat objects;
 * those tests additionally check actual reference-count transitions.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>

extern lean_obj_res l_RuntimeHeap_nest(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res l_RuntimeHeapDel_rebuildOrExtractByPayload(
    lean_obj_arg, lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res lr_heap_generated_source_del_extract(
    lean_obj_arg, lean_obj_arg, b_lean_obj_arg);
extern uint8_t lr_heap_source_del_shell_eligible(lean_obj_arg);
extern void lr_source_event_begin(unsigned, const char *, lean_object *,
                                   lean_object *, lean_object *);
extern void lr_source_event_end(void);

static int physical_rc(lean_object *p) {
    return p && !lean_is_scalar(p) && lean_is_st(p)
        ? lean_internal_get_rc(p) : -1;
}

static int pair_matches(lean_object* p, size_t a, size_t b) {
    if (!p || !lean_is_ctor(p) || lean_obj_tag(p) != 1 ||
        lean_ctor_num_objs(p) != 2) return 0;
    lean_object *left = lean_ctor_get(p, 0), *right = lean_ctor_get(p, 1);
    return lean_is_scalar(left) && lean_is_scalar(right) &&
        lean_unbox(left) == a && lean_unbox(right) == b;
}

/* The original compiler, not the test host, chooses whether to reuse,
 * delete a shell, increment a projection, or release the old stamp.
 * A result pointer must be the actual pre-existing child allocation.
 */
lean_obj_res lr_heap_compare_source_del(
    lean_obj_arg a, lean_obj_arg b, lean_obj_arg old_stamp,
    lean_obj_arg new_stamp, lean_obj_arg threshold, lean_obj_arg shared)
{
    if (!lean_is_scalar(a) || !lean_is_scalar(b) ||
        !lean_is_scalar(new_stamp) || !lean_is_scalar(threshold) ||
        !lean_is_scalar(shared))
        return lean_box(2);

    const int heap_stamp = !lean_is_scalar(old_stamp);
    // The Lean driver may retain additional references while iterating.
    // Observe the actual entry count, then require each parent credit to
    // change it by precisely one. Do not assume the caller holds only one.
    const int stamp_entry_rc = heap_stamp ? physical_rc(old_stamp) : -1;
    if (heap_stamp && stamp_entry_rc < 1) return lean_box(2);
    const size_t left = lean_unbox(a), right = lean_unbox(b);
    const size_t replacement = lean_unbox(new_stamp);
    const size_t test = lean_unbox(threshold), is_shared = lean_unbox(shared);
    if (is_shared > 1) return lean_box(2);

    // The C oracle receives one owned old_stamp reference. Give each
    // source-created Box a distinct *credit* to the same old stamp;
    // retain the caller's credit for before/after RC observation. These
    // two increments prepare independent parent references, not a
    // replacement for any source instruction in either function.
    lean_inc(old_stamp);
    lean_inc(old_stamp);
    lean_object *original = l_RuntimeHeap_nest(
        lean_box(left), lean_box(right), old_stamp);
    lean_object *generated = l_RuntimeHeap_nest(
        lean_box(left), lean_box(right), old_stamp);
    const int initial_stamp_rc = heap_stamp ? physical_rc(old_stamp) : -1;
    if (!lean_is_ctor(original) || !lean_is_ctor(generated) ||
        lean_obj_tag(original) != 1 || lean_obj_tag(generated) != 1 ||
        lean_ctor_num_objs(original) != 2 ||
        lean_ctor_num_objs(generated) != 2) {
        lean_dec(original);
        lean_dec(generated);
        lean_dec(old_stamp);
        return lean_box(3);
    }
    lean_object *original_child = lean_ctor_get(original, 0);
    lean_object *generated_child = lean_ctor_get(generated, 0);
    if (original == generated || original_child == generated_child ||
        !pair_matches(original_child, left, right) ||
        !pair_matches(generated_child, left, right) ||
        physical_rc(original) != 1 || physical_rc(generated) != 1 ||
        physical_rc(original_child) != 1 ||
        physical_rc(generated_child) != 1 ||
        !lean_is_exclusive(original) || !lean_is_exclusive(generated) ||
        (heap_stamp && initial_stamp_rc != stamp_entry_rc + 2)) {
        lean_dec(original);
        lean_dec(generated);
        lean_dec(old_stamp);
        return lean_box(4);
    }
    // A unique parent alone is not enough: an unspent *heap* stamp must
    // refuse shell deletion, as must a child with an independent owner.
    const uint8_t shell_admitted = lr_heap_source_del_shell_eligible(generated);
    if (shell_admitted != (heap_stamp ? 0 : 1)) {
        lean_dec(original);
        lean_dec(generated);
        lean_dec(old_stamp);
        return lean_box(13);
    }
    lean_inc(generated_child);
    if (lr_heap_source_del_shell_eligible(generated) != 0) {
        lean_dec(generated_child);
        lean_dec(original);
        lean_dec(generated);
        lean_dec(old_stamp);
        return lean_box(14);
    }
    lean_dec(generated_child);

    if (is_shared) {
        lean_inc(original);
        lean_inc(generated);
        if (physical_rc(original) != 2 || physical_rc(generated) != 2 ||
            lean_is_exclusive(original) || lean_is_exclusive(generated)) {
            lean_dec(original); lean_dec(original);
            lean_dec(generated); lean_dec(generated);
            lean_dec(old_stamp);
            return lean_box(5);
        }
    }
    // Observe eight disjoint branches (tagged/heap old stamp, shared/
    // unique parent, matching/mismatching payload) at their actual source
    // function boundaries. All 720 ordinary differential cases still run.
    // No source IR operation is performed by the host between begin/end.
    static unsigned selected_cases;
    const unsigned event_case = (heap_stamp ? 4u : 0u) |
        (is_shared ? 2u : 0u) | (test == left ? 1u : 0u);
    const unsigned event_bit = 1u << event_case;
    const int trace_this = left == 17 && right == 901 &&
        (heap_stamp || lean_unbox(old_stamp) == 17) &&
        !(selected_cases & event_bit);
    if (trace_this) selected_cases |= event_bit;
    // One owned parent reference is transferred to each original function.
    // No C host reset/reuse/del/dec acts on that reference.
    if (trace_this) lr_source_event_begin(
        event_case, "lean-c", original, original_child, old_stamp);
    lean_object *expected = l_RuntimeHeapDel_rebuildOrExtractByPayload(
        original, lean_box(replacement), lean_box(test));
    if (trace_this) lr_source_event_end();
    int status = 0;
    if (heap_stamp && physical_rc(old_stamp) !=
        (stamp_entry_rc + (is_shared ? 2 : 1)))
        status = 10;
    if (trace_this) lr_source_event_begin(
        event_case, "reader-rust", generated, generated_child, old_stamp);
    lean_object *actual = lr_heap_generated_source_del_extract(
        generated, lean_box(replacement), lean_box(test));
    if (trace_this) lr_source_event_end();
    if (heap_stamp && physical_rc(old_stamp) !=
        (stamp_entry_rc + (is_shared ? 2 : 0)))
        status = 11;
    if (expected != original_child || actual != generated_child ||
        expected == actual || !pair_matches(expected, left, right) ||
        !pair_matches(actual, left, right)) {
        if (!status) status = 6;
    } else if (physical_rc(expected) != (is_shared ? 2 : 1) ||
               physical_rc(actual) != (is_shared ? 2 : 1) ||
               (is_shared == 0 &&
                (!lean_is_exclusive(expected) || !lean_is_exclusive(actual)))) {
        if (!status) status = 7;
    }
    if (is_shared) {
        // The caller's second reference is still live and unchanged.
        if (physical_rc(original) != 1 || physical_rc(generated) != 1 ||
            !lean_is_exclusive(original) || !lean_is_exclusive(generated))
            status = 8;
        lean_dec(original);
        lean_dec(generated);
        // The returned child now has precisely one remaining credit.
        if (!status && (physical_rc(expected) != 1 ||
                        physical_rc(actual) != 1 ||
                        !lean_is_exclusive(expected) ||
                        !lean_is_exclusive(actual))) status = 9;
    }
    if (heap_stamp && physical_rc(old_stamp) != stamp_entry_rc && !status)
        status = 12;
    lean_dec(expected);
    lean_dec(actual);
    lean_dec(old_stamp);
    return lean_box(status);
}
