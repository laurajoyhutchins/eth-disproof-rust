/* Observation-only companion for the unmodified Lean C kernel.
 * IDs are per-run, assigned when each heap allocation is first observed.
 * We do not infer source RC from a compiler's variable names or field values.
 */
#include <lean/lean.h>
#include <stdint.h>

static lean_object *observed[32];
static unsigned n_observed;

uint64_t lr_object_trace_id(b_lean_obj_arg x) {
    if (!x || lean_is_scalar((lean_object *)x)) return UINT64_MAX - 1u;
    for (unsigned i = 0; i < n_observed; ++i) {
        if (observed[i] == x) return (uint64_t)(i + 1);
    }
    if (n_observed == 32) __builtin_trap();
    observed[n_observed++] = (lean_object *)x;
    return (uint64_t)n_observed;
}

uint64_t lr_object_trace_rc(b_lean_obj_arg x) {
    if (!x || lean_is_scalar((lean_object *)x)) return UINT64_MAX - 1u;
    if (!lean_is_st((lean_object *)x)) return UINT64_MAX - 2u;
    int rc = lean_internal_get_rc((lean_object *)x);
    if (rc < 1) return UINT64_MAX - 3u; /* never report as admitted */
    return (uint64_t)rc;
}
