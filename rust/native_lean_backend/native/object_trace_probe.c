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

/* Independent real-Lean-runtime control of the SAME generated kernel
 * operations as the Rust test driver. Every retained source reference is
 * explicit; neither driver depends on compiler-specific optimization of a
 * separate driver language.
 */
extern int printf(const char *, ...);
extern lean_object *l_OwnershipObjectTrace_create(lean_object *);
extern lean_object *l_OwnershipObjectTrace_identity(lean_object *);
extern lean_object *l_OwnershipObjectTrace_select(uint8_t, lean_object *, lean_object *);
extern lean_object *l_OwnershipObjectTrace_throughClosure(lean_object *);

lean_obj_res lr_object_trace_run(lean_obj_arg first, lean_obj_arg second) {
    lean_object *a = l_OwnershipObjectTrace_create(first);
    printf("TRACE create %llu %llu\n", (unsigned long long)lr_object_trace_id(a),
           (unsigned long long)lr_object_trace_rc(a));
    lean_inc(a);
    lean_object *same = l_OwnershipObjectTrace_identity(a);
    printf("TRACE direct %llu %llu %llu %llu\n",
           (unsigned long long)lr_object_trace_id(a), (unsigned long long)lr_object_trace_rc(a),
           (unsigned long long)lr_object_trace_id(same), (unsigned long long)lr_object_trace_rc(same));
    lean_object *b = l_OwnershipObjectTrace_create(second);
    printf("TRACE second %llu %llu\n", (unsigned long long)lr_object_trace_id(b),
           (unsigned long long)lr_object_trace_rc(b));
    lean_inc(same);
    lean_inc(b);
    lean_object *left = l_OwnershipObjectTrace_select(1, same, b);
    printf("TRACE branch-left %llu %llu %llu %llu %llu %llu\n",
           (unsigned long long)lr_object_trace_id(same), (unsigned long long)lr_object_trace_rc(same),
           (unsigned long long)lr_object_trace_id(left), (unsigned long long)lr_object_trace_rc(left),
           (unsigned long long)lr_object_trace_id(b), (unsigned long long)lr_object_trace_rc(b));
    lean_inc(same);
    lean_inc(b);
    lean_object *right = l_OwnershipObjectTrace_select(0, same, b);
    printf("TRACE branch-right %llu %llu %llu %llu %llu %llu\n",
           (unsigned long long)lr_object_trace_id(same), (unsigned long long)lr_object_trace_rc(same),
           (unsigned long long)lr_object_trace_id(right), (unsigned long long)lr_object_trace_rc(right),
           (unsigned long long)lr_object_trace_id(b), (unsigned long long)lr_object_trace_rc(b));
    lean_inc(left);
    lean_object *captured = l_OwnershipObjectTrace_throughClosure(left);
    printf("TRACE closure %llu %llu %llu %llu\n",
           (unsigned long long)lr_object_trace_id(left), (unsigned long long)lr_object_trace_rc(left),
           (unsigned long long)lr_object_trace_id(captured), (unsigned long long)lr_object_trace_rc(captured));
    lean_dec(a);
    lean_dec(same);
    lean_dec(b);
    lean_dec(left);
    lean_dec(right);
    lean_dec(captured);
    return lean_box(0);
}
