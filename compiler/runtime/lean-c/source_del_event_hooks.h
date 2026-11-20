/* Trace only calls made by the unmodified, compiler-generated C source.
 * This header is pre-included in a separate C translation unit, *after*
 * lean.h was parsed. It never changes Lean C's implementation of a primitive.
 * A source-level call to a reference primitive is observed at its call site.
 * Recursive destructor worklist internals remain outside this boundary. */
#ifndef LR_SOURCE_DEL_EVENT_TRACE_H
#define LR_SOURCE_DEL_EVENT_TRACE_H
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>

void lr_source_event_begin(unsigned case_id, const char *lane,
                           lean_object *parent, lean_object *child,
                           lean_object *old_stamp);
void lr_source_event_end(void);
int lr_source_event_active(void);
void lr_source_event_record(const char *op, uintptr_t object,
                            uintptr_t related, unsigned field,
                            int before, int after);

static inline int lr_source_event_rc(lean_object *p) {
    return lean_internal_get_rc(p);
}
static inline void lr_source_event_inc(lean_object *p) {
    if (!lr_source_event_active() || !p || lean_is_scalar(p)) {
        lean_inc(p);
        return;
    }
    const int before = lr_source_event_rc(p);
    const uintptr_t identity = (uintptr_t)p;
    lean_inc(p);
    lr_source_event_record("inc", identity, 0, 0, before,
                           lr_source_event_rc(p));
}
static inline void lr_source_event_dec(lean_object *p) {
    if (!lr_source_event_active() || !p || lean_is_scalar(p)) {
        lean_dec(p);
        return;
    }
    const int before = lr_source_event_rc(p);
    const uintptr_t identity = (uintptr_t)p;
    lean_dec(p);
    /* A final release makes the pointer invalid. Its zero is a tombstone. */
    const int after = before == 1 ? 0 : lr_source_event_rc(p);
    lr_source_event_record("dec", identity, 0, 0, before, after);
}
static inline void lr_source_event_dec_ref(lean_object *p) {
    if (!lr_source_event_active()) {
        lean_dec_ref(p);
        return;
    }
    const int before = lr_source_event_rc(p);
    const uintptr_t identity = (uintptr_t)p;
    lean_dec_ref(p);
    const int after = before == 1 ? 0 : lr_source_event_rc(p);
    lr_source_event_record("dec", identity, 0, 0, before, after);
}
static inline void lr_source_event_del(lean_object *p) {
    if (!lr_source_event_active() || !p || lean_is_scalar(p)) {
        lean_del_object(p);
        return;
    }
    const int before = lr_source_event_rc(p);
    const uintptr_t identity = (uintptr_t)p;
    lean_del_object(p);
    lr_source_event_record("del", identity, 0, 0, before, 0);
}
static inline lean_object *lr_source_event_alloc_ctor(
        unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    lean_object *p = lean_alloc_ctor(tag, num_objs, scalar_sz);
    if (lr_source_event_active()) {
        lr_source_event_record("alloc", (uintptr_t)p, 0, num_objs,
                               0, lr_source_event_rc(p));
    }
    return p;
}
static inline void lr_source_event_set(
        lean_object *p, unsigned index, lean_object *value) {
    lean_ctor_set(p, index, value);
    if (lr_source_event_active()) {
        lr_source_event_record("set", (uintptr_t)p, (uintptr_t)value,
                               index, lr_source_event_rc(p),
                               lr_source_event_rc(p));
    }
}

/* Macro interception is limited to the included, unchanged generated C
 * translation units. These names are not patched in Lean's runtime. */
#define lean_inc(p) lr_source_event_inc(p)
#define lean_dec(p) lr_source_event_dec(p)
#define lean_dec_ref(p) lr_source_event_dec_ref(p)
#define lean_del_object(p) lr_source_event_del(p)
#define lean_alloc_ctor(tag, n, sz) lr_source_event_alloc_ctor(tag, n, sz)
#define lean_ctor_set(p, i, v) lr_source_event_set(p, i, v)
#endif
