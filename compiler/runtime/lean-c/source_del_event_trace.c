/* Bounded, opt-in event recorder for the *actual* compiled Lean C and
 * exact Reader-generated Rust function. Values here are observed at the
 * primitive boundary, not a replacement for reference-count operations.
 * Identity tokens are captured before last release; no freed object read. */
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include "source_del_event_hooks.h"
typedef struct _IO_FILE FILE;
extern FILE *fopen(const char *, const char *);
extern int fprintf(FILE *, const char *, ...);
extern int fflush(FILE *);
extern char *getenv(const char *);
#define REQUIRE(x) do { if (!(x)) __builtin_trap(); } while (0)

static FILE *stream;
static unsigned current_case, step;
static const char *current_lane;
static uintptr_t parent_id, child_id, old_id;
static uintptr_t others[64];
static unsigned other_count;
static int active;

static const char *role(uintptr_t id, char *buffer) {
    if (id == 0) return "_";
    if (id == parent_id) return "parent";
    if (id == child_id) return "child";
    if (old_id && id == old_id) return "oldStamp";
    if ((id & (uintptr_t)1) != 0) {
        /* Lean's tagged pointer encoding; no dereference. */
        const size_t value = lean_unbox((lean_object *)id);
        extern int sprintf(char *, const char *, ...);
        sprintf(buffer, "small:%llu", (unsigned long long)value);
        return buffer;
    }
    for (unsigned i = 0; i < other_count; ++i) {
        if (others[i] == id) {
            extern int sprintf(char *, const char *, ...);
            sprintf(buffer, "created:%u", i);
            return buffer;
        }
    }
    REQUIRE(other_count < sizeof(others) / sizeof(others[0]));
    others[other_count] = id;
    extern int sprintf(char *, const char *, ...);
    sprintf(buffer, "created:%u", other_count++);
    return buffer;
}

int lr_source_event_active(void) { return active; }

void lr_source_event_begin(unsigned case_id, const char *lane,
                           lean_object *parent, lean_object *child,
                           lean_object *old_stamp) {
    REQUIRE(!active);
    const char *path = getenv("LR_SOURCE_DEL_EVENTS");
    if (!path || !*path) return;
    if (!stream) {
        stream = fopen(path, "w");
        REQUIRE(stream != 0);
        fprintf(stream, "case\tlane\tindex\top\tobject\trelated\tfield\tbefore\tafter\n");
    }
    current_case = case_id;
    current_lane = lane;
    step = 0;
    parent_id = (uintptr_t)parent;
    child_id = (uintptr_t)child;
    old_id = (uintptr_t)old_stamp;
    other_count = 0;
    active = 1;
    fprintf(stream, "%u\t%s\t0\tBEGIN\t_\t_\t0\t0\t0\n",
            current_case, current_lane);
}

void lr_source_event_record(const char *op, uintptr_t object,
                            uintptr_t related, unsigned field,
                            int before, int after) {
    if (!active) return;
    char obj_role[64], rel_role[64];
    const char *obj = role(object, obj_role);
    const char *rel = role(related, rel_role);
    REQUIRE(before >= 0 && after >= 0);
    fprintf(stream, "%u\t%s\t%u\t%s\t%s\t%s\t%u\t%d\t%d\n",
            current_case, current_lane, ++step, op, obj, rel, field,
            before, after);
}

void lr_source_event_end(void) {
    if (!active) return;
    fprintf(stream, "%u\t%s\t%u\tEND\t_\t_\t0\t0\t0\n",
            current_case, current_lane, step + 1);
    REQUIRE(fflush(stream) == 0);
    active = 0;
}
