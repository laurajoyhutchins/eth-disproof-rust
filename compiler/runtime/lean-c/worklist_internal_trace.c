/* Diagnostic journal for a pinned, separately compiled object.cpp.
 * All IDs are captured while live; no event callback dereferences any object.
 * Event order is the *instrumented C++ source order*, not a claim about an
 * unmodified runtime's internal timing. */
#include <lean/lean.h>
#include <stdint.h>
typedef struct _IO_FILE FILE;
extern FILE *fopen(const char *, const char *);
extern int fprintf(FILE *, const char *, ...);
extern int fflush(FILE *);
extern char *getenv(const char *);
#define ENSURE(x) do { if (!(x)) __builtin_trap(); } while (0)

typedef struct {
    uintptr_t ptr;
    const char *type;
    unsigned index;
} registered;
static registered objects[32];
static unsigned registered_count;
static FILE *out;
static const char *current_case;
static unsigned step;
static int active;

void lr_wl_trace_register(const char *type, unsigned index, lean_object *object) {
    ENSURE(!active && object && !lean_is_scalar(object));
    ENSURE(registered_count < 32);
    uintptr_t id = (uintptr_t)object;
    for (unsigned i = 0; i < registered_count; ++i)
        ENSURE(objects[i].ptr != id);
    objects[registered_count++] = (registered){id, type, index};
}

static void print_role(lean_object *object) {
    if (!object) {
        fprintf(out, "_");
        return;
    }
    /* Pointer-tagged immediate has no allocation identity. */
    if (lean_is_scalar(object)) {
        fprintf(out, "small:%llu", (unsigned long long)lean_unbox(object));
        return;
    }
    uintptr_t id = (uintptr_t)object;
    for (unsigned i = 0; i < registered_count; ++i) {
        if (objects[i].ptr == id) {
            fprintf(out, "%s:%u", objects[i].type, objects[i].index);
            return;
        }
    }
    ENSURE(0); /* Fail closed on an unregistered heap allocation. */
}

void lr_wl_trace_begin(const char *case_name) {
    ENSURE(!active);
    const char *path = getenv("LR_WORKLIST_EVENTS");
    if (!path || !*path) {
        registered_count = 0;
        return;
    }
    if (!out) {
        out = fopen(path, "w");
        ENSURE(out != NULL);
        fprintf(out, "case\tindex\tkind\tobject\trelated\tfield\tbefore\tafter\n");
    }
    current_case = case_name;
    step = 0;
    active = 1;
    fprintf(out, "%s\t0\tBEGIN\t_\t_\t0\t0\t0\n", current_case);
}

int lr_wl_trace_active(void) { return active; }

void lr_wl_trace_emit(const char *kind, lean_object *object,
                      lean_object *related, unsigned field,
                      int before, int after) {
    if (!active) return;
    ENSURE(object && before >= 0 && after >= 0);
    fprintf(out, "%s\t%u\t%s\t", current_case, ++step, kind);
    print_role(object);
    fprintf(out, "\t");
    print_role(related);
    fprintf(out, "\t%u\t%d\t%d\n", field, before, after);
}

void lr_wl_trace_end(void) {
    if (!active) return;
    fprintf(out, "%s\t%u\tEND\t_\t_\t0\t0\t0\n",
            current_case, step + 1);
    ENSURE(fflush(out) == 0);
    active = 0;
    registered_count = 0;
}
