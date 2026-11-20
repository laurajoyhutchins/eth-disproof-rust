/* Real Lean 4.34.1 C runtime operations for heap-stamp replacement
 * and final-reference recursive destruction. Distinct from the 28-row
 * shell-only trace and the 720-case generated Rust differential.
 *
 * The old and new stamps are genuinely heap-allocated Nat values kept
 * alive by borrowed external roots. Child and parent final frees are
 * NOT measured by dereferencing stale memory; zero is an explicit
 * logical tombstone, checked against surviving owners' actual RC.
 *
 * Source: lean.h: lean_dec_ref 691-700, lean_ctor_set 820-823;
 * object.cpp: lean_dec_ref_cold 467-487 and constructor worklist.
 */
#include <lean/lean.h>
#include <stdint.h>
typedef struct _IO_FILE FILE;
extern FILE *fopen(const char *, const char *);
extern int fclose(FILE *);
extern int fprintf(FILE *, const char *, ...);
extern char *getenv(const char *);
#define REQUIRE(x) do { if (!(x)) __builtin_trap(); } while (0)

typedef struct {
    const char *name;
    FILE *f;
    lean_object *parent, *child, *old, *fresh;
    int parentLive, childLive, childField, freshPending, borrowed;
    const char *slot;
    /* Captured while live. Never evaluate a dangling pointer for identity. */
    uintptr_t parentId, childId, oldId, freshId;
} episode;

static int live_rc(lean_object *o) {
    REQUIRE(o && !lean_is_scalar(o) && lean_is_st(o));
    int rc = lean_internal_get_rc(o);
    REQUIRE(rc >= 1);
    return rc;
}

static void record(episode *e, const char *event) {
    REQUIRE(e->parentId != e->childId && e->parentId != e->oldId &&
            e->parentId != e->freshId && e->childId != e->oldId &&
            e->childId != e->freshId && e->oldId != e->freshId);
    REQUIRE(e->childField == e->parentLive);
    if (e->parentLive) {
        REQUIRE(lean_is_ctor(e->parent));
        REQUIRE(lean_obj_tag(e->parent) == 1);
        REQUIRE(lean_ctor_num_objs(e->parent) == 2);
        REQUIRE(lean_ctor_get(e->parent, 0) == e->child);
        REQUIRE(e->childLive);
    }
    fprintf(e->f,
      "%s\t%s\tok\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%s\t%llu\t%llu\t%llu\t%llu\n",
      e->name, event,
      e->parentLive ? live_rc(e->parent) : 0,
      e->childLive ? live_rc(e->child) : 0,
      live_rc(e->old), live_rc(e->fresh),
      e->childField, e->freshPending, e->borrowed, e->slot,
      (unsigned long long)e->parentId,
      (unsigned long long)e->childId,
      (unsigned long long)e->oldId,
      (unsigned long long)e->freshId);
}

static episode begin(FILE *f, const char *name, lean_object *old, lean_object *fresh) {
    REQUIRE(old && fresh && old != fresh);
    REQUIRE(live_rc(old) >= 1 && live_rc(fresh) >= 1);
    lean_object *child = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(child, 0, lean_box(5));
    lean_ctor_set(child, 1, lean_box(6));
    lean_inc(old); /* Parent field receives one old-stamp owned credit. */
    lean_object *parent = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(parent, 0, child);
    lean_ctor_set(parent, 1, old);
    episode e = {name, f, parent, child, old, fresh, 1, 1, 1, 0, 0, "old",
                 (uintptr_t)parent, (uintptr_t)child,
                 (uintptr_t)old, (uintptr_t)fresh};
    REQUIRE(live_rc(parent) == 1 && live_rc(child) == 1);
    record(&e, "initial");
    return e;
}
static void borrow(episode *e) {
    REQUIRE(e->parentLive && lean_ctor_get(e->parent, 0) == e->child);
    e->borrowed = 1; /* Projection is borrowed: no Lean inc. */
    record(e, "borrowChild");
}
static void consume_old(episode *e) {
    REQUIRE(e->parentLive && lean_is_exclusive(e->parent));
    REQUIRE(e->slot[0] == 'o' && lean_ctor_get(e->parent, 1) == e->old);
    REQUIRE(live_rc(e->old) >= 2);
    lean_dec(e->old);
    e->slot = "spent"; /* Slot pointer is stale until field overwrite. */
    record(e, "decOld");
}
static void inc_fresh(episode *e) {
    REQUIRE(e->parentLive && e->slot[0] == 's' && !e->freshPending);
    lean_inc(e->fresh); /* This is the acquired NEW owned field credit. */
    e->freshPending = 1;
    record(e, "incFresh");
}
static void write_fresh(episode *e) {
    REQUIRE(e->parentLive && lean_is_exclusive(e->parent));
    REQUIRE(e->slot[0] == 's' && e->freshPending);
    int before = live_rc(e->fresh);
    lean_ctor_set(e->parent, 1, e->fresh); /* Does NOT inc or dec. */
    REQUIRE(live_rc(e->fresh) == before);
    e->slot = "fresh";
    e->freshPending = 0;
    record(e, "storeFresh");
}
static void inc_child(episode *e) {
    REQUIRE(e->parentLive && e->childLive);
    lean_inc(e->child);
    record(e, "incChild");
}
static void final_dec_parent(episode *e, int expectChildSurvival) {
    REQUIRE(e->parentLive && lean_is_exclusive(e->parent));
    REQUIRE(e->slot[0] == 'o' || e->slot[0] == 'f');
    int oldBefore = live_rc(e->old), freshBefore = live_rc(e->fresh);
    int childBefore = live_rc(e->child);
    REQUIRE(childBefore == (expectChildSurvival ? 2 : 1));
    lean_dec(e->parent); /* The actual Lean C destructor worklist. */
    e->parentLive = 0;
    e->childField = 0;
    e->childLive = expectChildSurvival;
    /* External references protect the live stamp objects. */
    REQUIRE(live_rc(e->old) == oldBefore - (e->slot[0] == 'o'));
    REQUIRE(live_rc(e->fresh) == freshBefore - (e->slot[0] == 'f'));
    if (expectChildSurvival) REQUIRE(live_rc(e->child) == childBefore - 1);
    /* Parent and possibly child freed: do not inspect their old memory. */
    record(e, "decParent");
}
static void final_dec_child(episode *e) {
    REQUIRE(!e->parentLive && e->childLive && live_rc(e->child) == 1);
    lean_dec(e->child);
    e->childLive = 0;
    record(e, "decLastChild"); /* Child RC=0 is a logical tombstone. */
}
static void fresh_final(FILE *f, lean_object *old, lean_object *fresh) {
    episode e = begin(f, "heapFreshFinal", old, fresh);
    borrow(&e);
    consume_old(&e);
    inc_fresh(&e);
    write_fresh(&e);
    final_dec_parent(&e, 0);
}
static void fresh_retained(FILE *f, lean_object *old, lean_object *fresh) {
    episode e = begin(f, "heapFreshRetained", old, fresh);
    borrow(&e);
    consume_old(&e);
    inc_fresh(&e);
    write_fresh(&e);
    inc_child(&e);
    final_dec_parent(&e, 1);
    final_dec_child(&e);
}
static void old_final(FILE *f, lean_object *old, lean_object *fresh) {
    episode e = begin(f, "oldStampFinal", old, fresh);
    final_dec_parent(&e, 0);
}

/* Both Nat parameters are borrowed: the Lean driver preserves external
 * credits while all internal field credits are actually acquired/released. */
lean_obj_res lr_heap_trace_final_releases(b_lean_obj_arg old, b_lean_obj_arg fresh) {
    if (!old || !fresh || lean_is_scalar(old) || lean_is_scalar(fresh)) return lean_box(1);
    if (!lean_is_st(old) || !lean_is_st(fresh) || old == fresh) return lean_box(2);
    const char *path = getenv("LR_RELEASE_TRACE");
    if (!path || !*path) return lean_box(3);
    FILE *f = fopen(path, "w");
    if (!f) return lean_box(4);
    fprintf(f, "case\tevent\toutcome\tparentRC\tchildRC\toldRC\tfreshRC\tchildField\tfreshPending\tchildBorrowed\tstampSlot\tparentId\tchildId\toldId\tfreshId\n");
    int oldInitial = live_rc((lean_object *)old);
    int freshInitial = live_rc((lean_object *)fresh);
    fresh_final(f, (lean_object *)old, (lean_object *)fresh);
    fresh_retained(f, (lean_object *)old, (lean_object *)fresh);
    old_final(f, (lean_object *)old, (lean_object *)fresh);
    REQUIRE(live_rc((lean_object *)old) == oldInitial);
    REQUIRE(live_rc((lean_object *)fresh) == freshInitial);
    if (fclose(f) != 0) return lean_box(5);
    return lean_box(0);
}
