/* Pinned Lean 4.34.1 physical-operation trace, distinct from the
 * original-source-vs-generated-Rust 720-case differential.
 *
 * Every "ok" event is measured immediately after the named REAL Lean C
 * primitive (lean_ctor_get / lean_is_exclusive / lean_inc / lean_dec /
 * lean_ctor_set / lean_del_object). "jumpOwned" is expressly a zero-C-op
 * bookkeeping stutter. A "refused" shellDel means the oracle's admission
 * predicate rejected it; lean_del_object was NEVER called.
 *
 * A freed parent's RC is not observable: parentRC=0 after shellDel is a
 * logical tombstone, NOT a read from freed memory. All object identities
 * are addresses compared within one live-allocation episode.
 *
 * These are bounded measurements, not a formal C semantics theorem.
 */
#include <lean/lean.h>
#include <stdint.h>

/* Pinned `leanc` ships a deliberately small C header set. Declare only
 * the standard C ABI calls this test oracle uses; FILE remains opaque.
 * No replacement implementation of any Lean ownership primitive. */
typedef struct _IO_FILE FILE;
extern FILE *fopen(const char *, const char *);
extern int fclose(FILE *);
extern int fprintf(FILE *, const char *, ...);
extern char *getenv(const char *);
extern int strcmp(const char *, const char *);
#define REQUIRE(test) do { if (!(test)) __builtin_trap(); } while (0)

typedef struct {
    const char *name;
    FILE *f;
    lean_object *parent;
    lean_object *child;
    lean_object *old_stamp; /* Borrowed external root, always live. */
    int parent_live;
    int child_field;
    int borrowed;
    int unique;
    const char *stamp_slot;
} episode;

static int checked_rc(lean_object *o) {
    REQUIRE(o && !lean_is_scalar(o) && lean_is_st(o));
    int n = lean_internal_get_rc(o);
    REQUIRE(n >= 1);
    return n;
}

/* Do not infer liveness from an address after free. */
static void checkpoint(episode *e, const char *event, const char *outcome) {
    REQUIRE(e->parent != e->child && e->child != e->old_stamp &&
           e->parent != e->old_stamp);
    REQUIRE(e->child_field == e->parent_live);
    if (e->parent_live) {
        REQUIRE(lean_is_ctor(e->parent));
        REQUIRE(lean_obj_tag(e->parent) == 1 &&
               lean_ctor_num_objs(e->parent) == 2);
        REQUIRE(lean_ctor_get(e->parent, 0) == e->child);
    }
    fprintf(e->f, "%s\t%s\t%s\t%d\t%d\t%d\t%d\t%d\t%s\t%d\t%llu\t%llu\t%llu\n",
        e->name, event, outcome,
        e->parent_live ? checked_rc(e->parent) : 0,
        checked_rc(e->child), checked_rc(e->old_stamp),
        e->child_field, e->borrowed, e->stamp_slot, e->unique,
        (unsigned long long)(uintptr_t)e->parent,
        (unsigned long long)(uintptr_t)e->child,
        (unsigned long long)(uintptr_t)e->old_stamp);
}

static episode new_episode(FILE *f, const char *name, lean_object *external_stamp) {
    REQUIRE(external_stamp && !lean_is_scalar(external_stamp));
    REQUIRE(checked_rc(external_stamp) >= 1);
    lean_object *child = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(child, 0, lean_box(5));
    lean_ctor_set(child, 1, lean_box(6));
    lean_inc(external_stamp); /* Parent receives exactly one owned field credit. */
    lean_object *parent = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(parent, 0, child);
    lean_ctor_set(parent, 1, external_stamp);
    episode e = {name, f, parent, child, external_stamp, 1, 1, 0, 0, "old"};
    REQUIRE(checked_rc(parent) == 1 && checked_rc(child) == 1);
    checkpoint(&e, "initial", "start");
    return e;
}
static void borrow_child(episode *e) {
    REQUIRE(e->parent_live && lean_ctor_get(e->parent, 0) == e->child);
    e->borrowed = 1; /* lean_ctor_get is a borrowed pointer, no inc. */
    checkpoint(e, "borrowChild", "ok");
}
static void observe_sharing(episode *e) {
    REQUIRE(e->parent_live);
    e->unique = lean_is_exclusive(e->parent) ? 1 : 0;
    checkpoint(e, "inspectSharing", "ok");
}
static void stamp_dec(episode *e) {
    REQUIRE(e->parent_live && e->unique && checked_rc(e->parent) == 1);
    REQUIRE(strcmp(e->stamp_slot, "old") == 0);
    REQUIRE(lean_ctor_get(e->parent, 1) == e->old_stamp);
    REQUIRE(checked_rc(e->old_stamp) >= 2); /* External root must protect it. */
    lean_dec(e->old_stamp); /* Consume the existing parent field credit. */
    e->stamp_slot = "spent";
    checkpoint(e, "stampDec", "ok");
}
static void jump_owner(episode *e) {
    REQUIRE(e->parent_live);
    /* Source jmp/rename is zero physical instructions, not a C operation. */
    checkpoint(e, "jumpOwned", "ok");
}
static int can_shell_del(episode *e) {
    return e->parent_live && e->borrowed && e->unique &&
        checked_rc(e->parent) == 1 && checked_rc(e->child) == 1 &&
        strcmp(e->stamp_slot, "spent") == 0 &&
        lean_ctor_get(e->parent, 0) == e->child;
}
static void do_shell_del(episode *e) {
    REQUIRE(can_shell_del(e));
    lean_del_object(e->parent);
    e->parent_live = 0;
    e->child_field = 0;
    /* Never touch e->parent again, except to print its saved identity. */
    checkpoint(e, "shellDel", "ok");
}
static void refuse_shell_del(episode *e) {
    REQUIRE(!can_shell_del(e));
    /* No lean_del_object call is attempted on a rejected state. */
    checkpoint(e, "shellDel", "refused");
}
static void retain_parent(episode *e) {
    REQUIRE(e->parent_live);
    lean_inc(e->parent);
    e->unique = 0; /* Observed exclusivity is invalidated by ownership change. */
    checkpoint(e, "retainParent", "ok");
}
static void release_shared_parent(episode *e) {
    REQUIRE(checked_rc(e->parent) > 1);
    lean_dec(e->parent);
    e->unique = 0;
    checkpoint(e, "releaseSharedParent", "ok");
}
static void retain_child(episode *e) {
    REQUIRE(e->parent_live && e->borrowed);
    lean_inc(e->child);
    checkpoint(e, "retainChild", "ok");
}
static void fresh_tagged_stamp(episode *e) {
    REQUIRE(e->parent_live && e->unique &&
           strcmp(e->stamp_slot, "spent") == 0);
    /* Only a scalar replacement is used: there is no untracked new
     * heap credit. General heap-stamp replacement remains unmodeled. */
    lean_ctor_set(e->parent, 1, lean_box(33));
    e->stamp_slot = "fresh";
    checkpoint(e, "setFreshStamp", "ok");
}

static void run_delete(FILE *f, lean_object *stamp) {
    episode e = new_episode(f, "unique", stamp);
    borrow_child(&e);
    observe_sharing(&e);
    stamp_dec(&e);
    jump_owner(&e);
    do_shell_del(&e);
    REQUIRE(checked_rc(e.child) == 1);
    lean_dec(e.child); /* Cleanup after the final observed checkpoint. */
}
static void run_shared(FILE *f, lean_object *stamp) {
    episode e = new_episode(f, "shared", stamp);
    retain_parent(&e);
    observe_sharing(&e);
    REQUIRE(!e.unique);
    release_shared_parent(&e);
    borrow_child(&e);
    observe_sharing(&e);
    stamp_dec(&e);
    jump_owner(&e);
    do_shell_del(&e);
    lean_dec(e.child);
}
static void run_retained(FILE *f, lean_object *stamp) {
    episode e = new_episode(f, "retained", stamp);
    borrow_child(&e);
    observe_sharing(&e);
    stamp_dec(&e);
    retain_child(&e);
    refuse_shell_del(&e);
    /* Both credits are still live. Drop the independent retain, then
     * shell-delete the parent WITHOUT dec'ing its already-spent stamp. */
    lean_dec(e.child);
    REQUIRE(can_shell_del(&e));
    lean_del_object(e.parent);
    lean_dec(e.child);
}
static void run_fresh(FILE *f, lean_object *stamp) {
    episode e = new_episode(f, "fresh", stamp);
    borrow_child(&e);
    observe_sharing(&e);
    stamp_dec(&e);
    jump_owner(&e);
    fresh_tagged_stamp(&e);
    refuse_shell_del(&e);
    /* New stamp is tagged, old heap stamp was already released, so an
     * ordinary destructor of this now-valid constructor is safe. */
    lean_dec(e.parent);
}

/* Borrowed @& Nat parameter: all heap-field increments are explicit
 * above, and the caller retains its independent reference throughout. */
lean_obj_res lr_heap_trace_source_credits(b_lean_obj_arg stamp) {
    if (!stamp || lean_is_scalar(stamp) || !lean_is_st(stamp)) return lean_box(1);
    const char *path = getenv("LR_SOURCE_TRACE");
    if (!path || !*path) return lean_box(2);
    FILE *f = fopen(path, "w");
    if (!f) return lean_box(3);
    fprintf(f, "case\tevent\toutcome\tparentRC\tchildRC\toldStampRC\tchildField\tborrowedChild\tstampSlot\tobservedUnique\tparentId\tchildId\toldStampId\n");
    const int initial = checked_rc((lean_object *)stamp);
    run_delete(f, (lean_object *)stamp);
    run_shared(f, (lean_object *)stamp);
    run_retained(f, (lean_object *)stamp);
    run_fresh(f, (lean_object *)stamp);
    REQUIRE(checked_rc((lean_object *)stamp) == initial);
    if (fclose(f) != 0) return lean_box(4);
    return lean_box(0);
}
