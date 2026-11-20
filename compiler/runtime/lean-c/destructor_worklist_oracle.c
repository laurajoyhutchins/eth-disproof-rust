/* Physical witnesses for the pinned Lean 4.34.1 recursive destructor.

   Lean's lean_dec_ref_cold invokes a C++ worklist when a constructor's last
   source-owned reference is released. We DO NOT replace or instrument that
   worklist: a protected, distinct sentinel survives for each chosen
   descendant, so the real lean_dec call exposes the effect on every sentinel
   after the worklist returns.

   The temporary constructor nodes are unique, ordinary single-threaded
   objects. Their identities are captured while live and are never
   dereferenced after destruction. A sentinel's observed RC is read only
   while its independent external credit is held.

   This measures the worklist's *effects*, not its internal event order or
   actual allocator-free timestamps. Source: lean4/v4.34.1,
   src/runtime/object.cpp, lean_dec_ref_cold and lean_del_core. */
#include <lean/lean.h>
#include <stdint.h>

typedef struct _IO_FILE FILE;
extern FILE *fopen(const char *, const char *);
extern int fclose(FILE *);
extern int fprintf(FILE *, const char *, ...);
extern char *getenv(const char *);
#define REQUIRE(b) do { if (!(b)) __builtin_trap(); } while (0)

/* No-op unless the diagnostic executable selects LR_WORKLIST_EVENTS.
 * These register live identities, never dereference an object after free. */
extern void lr_wl_trace_register(const char *, unsigned, lean_object *);
extern void lr_wl_trace_begin(const char *);
extern void lr_wl_trace_end(void);

enum { MAX_WITNESSES = 8 };

typedef struct {
    const char *name;
    lean_object *root;
    lean_object *retained;        /* Has an independent owned credit, or NULL. */
    lean_object *witness[MAX_WITNESSES];
    uintptr_t witness_id[MAX_WITNESSES];
    lean_object *nodes[MAX_WITNESSES + 2];
    unsigned node_count;
    uintptr_t root_id;
    unsigned count;
    int shared_root;
} cascade;

static int live_rc(lean_object *o) {
    REQUIRE(o != NULL && !lean_is_scalar(o) && lean_is_st(o));
    const int rc = lean_internal_get_rc(o);
    REQUIRE(rc >= 1);
    return rc;
}

static lean_object *make_witness(unsigned index) {
    lean_object *o = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(o, 0, lean_box((size_t)index + 71));
    lean_ctor_set(o, 1, lean_box((size_t)index + 113));
    REQUIRE(live_rc(o) == 1); /* An independent root survives all phases. */
    return o;
}

static lean_object *make_link(lean_object *child, lean_object *witness) {
    lean_inc(witness); /* The new node receives a separate field credit. */
    lean_object *node = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(node, 0, child);
    lean_ctor_set(node, 1, witness);
    REQUIRE(live_rc(node) == 1 && live_rc(witness) == 2);
    return node;
}

static cascade make_chain(const char *name, unsigned depth, int retained_index,
                          int shared_root) {
    REQUIRE(depth >= 1 && depth <= MAX_WITNESSES);
    REQUIRE(retained_index < (int)depth);
    REQUIRE(!shared_root || retained_index == -1);
    cascade c = {0};
    c.name = name;
    c.count = depth;
    c.shared_root = shared_root;
    lean_object *nodes[MAX_WITNESSES];
    for (unsigned i = 0; i < depth; ++i) {
        c.witness[i] = make_witness(i);
        c.witness_id[i] = (uintptr_t)c.witness[i];
    }
    lean_object *child = lean_box(0);
    for (unsigned i = depth; i != 0; --i) {
        nodes[i - 1] = make_link(child, c.witness[i - 1]);
        child = nodes[i - 1];
    }
    c.root = nodes[0];
    c.root_id = (uintptr_t)c.root;
    c.node_count = depth;
    for (unsigned i = 0; i < depth; ++i) c.nodes[i] = nodes[i];
    if (retained_index >= 0) {
        c.retained = nodes[retained_index];
        lean_inc(c.retained);
        REQUIRE(live_rc(c.retained) == 2);
    } else if (shared_root) {
        lean_inc(c.root);
        REQUIRE(live_rc(c.root) == 2);
    }
    return c;
}

/* Three witness-bearing leaves, two additional unretained fork nodes:
         root
        /    \
      inner  leaf2
     /    \
   leaf0  leaf1

   Every leaf owns a separate heap witness credit. */
static cascade make_fork(const char *name, int retain_right) {
    cascade c = {0};
    c.name = name;
    c.count = 3;
    lean_object *leaves[3];
    for (unsigned i = 0; i < 3; ++i) {
        c.witness[i] = make_witness(i);
        c.witness_id[i] = (uintptr_t)c.witness[i];
        leaves[i] = make_link(lean_box(0), c.witness[i]);
    }
    lean_object *inner = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(inner, 0, leaves[0]);
    lean_ctor_set(inner, 1, leaves[1]);
    lean_object *root = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(root, 0, inner);
    lean_ctor_set(root, 1, leaves[2]);
    c.root = root;
    c.root_id = (uintptr_t)root;
    c.node_count = 5;
    c.nodes[0] = root;
    c.nodes[1] = inner;
    for (unsigned i = 0; i < 3; ++i) c.nodes[i + 2] = leaves[i];
    REQUIRE(live_rc(root) == 1 && live_rc(inner) == 1);
    if (retain_right) {
        c.retained = leaves[2];
        lean_inc(c.retained);
        REQUIRE(live_rc(c.retained) == 2);
    }
    return c;
}

/* Non-tree constructor graphs: a child can carry multiple incoming
   field credits. The runtime must decrement each edge in source field order,
   and enqueue the target exactly once when its LAST owner is consumed.
   These are the first cases in this audit that the prior Tree model cannot
   express without falsely duplicating an allocation identity. */
static cascade make_aliased(const char *name, int diamond, int retain_shared) {
    cascade c = {0};
    c.name = name;
    c.count = 1;
    c.witness[0] = make_witness(0);
    c.witness_id[0] = (uintptr_t)c.witness[0];
    lean_object *shared = make_link(lean_box(0), c.witness[0]);
    lean_inc(shared); /* Two distinct owning fields target ONE object. */
    REQUIRE(live_rc(shared) == 2);
    if (!diamond) {
        REQUIRE(!retain_shared);
        lean_object *root = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(root, 0, shared);
        lean_ctor_set(root, 1, shared);
        c.root = root;
        c.node_count = 2;
        c.nodes[0] = root;
        c.nodes[1] = shared;
    } else {
        lean_object *left = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(left, 0, shared);
        lean_ctor_set(left, 1, lean_box(0));
        lean_object *right = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(right, 0, shared);
        lean_ctor_set(right, 1, lean_box(0));
        lean_object *root = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(root, 0, left);
        lean_ctor_set(root, 1, right);
        c.root = root;
        c.node_count = 4;
        c.nodes[0] = root;
        c.nodes[1] = left;
        c.nodes[2] = right;
        c.nodes[3] = shared;
    }
    c.root_id = (uintptr_t)c.root;
    if (retain_shared) {
        c.retained = shared;
        lean_inc(shared); /* One independent owner stops the cascade. */
        REQUIRE(live_rc(shared) == 3);
    }
    return c;
}

static void record(FILE *f, const cascade *c, const char *phase) {
    for (unsigned i = 0; i < c->count; ++i) {
        REQUIRE(c->witness[i] != NULL && c->witness_id[i] != 0);
        REQUIRE(c->root_id != c->witness_id[i]);
        for (unsigned j = 0; j < i; ++j)
            REQUIRE(c->witness_id[i] != c->witness_id[j]);
        const int rc = live_rc(c->witness[i]);
        REQUIRE(rc == 1 || rc == 2);
        fprintf(f, "%s\t%s\t%u\t%llu\t%llu\t%d\n",
                c->name, phase, i,
                (unsigned long long)c->root_id,
                (unsigned long long)c->witness_id[i], rc);
    }
}

static void run(FILE *f, cascade c) {
    REQUIRE(c.root != NULL && c.count >= 1);
    record(f, &c, "before");
    /* In the diagnostic build the original pinned object.cpp logs internal
       worklist events. The stock executable still runs unmodified and
       supplies independent descendant RC witness observations. */
    for (unsigned i = 0; i < c.node_count; ++i)
        lr_wl_trace_register("node", i, c.nodes[i]);
    for (unsigned i = 0; i < c.count; ++i)
        lr_wl_trace_register("witness", i, c.witness[i]);
    lr_wl_trace_begin(c.name);
    lean_dec(c.root);
    lr_wl_trace_end();
    /* The root is potentially freed: record only live, independently owned
       witnesses. Never dereference the old root or a freed descendant. */
    record(f, &c, "afterRoot");
    if (c.retained != NULL) {
        lean_dec(c.retained);   /* Drops the independent child root. */
    } else if (c.shared_root) {
        lean_dec(c.root);       /* Still live after the first shared dec. */
    }
    record(f, &c, "afterCleanup");
    for (unsigned i = 0; i < c.count; ++i) {
        REQUIRE(live_rc(c.witness[i]) == 1);
        lean_dec(c.witness[i]); /* Drop protected roots after all observations. */
    }
}

lean_obj_res lr_heap_trace_destructor_worklist(b_lean_obj_arg dummy) {
    REQUIRE(dummy != NULL && lean_is_scalar((lean_object *)dummy));
    const char *path = getenv("LR_DESTRUCTOR_WITNESSES");
    if (path == NULL || *path == 0) return lean_box(1);
    FILE *f = fopen(path, "w");
    if (f == NULL) return lean_box(2);
    fprintf(f, "case\tphase\tindex\trootId\twitnessId\trc\n");
    run(f, make_chain("chain1", 1, -1, 0));
    run(f, make_chain("chain3", 3, -1, 0));
    run(f, make_chain("chain8", 8, -1, 0));
    run(f, make_chain("retainMid3", 3, 1, 0));
    run(f, make_chain("retainLeaf3", 3, 2, 0));
    run(f, make_chain("sharedRoot3", 3, -1, 1));
    run(f, make_fork("forkAll", 0));
    run(f, make_fork("forkRetainRight", 1));
    run(f, make_aliased("duplicateField", 0, 0));
    run(f, make_aliased("diamond", 1, 0));
    run(f, make_aliased("diamondRetained", 1, 1));
    if (fclose(f) != 0) return lean_box(3);
    return lean_box(0);
}
