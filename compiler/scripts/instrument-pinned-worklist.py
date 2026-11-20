#!/usr/bin/env python3
"""Instrument the *entire original* Lean 4.34.1 object.cpp translation unit.

This is a separate, diagnostic executable. The production Lean runtime is
unchanged. Before editing, pin both the upstream commit and the exact Git blob
of object.cpp. Every replacement must match exactly once, or fail closed.
Events are emitted by the actual source control-flow in that separate build,
not by a rewritten model of the destructor.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
BLOB = "9a8b4c56809b160055d83f5c7e7b64e6191aa86c"

def replace_one(s: str, before: str, after: str) -> str:
    if s.count(before) != 1:
        raise ValueError(f"pinned upstream destructor anchor count != 1: {before[:90]!r}")
    return s.replace(before, after)

def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: instrument-pinned-worklist.py UPSTREAM_CHECKOUT OUTPUT_CPP")
    checkout = Path(sys.argv[1])
    source = checkout / "src/runtime/object.cpp"
    output = Path(sys.argv[2])
    head = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    blob = subprocess.check_output(
        ["git", "-C", str(checkout), "hash-object", str(source.resolve())],
        text=True,
    ).strip()
    if head != COMMIT or blob != BLOB:
        raise ValueError(f"Lean runtime source drift: commit={head}, object.cpp={blob}")
    s = source.read_text()
    s = replace_one(s, '#include <lean/lean.h>\n', '''#include <lean/lean.h>
#ifdef LEAN_LAZY_RC
#error "This worklist trace requires the pinned eager RC runtime"
#endif
extern "C" int lr_wl_trace_active(void);
extern "C" void lr_wl_trace_emit(
    const char *kind, lean_object *object, lean_object *related,
    unsigned field, int before, int after);
#define LR_WL(kind, obj, related, field, before, after) \\
    do { if (lr_wl_trace_active()) \\
        lr_wl_trace_emit(kind, obj, related, field, before, after); } while (0)
''')
    s = replace_one(s, '''static inline lean_object * pop_back(lean_object * & todo) {
    lean_object * r = todo;
    todo = get_next(todo);
    return r;
}
''', '''static inline lean_object * pop_back(lean_object * & todo) {
    lean_object * r = todo;
    todo = get_next(todo);
    LR_WL("pop", r, nullptr, 0, 0, 0);
    return r;
}
''')
    s = replace_one(s, '''static inline void dec(lean_object * o, lean_object* & todo) {
    if (lean_is_scalar(o))
        return;
    if (LEAN_LIKELY(lean_internal_get_rc(o) > 1)) {
        lean_internal_sub_rc(o, 1);
    } else if (lean_internal_get_rc(o) == 1) {
        push_back(todo, o);
    } else if (lean_is_never_freed(o)) {
        return;
    } else if (std::atomic_fetch_add_explicit(lean_get_rc_mt_addr(o), 1, std::memory_order_acq_rel) == -1) {
        push_back(todo, o);
    }
}''', '''static inline void dec(lean_object * o, lean_object* & todo) {
    if (lean_is_scalar(o))
        return;
    if (LEAN_LIKELY(lean_internal_get_rc(o) > 1)) {
        int before = lean_internal_get_rc(o);
        lean_internal_sub_rc(o, 1);
        LR_WL("decrement", o, nullptr, 0, before, before - 1);
    } else if (lean_internal_get_rc(o) == 1) {
        LR_WL("enqueue", o, nullptr, 0, 1, 1);
        push_back(todo, o);
    } else if (lean_is_never_freed(o)) {
        return;
    } else if (std::atomic_fetch_add_explicit(lean_get_rc_mt_addr(o), 1, std::memory_order_acq_rel) == -1) {
        push_back(todo, o);
    }
}''')
    s = replace_one(s, '''static object * lean_del_core(object * o, object * todo) {
    uint8 tag = lean_ptr_tag(o);
    if (LEAN_LIKELY(tag <= LeanMaxCtorTag)) {
        object ** it  = lean_ctor_obj_cptr(o);
        object ** end = it + lean_ctor_num_objs(o);
        for (; it != end; ++it) dec(*it, todo);
        lean_free_small_object(o);
        return todo;
    } else {
        return lean_del_core_other(o, tag, todo);
    }
}''', '''static object * lean_del_core(object * o, object * todo) {
    uint8 tag = lean_ptr_tag(o);
    if (LEAN_LIKELY(tag <= LeanMaxCtorTag)) {
        LR_WL("visit", o, nullptr, 0, 0, 0);
        object ** it  = lean_ctor_obj_cptr(o);
        object ** end = it + lean_ctor_num_objs(o);
        for (; it != end; ++it) {
            LR_WL("field", o, *it, (unsigned)(it - lean_ctor_obj_cptr(o)), 0, 0);
            dec(*it, todo);
        }
        LR_WL("free", o, nullptr, 0, 0, 0); /* BEFORE actual free */
        lean_free_small_object(o);
        return todo;
    } else {
        return lean_del_core_other(o, tag, todo);
    }
}''')
    output.write_text(s)
    print(f"worklist_pinned_source=commit:{COMMIT} object_cpp_blob:{BLOB}")
    print("worklist_instrumentation=ORIGINAL_CPP_SOURCE_WITH_EIGHT_GUARDED_TRACE_HOOKS")
    print("worklist_normal_runtime=UNCHANGED")

if __name__ == "__main__":
    main()
