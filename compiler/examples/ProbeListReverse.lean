import NativeRust

-- This imported Lean 4.34.1 declaration is not reproduced or modified.
-- First check the original library's behavior independently.
#guard (List.reverse ([1, 2, 3] : List Nat) == [3, 2, 1])

-- Compile the actual imported symbol, not a hand-rewritten substitute.
#native_rust_closure List.reverse as "public_root" to "examples/probe_ListReverse.rs"
