import NativeRust

-- This imported Lean 4.34.1 declaration is not reproduced or modified.
-- First check the original library's behavior independently.
#guard (String.intercalate ":" ["a", "b"] == "a:b")

-- Compile the actual imported symbol, not a hand-rewritten substitute.
#native_rust_closure String.intercalate as "public_root" to "examples/probe_StringIntercalate.rs"
