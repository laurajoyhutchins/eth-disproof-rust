import NativeRust

-- This imported Lean 4.34.1 declaration is not reproduced or modified.
-- First check the original library's behavior independently.
#guard (Nat.gcd 84 30 == 6)

-- Compile the actual imported symbol, not a hand-rewritten substitute.
#native_rust_closure Nat.gcd as "public_root" to "examples/probe_NatGcd.rs"
