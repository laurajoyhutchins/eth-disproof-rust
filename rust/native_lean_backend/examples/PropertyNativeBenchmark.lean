import PropertyDef

-- Run exactly the original Property.hop on the same deterministic input
-- stream as the emitted Rust. No reimplementation of the algorithm.
def checksum (iterations : Nat) : UInt64 := Id.run do
  let mut state : UInt64 := 0x9E3779B97F4A7C15
  let mut result : UInt64 := 0
  for i in [:iterations] do
    state := state * 6364136223846793005 + 1442695040888963407
    let fuel := UInt64.ofNat (i % 17)
    result := result + Property.hop fuel state
  return result

def main : IO Unit := do
  IO.println (checksum 16384).toNat
