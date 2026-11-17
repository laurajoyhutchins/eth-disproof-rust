import NativeRust
import PropertyDef

#native_rust_closure Property.hop as "property_hop" to "examples/generated_property.rs"

open Lean Elab Command

-- All oracle outputs come from the original Lean declaration, independently
-- of codegen. Fixed seeds and candidate shrink ladders make failures replayable.
run_cmd do
  let mut cases := "pub const CASES: &[(u64, u64, u64, u64, u64)] = &[\n"
  let mut state : UInt64 := 0x9E3779B97F4A7C15
  let edges : Array UInt64 := #[0, 1, 2, 3, 7, 42, UInt64.ofNat (2^32-1),
                                UInt64.ofNat (2^32), UInt64.ofNat (2^63),
                                UInt64.ofNat (2^64-1)]
  for seed in [:128] do
    state := state * 6364136223846793005 + 1442695040888963407
    let x := if seed < edges.size then edges[seed]! else state
    let fuel := UInt64.ofNat (seed % 17)
    for step in [:8] do
      let shrunkFuel := UInt64.ofNat (fuel.toNat / (step + 1))
      let shrunkX := UInt64.ofNat (x.toNat / (2 ^ step))
      let result := Property.hop shrunkFuel shrunkX
      cases := cases ++ s!"    ({seed}u64, {shrunkFuel.toNat}u64, {shrunkX.toNat}u64, {result.toNat}u64, {step}u64),\n"
  cases := cases ++ "];\n"
  liftIO <| IO.FS.writeFile "examples/generated_property_cases.rs" cases
  logInfo "Generated 1024 independently evaluated property/shrink cases with pinned seeds"
