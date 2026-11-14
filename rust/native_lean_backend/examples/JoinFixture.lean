import NativeRust

namespace JoinFixture
  def join (x y : UInt64) : UInt64 :=
    let z := if x < y then x + 1 else y * 3
    z + 5
  def nested (x y : UInt64) : UInt64 :=
    let z := if x < y then (if x == 0 then y + 1 else x + 2) else (y + 1)
    z + x
end JoinFixture

#native_rust_closure JoinFixture.join as "join" to "examples/generated_join.rs"
#native_rust_closure JoinFixture.nested as "nested" to "examples/generated_nested_join.rs"

open Lean Elab Command
run_cmd do
  let mut test := "{\n"
  let mut state : UInt64 := 0xD1A5BB20DFAED731
  for i in [:128] do
    state := state * 6364136223846793005 + 1442695040888963407
    let a : UInt64 := if i < 4 then UInt64.ofNat i else state
    let b : UInt64 := if i < 4 then UInt64.ofNat (4 - i) else state + 1
    test := test ++ s!"assert_eq!(join({a.toNat}u64,{b.toNat}u64),{(JoinFixture.join a b).toNat}u64);\n"
    test := test ++ s!"assert_eq!(nested({a.toNat}u64,{b.toNat}u64),{(JoinFixture.nested a b).toNat}u64);\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_join_differential.rs" test
  logInfo "Generated 256 Lean-evaluated join-point conformance assertions"
