import NativeRust
open Lean Elab Command

namespace SumFixture
  def construct (x y : UInt64) : Sum UInt64 UInt64 :=
    if x < y then .inl x else .inr y
  def extract (v : Sum UInt64 UInt64) : UInt64 :=
    match v with
    | .inl x => x + 5
    | .inr y => y * 7
  def roundTrip (x y : UInt64) : UInt64 := extract (construct x y)
  def nested (x y : UInt64) : UInt64 :=
    let wrapped : Option (Sum UInt64 UInt64) := some (construct x y)
    match wrapped with
    | none => 999
    | some (.inl v) => v + 19
    | some (.inr w) => w - 13
end SumFixture

#native_rust_package [SumFixture.roundTrip, SumFixture.nested] to "examples/sum-package"

run_cmd do
  let mut text := "use lean_generated::*;\n#[test] fn sum_differential() {\n"
  let mut state : UInt64 := 0xD0A5E1CAFFEEBEEF
  for i in [:512] do
    state := state * 6364136223846793005 + 1442695040888963407
    let x : UInt64 := if i < 8 then UInt64.ofNat i else state
    let y : UInt64 := if i < 8 then UInt64.ofNat (7 - i) else state + 1
    text := text ++ s!"assert_eq!(roundTrip({x.toNat}u64, {y.toNat}u64), {(SumFixture.roundTrip x y).toNat}u64);\n"
    text := text ++ s!"assert_eq!(nested({x.toNat}u64, {y.toNat}u64), {(SumFixture.nested x y).toNat}u64);\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/sum-package/tests"
  liftIO <| IO.FS.writeFile "examples/sum-package/tests/sum.rs" text
  logInfo "Generated 1024 Lean-evaluated Sum comparisons"
