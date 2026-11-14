import NativeRust

namespace NatFixture
 def addN (a b : Nat) : Nat := a + b
 def subN (a b : Nat) : Nat := a - b
 def mulN (a b : Nat) : Nat := a * b
 def divN (a b : Nat) : Nat := a / b
 def modN (a b : Nat) : Nat := a % b
 def eqN (a b : Nat) : Bool := a == b
 def ltN (a b : Nat) : Bool := a < b
 def leN (a b : Nat) : Bool := a ≤ b
 def maxN (a b : Nat) : Nat := if a < b then b else a
 def addFive (a : Nat) : Nat := a + 5
end NatFixture

#native_rust_package [NatFixture.addN, NatFixture.subN, NatFixture.mulN, NatFixture.divN, NatFixture.modN,
  NatFixture.eqN, NatFixture.ltN, NatFixture.leN,
  NatFixture.maxN, NatFixture.addFive] to "examples/nat-package"

open Lean Elab Command
run_cmd do
  let mut text := "use lean_generated::*;\n#[test] fn nat_differential() {\n"
  let values : Array Nat := #[0, 1, 2, 3, 5, 7, 42, 255, 256, 65535,
    2^31-1, 2^32, 2^63, 2^64-1, 2^64, 2^65+1,
    2^120, 2^128-1, 2^128, 2^192+17,
    2^256-1, 2^256, 2^512+199, 2^1024+57]
  for a in values do
    let aa := s!"__LeanValue::nat_from_decimal(\"{a}\")"
    text := text ++ s!"assert_eq!(addFive({aa}).nat_to_decimal(), \"{a + 5}\");\n"
    for b in values do
      let bb := s!"__LeanValue::nat_from_decimal(\"{b}\")"
      let pair := s!"{aa}, {bb}"
      text := text ++ s!"assert_eq!(addN({pair}).nat_to_decimal(), \"{a + b}\");\n"
      text := text ++ s!"assert_eq!(subN({pair}).nat_to_decimal(), \"{a - b}\");\n"
      text := text ++ s!"assert_eq!(mulN({pair}).nat_to_decimal(), \"{a * b}\");\n"
      text := text ++ s!"assert_eq!(divN({pair}).nat_to_decimal(), \"{a / b}\");\n"
      text := text ++ s!"assert_eq!(modN({pair}).nat_to_decimal(), \"{a % b}\");\n"
      text := text ++ s!"assert_eq!(eqN({pair}), {if a == b then 1 else 0}u8);\n"
      text := text ++ s!"assert_eq!(ltN({pair}), {if a < b then 1 else 0}u8);\n"
      text := text ++ s!"assert_eq!(leN({pair}), {if a ≤ b then 1 else 0}u8);\n"
      text := text ++ s!"assert_eq!(maxN({pair}).nat_to_decimal(), \"{max a b}\");\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/nat-package/tests"
  liftIO <| IO.FS.writeFile "examples/nat-package/tests/nat_differential.rs" text
  logInfo "Generated 5208 Lean-evaluated Nat assertions over 0..1024-bit operands"
