import NativeRust

-- Decimal constants are extracted from original Lean.IR.LitVal.num objects.
-- No compiler-IR serialization and no machine-word truncation are permitted.
namespace LargeNatFixture
  def addHuge (n : Nat) : Nat := n + 1606938044258990275541962092341162602522202993782792835301383
  def mulHuge (n : Nat) : Nat := n * 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084115
  def divideHuge (n : Nat) : Nat := n / 6277101735386680763835789423207666416102355444464034512907
  def conditional (n : Nat) : Nat :=
    if n < 340282366920938463463374607431768211461 then n + 115792089237316195423570985008687907853269984665640564039457584007913129639953 else n - 79228162514264337593543950339
end LargeNatFixture

#native_rust_package [LargeNatFixture.addHuge, LargeNatFixture.mulHuge,
  LargeNatFixture.divideHuge, LargeNatFixture.conditional] to "examples/large-nat-package"

open Lean Elab Command
run_cmd do
  let values : Array Nat := #[0, 1, 2, 7, 19, 42, 2^32-1, 2^64, 2^96+3,
    2^128+4, 2^128+5, 2^128+6, 2^192, 2^200+7, 2^256+17,
    2^512+19, 2^1024+57, 2^2048-1, 2^4096+71]
  let mut test := "use lean_generated::*;\n#[test] fn closed_nat_literal_differential() {\n"
  for n in values do
    let input := s!"__LeanValue::nat_from_decimal(\"{n}\")"
    test := test ++ s!"assert_eq!(addHuge({input}).nat_to_decimal(), \"{LargeNatFixture.addHuge n}\");\n"
    test := test ++ s!"assert_eq!(mulHuge({input}).nat_to_decimal(), \"{LargeNatFixture.mulHuge n}\");\n"
    test := test ++ s!"assert_eq!(divideHuge({input}).nat_to_decimal(), \"{LargeNatFixture.divideHuge n}\");\n"
    test := test ++ s!"assert_eq!(conditional({input}).nat_to_decimal(), \"{LargeNatFixture.conditional n}\");\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/large-nat-package/tests"
  liftIO <| IO.FS.writeFile "examples/large-nat-package/tests/literals.rs" test
  logInfo s!"Generated {values.size * 4} independently Lean-evaluated large-constant assertions"
