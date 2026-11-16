import NativeRust
import MutKernels

#native_rust_package [MutFixture.unique, MutFixture.shared] to "examples/mut-package"

open Lean Elab Command
run_cmd do
  let mut code := "use lean_generated::*;\n#[test] fn optimized_mutation() {\n"
  let mut xs : Array Nat := #[0, 1, 2, 3, 4, 7, 2^64+9, 2^256+11]
  for i in [:80] do xs := xs.push (i * i + 42)
  for a in xs do
    let b := a + 3
    code := code ++ s!"assert_eq!(unique(__LeanValue::nat_from_decimal(\"{a}\"), __LeanValue::nat_from_decimal(\"{b}\")).nat_to_decimal(), \"{MutFixture.unique a b}\");\n"
    code := code ++ s!"assert_eq!(shared(__LeanValue::nat_from_decimal(\"{a}\"), __LeanValue::nat_from_decimal(\"{b}\")).nat_to_decimal(), \"{MutFixture.shared a b}\");\n"
  code := code ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/mut-package/tests"
  liftIO <| IO.FS.writeFile "examples/mut-package/tests/optimized_mutation.rs" code
  logInfo s!"Generated {xs.size * 2} optimized constructor mutation comparisons"
