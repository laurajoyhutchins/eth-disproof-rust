import NativeRust

namespace CustomCtor
inductive Event where
| quiet
| value (n : Nat)
| pair (x y : Nat)
| triple (x y z : Nat)

def encode (n : Nat) : Event :=
  if n == 0 then .quiet
  else if n == 1 then .value n
  else if n == 2 then .pair n (n + 1)
  else .triple n (n + 1) (n + 2)

def checksum (event : Event) : Nat :=
  match event with
  | .quiet => 11
  | .value n => n + 13
  | .pair x y => x + y
  | .triple x y z => x + y + z

def roundTrip (n : Nat) : Nat := checksum (encode n)
end CustomCtor

def CustomCtor.taggedDefault (n : Nat) : Nat :=
  match encode n with
  | .quiet => 77
  | _ => 88

#native_rust_package [CustomCtor.roundTrip, CustomCtor.taggedDefault] to "examples/custom-package"

open Lean Elab Command
run_cmd do
  let mut code := "use lean_generated::*;\n#[test] fn custom_constructors() {\n"
  let mut xs : Array Nat := #[0, 1, 2, 3, 4, 5, 100, 2^64+5, 2^128+11]
  for i in [:128] do
    xs := xs.push (i * i + i * 33)
  for x in xs do
    code := code ++ s!"assert_eq!(roundTrip(__LeanValue::nat_from_decimal(\"{x}\")).nat_to_decimal(), \"{CustomCtor.roundTrip x}\");\n"
    code := code ++ s!"assert_eq!(taggedDefault(__LeanValue::nat_from_decimal(\"{x}\")).nat_to_decimal(), \"{CustomCtor.taggedDefault x}\");\n"
  code := code ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/custom-package/tests"
  liftIO <| IO.FS.writeFile "examples/custom-package/tests/custom_constructors.rs" code
  logInfo s!"Generated {xs.size * 2} custom-constructor differential checks"
