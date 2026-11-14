import NativeRust

namespace RecursiveCtor
inductive Chain where
| nil
| cons (head : Nat) (tail : Chain)

def fromNat : Nat → Chain
| 0 => .nil
| n + 1 => .cons (n + 1) (fromNat n)

def sum : Chain → Nat
| .nil => 0
| .cons n xs => n + sum xs

def checksum (n : Nat) : Nat := sum (fromNat n)
end RecursiveCtor

#native_rust_package [RecursiveCtor.checksum] to "examples/recursive-package"

open Lean Elab Command
run_cmd do
  let mut code := "use lean_generated::*;\n#[test] fn recursive_constructors() {\n"
  for i in [:64] do
    code := code ++ s!"assert_eq!(checksum(__LeanValue::nat_from_decimal(\"{i}\")).nat_to_decimal(), \"{RecursiveCtor.checksum i}\");\n"
  code := code ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/recursive-package/tests"
  liftIO <| IO.FS.writeFile "examples/recursive-package/tests/recursion.rs" code
