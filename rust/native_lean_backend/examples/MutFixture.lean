import NativeRust

namespace MutFixture
inductive PairLike where
  | empty
  | one (value : Nat)
  | two (left right : Nat)

def rotate (x : PairLike) : PairLike :=
  match x with
  | .empty => .empty
  | .one a => .two a (a + 1)
  | .two a b => .two b a

def first (x : PairLike) : Nat :=
  match x with
  | .empty => 0
  | .one a => a
  | .two a _ => a

def unique (a b : Nat) : Nat :=
  first (rotate (.two a b))

def shared (a b : Nat) : Nat :=
  let original := PairLike.two a b
  first (rotate original) + first original
end MutFixture

-- Temporary source-IR diagnosis of source RC order and alias identities.
open Lean Elab Command
run_cmd do
  let targets : Array Lean.Name := #[
    `MutFixture.unique, `MutFixture.shared, `MutFixture.rotate, `MutFixture.first
  ]
  for target in targets do
    let decl? ← liftCoreM do
      if (← Lean.IR.findDecl target).isNone then
        Lean.Compiler.compile #[target]
      Lean.IR.findDecl target
    if let some decl := decl? then
      logInfo s!"RC_SOURCE_IR {target}:\n{Lean.IR.formatDecl decl |>.pretty}"

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
