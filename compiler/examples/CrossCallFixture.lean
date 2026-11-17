import NativeRust
open Lean Elab Command

namespace CrossCallFixture

inductive Pair where
  | empty
  | one (value : Nat)
  | two (left right : Nat)

-- Force genuine interprocedural IR rather than a source-level inlining test.
@[noinline] def identity (p : Pair) : Pair := p

@[noinline] def rotate (p : Pair) : Pair :=
  match p with
  | .empty => .empty
  | .one a => .two a (a + 1)
  | .two a b => .two b a

@[noinline] def first (p : Pair) : Nat :=
  match p with
  | .empty => 0
  | .one a => a
  | .two a _ => a

@[noinline] def combine (x y : Pair) : Nat :=
  first x + first y

-- Unique temporary passes through two compiled function boundaries.
def consumed (a b : Nat) : Nat :=
  first (rotate (identity (.two a b)))

-- Source aliases must keep the earlier constructor observable after a call.
def retained (a b : Nat) : Nat :=
  let original := Pair.two a b
  first (rotate original) + first original

-- Returning an object from a callee and retaining its input exercises sharing.
def returnedAlias (a b : Nat) : Nat :=
  let original := Pair.two a b
  let alias := identity original
  first (rotate alias) + first original

-- Repeated uses of one argument at a call boundary prohibit a move.
def repeated (a b : Nat) : Nat :=
  let original := Pair.two a b
  combine original original

end CrossCallFixture

#native_rust_package [
  CrossCallFixture.consumed,
  CrossCallFixture.retained,
  CrossCallFixture.returnedAlias,
  CrossCallFixture.repeated
] to "examples/cross-call-package"

run_cmd do
  let mut text := "use lean_generated::*;\n#[test] fn cross_call_differential() {\n"
  let mut xs : Array Nat := #[0, 1, 2, 3, 7, 2^64 + 9, 2^256 + 11]
  for i in [:121] do xs := xs.push (i * i + i + 42)
  for a in xs do
    let b := a + 3
    let left := s!"__LeanValue::nat_from_decimal(\"{a}\")"
    let right := s!"__LeanValue::nat_from_decimal(\"{b}\")"
    text := text ++ s!"assert_eq!(consumed({left}, {right}).nat_to_decimal(), \"{CrossCallFixture.consumed a b}\");\n"
    text := text ++ s!"assert_eq!(retained({left}, {right}).nat_to_decimal(), \"{CrossCallFixture.retained a b}\");\n"
    text := text ++ s!"assert_eq!(returnedAlias({left}, {right}).nat_to_decimal(), \"{CrossCallFixture.returnedAlias a b}\");\n"
    text := text ++ s!"assert_eq!(repeated({left}, {right}).nat_to_decimal(), \"{CrossCallFixture.repeated a b}\");\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/cross-call-package/tests"
  liftIO <| IO.FS.writeFile "examples/cross-call-package/tests/cross_call.rs" text
  logInfo "Generated 512 Lean-evaluated interprocedural ownership comparisons"
