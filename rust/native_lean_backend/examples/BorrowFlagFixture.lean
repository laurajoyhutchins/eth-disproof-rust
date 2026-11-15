import NativeRust
open Lean Elab Command

namespace BorrowFlagFixture
  @[noinline] def passthrough (x : Nat) : Nat := x
end BorrowFlagFixture

-- Construct genuine Lean.IR.Param values in the pinned Lean process.
-- An owned observation must emit; the otherwise identical borrowed
-- observation must refuse. This checks the packed Bool through the
-- production backend without introducing a second diagnostic entry point.
run_cmd do
  let owned : Lean.IR.Param :=
    { x := ⟨0⟩, borrow := false, ty := .object }
  let borrowed : Lean.IR.Param := { owned with borrow := true }
  let decl? ← liftCoreM do
    if (← Lean.IR.findDecl `BorrowFlagFixture.passthrough).isNone then
      Lean.Compiler.compile #[`BorrowFlagFixture.passthrough]
    Lean.IR.findDecl `BorrowFlagFixture.passthrough
  let some (.fdecl name _ _ _ info) := decl?
    | throwError "missing executable Lean compiler IR for borrow flag probe"

  let observed : Lean.IR.FnBody :=
    .vdecl ⟨1⟩ .uint8 (.isShared ⟨0⟩) (.ret (.var ⟨1⟩))
  let forbidden : Lean.IR.Decl :=
    .fdecl name #[borrowed] .uint8 observed info
  let refused := NativeRust.emit forbidden "borrowed_observation"
  unless refused.startsWith "ERROR\n" &&
      (refused.splitOn "borrowed parameter").length > 1 do
    throwError "borrowed-param isShared must fail closed: {refused}"

  -- Distinguish ownership-policy refusal from an unconditional ban on
  -- isShared; this only asserts the bounded emitted path is still available.
  let permitted : Lean.IR.Decl :=
    .fdecl name #[owned] .uint8 observed info
  let accepted := NativeRust.emit permitted "owned_observation"
  unless accepted.startsWith "OK\n" do
    throwError "owned-param source IR unexpectedly refused: {accepted}"
  logInfo "Pinned Param.borrow ABI and source-IR sharedness refusal passed"
