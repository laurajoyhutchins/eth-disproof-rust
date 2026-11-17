import NativeRust

open Lean Elab Command

namespace TransferContractFixture
  @[noinline] def seed (x : Nat) : Nat := x
end TransferContractFixture

/-!
Actual Lean.IR.Decl/Param/FnBody constructors are passed directly to the
production Reader. The point is source ownership, not merely whether the
two Rust Rc aliases happen to make the generated code memory safe.
-/
run_cmd do
  let found? ← liftCoreM do
    if (← Lean.IR.findDecl `TransferContractFixture.seed).isNone then
      Lean.Compiler.compile #[`TransferContractFixture.seed]
    Lean.IR.findDecl `TransferContractFixture.seed
  let some (.fdecl _ _ _ _ info) := found?
    | throwError "missing pinned original IR for transfer contract fixture"

  let caller := `TransferContractFixture.forward
  let consume := `TransferContractFixture.consumeTwo
  let observe := `TransferContractFixture.observeBorrowed
  let borrowed : Lean.IR.Param :=
    { x := ⟨0⟩, ty := .object, borrow := true }
  let owned : Lean.IR.Param := { borrowed with borrow := false }
  let ownedOther : Lean.IR.Param :=
    { x := ⟨1⟩, ty := .object, borrow := false }
  let borrowOther : Lean.IR.Param :=
    { ownedOther with borrow := true }
  let doneBody : Lean.IR.FnBody :=
    .vdecl ⟨7⟩ .uint8 (.lit (.num 3)) (.ret (.var ⟨7⟩))

  -- Both source formal references are consumed. Passing the SAME actual
  -- twice is legal only when the caller owns two distinct source credits.
  let consuming : Lean.IR.Decl :=
    .fdecl consume #[owned, ownedOther] .uint8
      (.dec ⟨0⟩ 1 true false
        (.dec ⟨1⟩ 1 true false doneBody)) info

  let callOnce : Lean.IR.FnBody :=
    .inc ⟨0⟩ 1 true false
      (.vdecl ⟨2⟩ .uint8
        (.fap consume #[.var ⟨0⟩, .var ⟨0⟩])
        (.ret (.var ⟨2⟩)))
  let callOnceResult := NativeRust.emitModule
    #[consuming, .fdecl caller #[borrowed] .uint8 callOnce info]
    caller "double_owned_direct_call_one_credit"
  unless callOnceResult.startsWith "ERROR\n" &&
      (callOnceResult.splitOn "argument 1").length > 1 do
    throwError "second owned direct argument acquired a phantom credit: {callOnceResult}"

  let callTwice : Lean.IR.FnBody :=
    .inc ⟨0⟩ 2 true false
      (.vdecl ⟨2⟩ .uint8
        (.fap consume #[.var ⟨0⟩, .var ⟨0⟩])
        (.ret (.var ⟨2⟩)))
  let callTwiceResult := NativeRust.emitModule
    #[consuming, .fdecl caller #[borrowed] .uint8 callTwice info]
    caller "double_owned_direct_call_two_credits"
  unless callTwiceResult.startsWith "OK\n" &&
      (callTwiceResult.splitOn ".source_inc(2, true, false)").length > 1 do
    throwError "two source inc credits did not authorize two owned call arguments: {callTwiceResult}"

  -- Borrowed formals can read the same protected object twice without
  -- either the caller or the callee creating a source ownership credit.
  let observing : Lean.IR.Decl :=
    .fdecl observe #[borrowed, borrowOther] .uint8 doneBody info
  let borrowedDoubleCall : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .uint8
      (.fap observe #[.var ⟨0⟩, .var ⟨0⟩])
      (.ret (.var ⟨2⟩))
  let borrowedResult := NativeRust.emitModule
    #[observing, .fdecl caller #[borrowed] .uint8 borrowedDoubleCall info]
    caller "double_borrowed_direct_call"
  unless borrowedResult.startsWith "OK\n" do
    throwError "two borrowed direct arguments incorrectly consumed ownership: {borrowedResult}"

  -- A *join* can likewise receive the same source object in two owned
  -- slots only when two explicit references have been created beforehand.
  let joinA : Lean.IR.Param := { x := ⟨4⟩, ty := .object, borrow := false }
  let joinB : Lean.IR.Param := { x := ⟨5⟩, ty := .object, borrow := false }
  let joinBody : Lean.IR.FnBody :=
    .dec ⟨4⟩ 1 true false
      (.dec ⟨5⟩ 1 true false doneBody)
  let joinOnce : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[joinA, joinB] joinBody
      (.inc ⟨0⟩ 1 true false
        (.jmp ⟨9⟩ #[.var ⟨0⟩, .var ⟨0⟩]))
  let joinOnceResult := NativeRust.emit
    (.fdecl caller #[borrowed] .uint8 joinOnce info)
    "double_owned_join_one_credit"
  unless joinOnceResult.startsWith "ERROR\n" &&
      (joinOnceResult.splitOn "join point 9 argument 1").length > 1 do
    throwError "second owned join argument acquired a phantom credit: {joinOnceResult}"

  let joinTwice : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[joinA, joinB] joinBody
      (.inc ⟨0⟩ 2 true false
        (.jmp ⟨9⟩ #[.var ⟨0⟩, .var ⟨0⟩]))
  let joinTwiceResult := NativeRust.emit
    (.fdecl caller #[borrowed] .uint8 joinTwice info)
    "double_owned_join_two_credits"
  unless joinTwiceResult.startsWith "OK\n" &&
      (joinTwiceResult.splitOn ".source_inc(2, true, false)").length > 1 do
    throwError "two explicit source credits did not authorize two owned join formals: {joinTwiceResult}"

  let borrowedJoinA : Lean.IR.Param := { joinA with borrow := true }
  let borrowedJoinB : Lean.IR.Param := { joinB with borrow := true }
  let doubleBorrowedJoin : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[borrowedJoinA, borrowedJoinB] doneBody
      (.jmp ⟨9⟩ #[.var ⟨0⟩, .var ⟨0⟩])
  let doubleBorrowedResult := NativeRust.emit
    (.fdecl caller #[borrowed] .uint8 doubleBorrowedJoin info)
    "double_borrowed_join_no_credits"
  unless doubleBorrowedResult.startsWith "OK\n" do
    throwError "borrowed join formals unexpectedly acquired owned transfer requirements: {doubleBorrowedResult}"

  -- The second owned transfer remains illegal even if the Rust runtime
  -- would have a live Rc allocation for both variable aliases.
  logInfo "Pinned Lean.IR ownership transfer: double-arg direct call and join require two real source inc credits; borrowed formals require none"
