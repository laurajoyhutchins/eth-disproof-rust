import NativeRust
open Lean Elab Command

namespace BorrowFlagFixture
  @[noinline] def passthrough (x : Nat) : Nat := x

  -- An original compiled Lean program, not a constructed IR declaration.
  -- The function only inspects its input constructor tag and never takes
  -- ownership of the frame or one of its fields.
  inductive Frame where
    | vacant
    | node (left right : Nat)
  @[noinline] def inspectTag (value : Frame) : UInt8 :=
    match value with
    | .vacant => 0
    | .node .. => 1
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

  -- Verify that actual pinned Lean compiler output produces a borrowed
  -- formal. This protects the analysis against only testing invented flags.
  let sourceDecl? ← liftCoreM do
    if (← Lean.IR.findDecl `BorrowFlagFixture.inspectTag).isNone then
      Lean.Compiler.compile #[`BorrowFlagFixture.inspectTag]
    Lean.IR.findDecl `BorrowFlagFixture.inspectTag
  let some (.fdecl _ sourceParams _ _ _) := sourceDecl?
    | throwError "missing original Lean IR for borrowed tag inspector"
  unless sourceParams.size == 1 && sourceParams[0]!.borrow do
    throwError "original Lean compiler did not mark read-only Frame parameter as borrowed"

  -- Direct source-ownership permissions are independent of Rust Rc aliases.
  -- Borrowed x begins with zero transferable references. The source-only
  -- instructions below either grant ownership via inc or attempt to move
  -- ownership the caller retained. These exercise the canonical emitter.
  let escaped := NativeRust.emit
    (.fdecl name #[borrowed] .object (.ret (.var ⟨0⟩)) info)
    "borrowed_escaped"
  unless escaped.startsWith "ERROR\n" &&
      (escaped.splitOn "owned transfer in return value").length > 1 do
    throwError "borrowed object returned without inc: {escaped}"
  let retained := NativeRust.emit
    (.fdecl name #[borrowed] .object
      (.inc ⟨0⟩ 1 true false (.ret (.var ⟨0⟩))) info) "borrowed_retained"
  unless retained.startsWith "OK\n" &&
      (retained.splitOn ".source_inc(1, true, false)").length > 1 do
    throwError "explicit borrowed-to-owned source inc refused: {retained}"

  let badRelease := NativeRust.emit
    (.fdecl name #[borrowed] .uint8
      (.dec ⟨0⟩ 1 true false
        (.vdecl ⟨1⟩ .uint8 (.lit (.num 3)) (.ret (.var ⟨1⟩)))) info)
    "borrowed_dec"
  unless badRelease.startsWith "ERROR\n" &&
      (badRelease.splitOn "dec without owned inc").length > 1 do
    throwError "borrowed param consumed without retained ownership: {badRelease}"
  let balanced := NativeRust.emit
    (.fdecl name #[borrowed] .uint8
      (.inc ⟨0⟩ 1 true false
        (.dec ⟨0⟩ 1 true false
          (.vdecl ⟨1⟩ .uint8 (.lit (.num 3)) (.ret (.var ⟨1⟩))))) info)
    "borrowed_balanced"
  unless balanced.startsWith "OK\n" do
    throwError "balanced borrowed inc/dec unexpectedly refused: {balanced}"

  let ownedName := `BorrowFlagFixture.ownedCallee
  let borrowedName := `BorrowFlagFixture.borrowedCallee
  let callerName := `BorrowFlagFixture.caller
  let simple : Lean.IR.FnBody :=
    .vdecl ⟨1⟩ .uint8 (.lit (.num 3)) (.ret (.var ⟨1⟩))
  let ownedCallee : Lean.IR.Decl :=
    .fdecl ownedName #[owned] .uint8 simple info
  let borrowedCallee : Lean.IR.Decl :=
    .fdecl borrowedName #[borrowed] .uint8 simple info

  let unsafeCall : Lean.IR.Decl :=
    .fdecl callerName #[borrowed] .uint8
      (.vdecl ⟨1⟩ .uint8 (.fap ownedName #[.var ⟨0⟩]) (.ret (.var ⟨1⟩))) info
  let refusedCall :=
    NativeRust.emitModule #[ownedCallee, unsafeCall] callerName "borrowed_caller"
  unless refusedCall.startsWith "ERROR\n" &&
      (refusedCall.splitOn "call to BorrowFlagFixture.ownedCallee argument 0").length > 1 do
    throwError "borrowed argument consumed by owned direct callee: {refusedCall}"

  let validCall : Lean.IR.Decl :=
    .fdecl callerName #[borrowed] .uint8
      (.vdecl ⟨1⟩ .uint8 (.fap borrowedName #[.var ⟨0⟩]) (.ret (.var ⟨1⟩))) info
  let forwarded := NativeRust.emitModule #[borrowedCallee, validCall]
    callerName "borrowed_caller"
  unless forwarded.startsWith "OK\n" &&
      (forwarded.splitOn "x_0.compiler_alias()").length > 1 do
    throwError "borrowed-to-borrowed source callee or alias was lost: {forwarded}"

  let allowedOwnedCall : Lean.IR.Decl :=
    .fdecl callerName #[borrowed] .uint8
      (.inc ⟨0⟩ 1 true false
        (.vdecl ⟨1⟩ .uint8 (.fap ownedName #[.var ⟨0⟩]) (.ret (.var ⟨1⟩)))) info
  let forwardedOwned := NativeRust.emitModule #[ownedCallee, allowedOwnedCall]
    callerName "owned_caller"
  unless forwardedOwned.startsWith "OK\n" do
    throwError "source-inc-backed owned call unexpectedly refused: {forwardedOwned}"

  let captured : Lean.IR.Decl :=
    .fdecl callerName #[borrowed] .object
      (.vdecl ⟨1⟩ .object (.pap ownedName #[.var ⟨0⟩]) (.ret (.var ⟨1⟩))) info
  let capturedResult := NativeRust.emitModule #[ownedCallee, captured] callerName "borrowed_capture"
  unless capturedResult.startsWith "ERROR\n" &&
      (capturedResult.splitOn "partial application capture").length > 1 do
    throwError "borrowed PAP capture without ownership was accepted: {capturedResult}"

  let badBranch : Lean.IR.FnBody :=
    .case `Bool ⟨1⟩ .object #[.default (.ret (.var ⟨0⟩))]
  let branchDecl : Lean.IR.Decl :=
    .fdecl name #[borrowed, { x := ⟨1⟩, borrow := false, ty := .uint8 }]
      .object badBranch info
  let branchResult := NativeRust.emit branchDecl "borrowed_branch_escape"
  unless branchResult.startsWith "ERROR\n" &&
      (branchResult.splitOn "owned transfer in return value").length > 1 do
    throwError "branch-hidden borrowed return without inc accepted: {branchResult}"
  logInfo "Pinned borrowed Param: direct transfer, balanced inc, direct-call ABI, PAP and branch refusal"
  logInfo "Pinned Param.borrow ABI and source-IR sharedness refusal passed"
