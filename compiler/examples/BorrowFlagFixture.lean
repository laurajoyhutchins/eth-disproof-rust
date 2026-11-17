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

  -- Pointer projections are source borrows, not owned values. Provenance
  -- follows the actual IR VarId, including a second projection.
  let projected : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩) (.ret (.var ⟨2⟩))
  let projectedRefusal := NativeRust.emit
    (.fdecl name #[borrowed] .object projected info) "borrowed_projected_escape"
  unless projectedRefusal.startsWith "ERROR\n" &&
      (projectedRefusal.splitOn "borrowed parameter x_2").length > 1 do
    throwError "unretained borrowed projection escaped: {projectedRefusal}"

  let projectedOwned : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩)))
  let projectedAllowed := NativeRust.emit
    (.fdecl name #[borrowed] .object projectedOwned info) "borrowed_projected_retained"
  unless projectedAllowed.startsWith "OK\n" &&
      (projectedAllowed.splitOn "x_2.source_inc(1, true, false)").length > 1 do
    throwError "source-retained borrowed projection refused: {projectedAllowed}"

  let nestedProjection : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.vdecl ⟨3⟩ .object (.proj 0 ⟨2⟩) (.ret (.var ⟨3⟩)))
  let nestedRefusal := NativeRust.emit
    (.fdecl name #[borrowed] .object nestedProjection info) "nested_projection"
  unless nestedRefusal.startsWith "ERROR\n" &&
      (nestedRefusal.splitOn "borrowed parameter x_3").length > 1 do
    throwError "transitive borrowed projection escaped: {nestedRefusal}"

  -- Join point formals have their own source Param.borrow bit. Passing a
  -- borrowed value into a borrowed formal is legal; returning it without
  -- an owned inc from inside that join is not.
  let joinBorrowed : Lean.IR.Param :=
    { x := ⟨4⟩, ty := .object, borrow := true }
  let joinOwned : Lean.IR.Param := { joinBorrowed with borrow := false }
  let joinEscaped : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[joinBorrowed] (.ret (.var ⟨4⟩))
      (.jmp ⟨9⟩ #[.var ⟨0⟩])
  let joinEscapeResult := NativeRust.emit
    (.fdecl name #[borrowed] .object joinEscaped info) "join_borrowed_escape"
  unless joinEscapeResult.startsWith "ERROR\n" &&
      (joinEscapeResult.splitOn "borrowed parameter x_4").length > 1 do
    throwError "borrowed join formal escaped without inc: {joinEscapeResult}"

  let joinSafe : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[joinBorrowed]
      (.vdecl ⟨5⟩ .uint8 (.lit (.num 1)) (.ret (.var ⟨5⟩)))
      (.jmp ⟨9⟩ #[.var ⟨0⟩])
  let joinForward := NativeRust.emit
    (.fdecl name #[borrowed] .uint8 joinSafe info) "join_borrowed_read"
  unless joinForward.startsWith "OK\n" do
    throwError "borrowed join-to-borrowed forwarding refused: {joinForward}"

  let ownedJoin : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[joinOwned] (.ret (.var ⟨4⟩))
      (.jmp ⟨9⟩ #[.var ⟨0⟩])
  let ownedJoinRefusal := NativeRust.emit
    (.fdecl name #[borrowed] .object ownedJoin info) "join_owned_without_inc"
  unless ownedJoinRefusal.startsWith "ERROR\n" &&
      (ownedJoinRefusal.splitOn "join point 9 argument 0").length > 1 do
    throwError "owned join transfer without inc was admitted: {ownedJoinRefusal}"

  let ownedJoinWithInc : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[joinOwned] (.ret (.var ⟨4⟩))
      (.inc ⟨0⟩ 1 true false (.jmp ⟨9⟩ #[.var ⟨0⟩]))
  let joinedOwned := NativeRust.emit
    (.fdecl name #[borrowed] .object ownedJoinWithInc info) "join_owned_with_inc"
  unless joinedOwned.startsWith "OK\n" do
    throwError "source-inc-backed owned join transfer refused: {joinedOwned}"

  let projectedJoin : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.jdecl ⟨9⟩ #[joinBorrowed] (.ret (.var ⟨4⟩))
        (.jmp ⟨9⟩ #[.var ⟨2⟩]))
  let projectedJoinRefusal := NativeRust.emit
    (.fdecl name #[borrowed] .object projectedJoin info) "join_projected_escape"
  unless projectedJoinRefusal.startsWith "ERROR\n" &&
      (projectedJoinRefusal.splitOn "borrowed parameter x_4").length > 1 do
    throwError "join dropped projected provenance: {projectedJoinRefusal}"

  let projectedJoinSafe : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.jdecl ⟨9⟩ #[joinBorrowed]
        (.inc ⟨4⟩ 1 true false (.ret (.var ⟨4⟩)))
        (.jmp ⟨9⟩ #[.var ⟨2⟩]))
  let projectedJoined := NativeRust.emit
    (.fdecl name #[borrowed] .object projectedJoinSafe info) "join_projected_retained"
  unless projectedJoined.startsWith "OK\n" do
    throwError "source-retained projection through borrowed join refused: {projectedJoined}"


  -- Source-protected child lifetime: these intentionally invalid programs
  -- are NEVER executed against Lean C because that would read freed memory.
  -- The native emitter must reject them before producing a Rust package.
  let deadChild : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.dec ⟨0⟩ 1 true false
        (.vdecl ⟨3⟩ .object (.proj 0 ⟨2⟩) (.ret (.var ⟨3⟩))))
  let deadChildResult := NativeRust.emit
    (.fdecl name #[owned] .object deadChild info) "parent_released_before_child_read"
  unless deadChildResult.startsWith "ERROR\n" &&
      (deadChildResult.splitOn "protecting parent release").length > 1 do
    throwError "child read after parent release was admitted: {deadChildResult}"

  let lateRetain : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.dec ⟨0⟩ 1 true false
        (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩))))
  let lateRetainResult := NativeRust.emit
    (.fdecl name #[owned] .object lateRetain info) "late_retained_child"
  unless lateRetainResult.startsWith "ERROR\n" &&
      (lateRetainResult.splitOn "protecting parent release").length > 1 do
    throwError "late inc resurrected a dead projected child: {lateRetainResult}"

  let earlyRetain : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.inc ⟨2⟩ 1 true false
        (.dec ⟨0⟩ 1 true false (.ret (.var ⟨2⟩))))
  let earlyRetainResult := NativeRust.emit
    (.fdecl name #[owned] .object earlyRetain info) "child_retained_before_parent_release"
  unless earlyRetainResult.startsWith "OK\n" do
    throwError "independently retained child lost after parent release: {earlyRetainResult}"

  let nestedDead : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.vdecl ⟨3⟩ .object (.proj 0 ⟨2⟩)
        (.dec ⟨0⟩ 1 true false
          (.inc ⟨3⟩ 1 true false (.ret (.var ⟨3⟩)))))
  let nestedDeadResult := NativeRust.emit
    (.fdecl name #[owned] .object nestedDead info) "nested_descendant_after_release"
  unless nestedDeadResult.startsWith "ERROR\n" &&
      (nestedDeadResult.splitOn "protecting parent release").length > 1 do
    throwError "nested descendant survived a dead source parent: {nestedDeadResult}"

  -- An intermediate field retained before root release protects its child.
  -- After retaining that grandchild independently, intermediate can drop.
  let nestedSafe : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.vdecl ⟨3⟩ .object (.proj 0 ⟨2⟩)
        (.inc ⟨2⟩ 1 true false
          (.dec ⟨0⟩ 1 true false
            (.inc ⟨3⟩ 1 true false
              (.dec ⟨2⟩ 1 true false (.ret (.var ⟨3⟩)))))))
  let nestedSafeResult := NativeRust.emit
    (.fdecl name #[owned] .object nestedSafe info) "grandchild_independently_retained"
  unless nestedSafeResult.startsWith "OK\n" do
    throwError "retained intermediate did not protect its child: {nestedSafeResult}"

  -- A borrowed formal remains protected by its caller's reference after
  -- releasing only a temporary IR.inc reference acquired inside the callee.
  let externallyProtected : Lean.IR.FnBody :=
    .inc ⟨0⟩ 1 true false
      (.dec ⟨0⟩ 1 true false
        (.vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
          (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩)))))
  let protectedResult := NativeRust.emit
    (.fdecl name #[borrowed] .object externallyProtected info) "caller_protected_parent"
  unless protectedResult.startsWith "OK\n" do
    throwError "temporary inc/dec incorrectly destroyed a borrowed parent: {protectedResult}"

  let parentMoved : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.vdecl ⟨3⟩ .uint8 (.fap ownedName #[.var ⟨0⟩])
        (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩))))
  let movedResult := NativeRust.emitModule
    #[ownedCallee, .fdecl callerName #[owned] .object parentMoved info]
    callerName "parent_transferred_to_owned_callee"
  unless movedResult.startsWith "ERROR\n" &&
      (movedResult.splitOn "protecting parent release").length > 1 do
    throwError "owned callee transfer left an unsafe child live: {movedResult}"

  let parentBorrowed : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.vdecl ⟨3⟩ .uint8 (.fap borrowedName #[.var ⟨0⟩])
        (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩))))
  let borrowedResult := NativeRust.emitModule
    #[borrowedCallee, .fdecl callerName #[owned] .object parentBorrowed info]
    callerName "parent_passed_to_borrowed_callee"
  unless borrowedResult.startsWith "OK\n" do
    throwError "borrowed callee falsely consumed its caller's parent: {borrowedResult}"

  -- A join body must be evaluated at its actual jump state, not at its
  -- lexical definition where the source parent may still be alive.
  let joinAfterRelease : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.jdecl ⟨9⟩ #[]
        (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩)))
        (.dec ⟨0⟩ 1 true false (.jmp ⟨9⟩ #[])))
  let joinDeadResult := NativeRust.emit
    (.fdecl name #[owned] .object joinAfterRelease info) "join_child_after_release"
  unless joinDeadResult.startsWith "ERROR\n" &&
      (joinDeadResult.splitOn "protecting parent release").length > 1 do
    throwError "join checked child at declaration instead of jump: {joinDeadResult}"

  let joinBeforeRelease : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.jdecl ⟨9⟩ #[]
        (.ret (.var ⟨2⟩))
        (.inc ⟨2⟩ 1 true false
          (.dec ⟨0⟩ 1 true false (.jmp ⟨9⟩ #[]))))
  let joinSafeResult := NativeRust.emit
    (.fdecl name #[owned] .object joinBeforeRelease info) "join_child_retained_before_release"
  unless joinSafeResult.startsWith "OK\n" do
    throwError "retained child lost ownership across join: {joinSafeResult}"

  -- The pinned Lean C runtime's del is shell-only. If exactly one source
  -- projection identifies a slot, its original owned reference can be
  -- transferred from the deleted shell to that projected child.
  let shellDeleted : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.del ⟨0⟩ (.ret (.var ⟨2⟩)))
  let deletedResult := NativeRust.emit
    (.fdecl name #[owned] .object shellDeleted info) "unique_shell_field_transfer"
  unless deletedResult.startsWith "OK\n" do
    throwError "unique field transfer through shell-only del was refused: {deletedResult}"

  let duplicateShellProjection : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.vdecl ⟨3⟩ .object (.proj 0 ⟨0⟩)
        (.del ⟨0⟩ (.ret (.var ⟨3⟩))))
  let duplicateShellResult := NativeRust.emit
    (.fdecl name #[owned] .object duplicateShellProjection info) "ambiguous_shell_field_owner"
  unless duplicateShellResult.startsWith "ERROR\n" &&
      (duplicateShellResult.splitOn "protecting parent release").length > 1 do
    throwError "duplicate projections fabricated multiple owners: {duplicateShellResult}"

  -- lean_ctor_set overwrites one pointer without releasing its old value.
  -- A unique projection of that exact slot may receive the displaced owner.
  let oldFieldReplaced : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.set ⟨0⟩ 0 (.var ⟨1⟩) (.ret (.var ⟨2⟩)))
  let replacedResult := NativeRust.emit
    (.fdecl name #[owned, { x := ⟨1⟩, borrow := false, ty := .object }]
      .object oldFieldReplaced info) "unique_field_replacement"
  unless replacedResult.startsWith "OK\n" do
    throwError "old constructor field transfer was refused: {replacedResult}"

  let duplicateFieldReplaced : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.vdecl ⟨3⟩ .object (.proj 0 ⟨0⟩)
        (.set ⟨0⟩ 0 (.var ⟨1⟩) (.ret (.var ⟨3⟩))))
  let duplicateReplacedResult := NativeRust.emit
    (.fdecl name #[owned, { x := ⟨1⟩, borrow := false, ty := .object }]
      .object duplicateFieldReplaced info) "ambiguous_replaced_field"
  unless duplicateReplacedResult.startsWith "ERROR\n" &&
      (duplicateReplacedResult.splitOn "protecting parent release").length > 1 do
    throwError "overwritten field with duplicate projections created ownership: {duplicateReplacedResult}"


  -- A unique object's owned join formal is an alias of the SAME source
  -- allocation. Two consecutive writes can permute the old field owners
  -- without manufacturing a reference; the final slot map must be bijective.
  let swapJoin : Lean.IR.Param :=
    { x := ⟨4⟩, ty := .object, borrow := false }
  let swapFields : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.vdecl ⟨3⟩ .object (.proj 1 ⟨0⟩)
        (.jdecl ⟨9⟩ #[swapJoin]
          (.set ⟨4⟩ 1 (.var ⟨2⟩)
            (.set ⟨4⟩ 0 (.var ⟨3⟩) (.ret (.var ⟨4⟩))))
          (.jmp ⟨9⟩ #[.var ⟨0⟩])))
  let swapResult := NativeRust.emit
    (.fdecl name #[owned] .object swapFields info) "unique_constructor_swap"
  unless swapResult.startsWith "OK\n" do
    throwError "unique source slot permutation was refused: {swapResult}"

  let incompleteSwap : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.jdecl ⟨9⟩ #[swapJoin]
        (.set ⟨4⟩ 1 (.var ⟨2⟩) (.ret (.var ⟨4⟩)))
        (.jmp ⟨9⟩ #[.var ⟨0⟩]))
  let incompleteResult := NativeRust.emit
    (.fdecl name #[owned] .object incompleteSwap info) "incomplete_field_permutation"
  unless incompleteResult.startsWith "ERROR\n" &&
      (incompleteResult.splitOn "incomplete or duplicate field-owner permutation").length > 1 do
    throwError "unbalanced source field permutation was admitted: {incompleteResult}"

  let duplicateSwap : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.jdecl ⟨9⟩ #[swapJoin]
        (.set ⟨4⟩ 1 (.var ⟨2⟩)
          (.set ⟨4⟩ 0 (.var ⟨2⟩) (.ret (.var ⟨4⟩))))
        (.jmp ⟨9⟩ #[.var ⟨0⟩]))
  let duplicateSwapResult := NativeRust.emit
    (.fdecl name #[owned] .object duplicateSwap info) "duplicate_field_permutation"
  unless duplicateSwapResult.startsWith "ERROR\n" &&
      (duplicateSwapResult.splitOn "incomplete or duplicate field-owner permutation").length > 1 do
    throwError "duplicated field source reference was admitted: {duplicateSwapResult}"


  -- A source dec carries a multiplicity. An internal Rc alias must not
  -- hide a final release when that multiplicity exceeds one.
  let countedRelease : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.inc ⟨0⟩ 1 true false
        (.dec ⟨0⟩ 2 true false
          (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩)))))
  let countedReleaseResult := NativeRust.emit
    (.fdecl name #[owned] .object countedRelease info) "counted_final_parent_release"
  unless countedReleaseResult.startsWith "ERROR\n" &&
      (countedReleaseResult.splitOn "protecting parent release").length > 1 do
    throwError "dec by two failed to invalidate projected child: {countedReleaseResult}"

  -- Two supported unit decrements against three real source credits
  -- leave the parent live until the child receives its independent inc.
  let countedRetained : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
      (.inc ⟨0⟩ 2 true false
        (.dec ⟨0⟩ 1 true false
          (.dec ⟨0⟩ 1 true false
            (.inc ⟨2⟩ 1 true false
              (.dec ⟨0⟩ 1 true false (.ret (.var ⟨2⟩)))))))
  let countedRetainedResult := NativeRust.emit
    (.fdecl name #[owned] .object countedRetained info) "unit_decrements_leave_parent_live"
  unless countedRetainedResult.startsWith "OK\n" do
    throwError "unit source decrements incorrectly destroyed a live parent: {countedRetainedResult}"

  -- A nonpersistent source dec of more than one remains explicitly
  -- unsupported by the pinned canonical code generator and runtime.
  let unsupportedNonUnitDec : Lean.IR.FnBody :=
    .inc ⟨0⟩ 1 true false
      (.dec ⟨0⟩ 2 true false
        (.vdecl ⟨2⟩ .uint8 (.lit (.num 1)) (.ret (.var ⟨2⟩))))
  let unsupportedNonUnitResult := NativeRust.emit
    (.fdecl name #[owned] .uint8 unsupportedNonUnitDec info) "nonunit_dec_refusal"
  unless unsupportedNonUnitResult.startsWith "ERROR\n" &&
      (unsupportedNonUnitResult.splitOn "source reference-count delta unsupported").length > 1 do
    throwError "source non-unit dec was silently emitted: {unsupportedNonUnitResult}"

  let excessiveDec : Lean.IR.FnBody :=
    .dec ⟨0⟩ 2 true false
      (.vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
        (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩))))
  let excessiveDecResult := NativeRust.emit
    (.fdecl name #[owned] .object excessiveDec info) "source_decrement_exceeds_credits"
  unless excessiveDecResult.startsWith "ERROR\n" &&
      (excessiveDecResult.splitOn "exceeds").length > 1 do
    throwError "unjustified source dec over-release was admitted: {excessiveDecResult}"

  -- The parent is itself a source dereference, even if no child VarId has
  -- previously been tracked. Both final dec and shell-only del kill it.
  let directRootAfterDec : Lean.IR.FnBody :=
    .dec ⟨0⟩ 1 true false
      (.vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
        (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩))))
  let directRootAfterDecResult := NativeRust.emit
    (.fdecl name #[owned] .object directRootAfterDec info) "root_projected_after_dec"
  unless directRootAfterDecResult.startsWith "ERROR\n" &&
      (directRootAfterDecResult.splitOn "protecting parent release").length > 1 do
    throwError "root projection read a source-released object: {directRootAfterDecResult}"

  let directRootAfterDel : Lean.IR.FnBody :=
    .del ⟨0⟩
      (.vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
        (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩))))
  let directRootAfterDelResult := NativeRust.emit
    (.fdecl name #[owned] .object directRootAfterDel info) "root_projected_after_del"
  unless directRootAfterDelResult.startsWith "ERROR\n" &&
      (directRootAfterDelResult.splitOn "protecting parent release").length > 1 do
    throwError "shell deletion left an invalid root readable: {directRootAfterDelResult}"

  -- The C emitter elides persistent dec operations. The admission pass
  -- must not invent a release for that source-no-op form.
  let persistentDec : Lean.IR.FnBody :=
    .dec ⟨0⟩ 2 true true
      (.vdecl ⟨2⟩ .object (.proj 0 ⟨0⟩)
        (.inc ⟨2⟩ 1 true false (.ret (.var ⟨2⟩))))
  let persistentDecResult := NativeRust.emit
    (.fdecl name #[owned] .object persistentDec info) "persistent_parent_dec_noop"
  unless persistentDecResult.startsWith "OK\n" do
    throwError "persistent source dec incorrectly invalidated its parent: {persistentDecResult}"

  let rootAfterOwnedCall : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .uint8 (.fap ownedName #[.var ⟨0⟩])
      (.vdecl ⟨3⟩ .object (.proj 0 ⟨0⟩)
        (.inc ⟨3⟩ 1 true false (.ret (.var ⟨3⟩))))
  let rootAfterOwnedCallResult := NativeRust.emitModule
    #[ownedCallee, .fdecl callerName #[owned] .object rootAfterOwnedCall info]
    callerName "root_after_owned_call"
  unless rootAfterOwnedCallResult.startsWith "ERROR\n" &&
      (rootAfterOwnedCallResult.splitOn "protecting parent release").length > 1 do
    throwError "consuming callee left source-released root readable: {rootAfterOwnedCallResult}"


  -- Exact direct identity calls return the consumed source object. The
  -- result's real owned reference protects the original VarId, whereas an
  -- unrelated result must never be guessed to be an alias.
  let identityName := `BorrowFlagFixture.returnIdentity
  let identityCallee : Lean.IR.Decl :=
    .fdecl identityName #[owned] .object (.ret (.var ⟨0⟩)) info
  let identityProtected : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.fap identityName #[.var ⟨0⟩])
      (.vdecl ⟨3⟩ .object (.proj 0 ⟨0⟩)
        (.inc ⟨3⟩ 1 true false (.ret (.var ⟨3⟩))))
  let identityProtectedResult := NativeRust.emitModule
    #[identityCallee, .fdecl callerName #[owned] .object identityProtected info]
    callerName "source_identity_return_preserves_root"
  unless identityProtectedResult.startsWith "OK\n" do
    throwError "source-exact identity return lost its protecting owner: {identityProtectedResult}"

  let identityReleased : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .object (.fap identityName #[.var ⟨0⟩])
      (.dec ⟨2⟩ 1 true false
        (.vdecl ⟨3⟩ .object (.proj 0 ⟨0⟩)
          (.inc ⟨3⟩ 1 true false (.ret (.var ⟨3⟩)))))
  let identityReleasedResult := NativeRust.emitModule
    #[identityCallee, .fdecl callerName #[owned] .object identityReleased info]
    callerName "source_identity_return_released"
  unless identityReleasedResult.startsWith "ERROR\n" &&
      (identityReleasedResult.splitOn "protecting parent release").length > 1 do
    throwError "released identity result kept the source root alive: {identityReleasedResult}"


  -- Source-native IR uses a tagged constant for Array indices. Tagged
  -- immediates have no heap refcount, even when a generic primitive's
  -- argument ownership is conservatively classified as consuming.
  let reusableTagged : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .tagged (.lit (.num 0))
      (.vdecl ⟨3⟩ .uint8 (.fap `Nat.decLt #[.var ⟨2⟩, .var ⟨2⟩])
        (.vdecl ⟨4⟩ .uint8 (.fap `Nat.decLe #[.var ⟨2⟩, .var ⟨2⟩])
          (.ret (.var ⟨4⟩))))
  let taggedAllowed := NativeRust.emit
    (.fdecl name #[] .uint8 reusableTagged info) "reused_statically_tagged_immediate"
  unless taggedAllowed.startsWith "OK\n" do
    throwError "statically tagged immediate was treated as a released heap owner: {taggedAllowed}"

  let taggedFormal : Lean.IR.Param :=
    { x := ⟨0⟩, ty := .tagged, borrow := false }
  let reusableTaggedFormal : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .uint8 (.fap `Nat.decLt #[.var ⟨0⟩, .var ⟨0⟩])
      (.vdecl ⟨3⟩ .uint8 (.fap `Nat.decLe #[.var ⟨0⟩, .var ⟨0⟩])
        (.ret (.var ⟨3⟩)))
  let taggedFormalAllowed := NativeRust.emit
    (.fdecl name #[taggedFormal] .uint8 reusableTaggedFormal info)
      "reused_statically_tagged_formal"
  unless taggedFormalAllowed.startsWith "OK\n" do
    throwError "statically tagged parameter acquired a fictitious heap credit: {taggedFormalAllowed}"

  logInfo "Source lifetime regression: counted dec, over-release, direct root, identity returns, tagged immediates and persistent no-op cases passed"

  logInfo "Source constructor join transfer: verified unique two-slot swap, refused incomplete and duplicate swaps"

  logInfo "Source projected lifetimes: parent release, nested/retained children, calls, joins, shell deletion and field replacement"

  logInfo "Source borrowed provenance: nested projection, retained result, join borrowed/owned arguments passed"

  logInfo "Pinned borrowed Param: direct transfer, balanced inc, direct-call ABI, PAP and branch refusal"
  logInfo "Pinned Param.borrow ABI and source-IR sharedness refusal passed"
