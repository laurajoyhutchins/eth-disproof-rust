import NativeRust
open Lean Elab Command

namespace ReferenceBookkeepingFixture
  @[noinline] def baseline (x : Nat) : Nat := x
end ReferenceBookkeepingFixture

-- Every case below uses source-native Lean.IR.FnBody constructors and the
-- production in-process emitter. No shadow interpreter or synthetic JSON.
run_cmd do
  let decl? ← liftCoreM do
    if (← Lean.IR.findDecl `ReferenceBookkeepingFixture.baseline).isNone then
      Lean.Compiler.compile #[`ReferenceBookkeepingFixture.baseline]
    Lean.IR.findDecl `ReferenceBookkeepingFixture.baseline
  let some (.fdecl name _ _ _ info) := decl?
    | throwError "missing original Lean declaration for source RC probe"
  let x : Lean.IR.Param := { x := ⟨0⟩, borrow := false, ty := .object }
  let y : Lean.IR.Param := { x := ⟨1⟩, borrow := false, ty := .object }
  let observed : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .uint8 (.isShared ⟨0⟩) (.ret (.var ⟨2⟩))
  let observedOther : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .uint8 (.isShared ⟨1⟩) (.ret (.var ⟨2⟩))
  let direct : Array (String × Lean.IR.FnBody) := #[
    ("inc", .inc ⟨0⟩ 1 true false observed),
    ("dec", .dec ⟨0⟩ 1 true false observed),
    ("del", .del ⟨0⟩ observed),
    ("alias-uncertain", .inc ⟨0⟩ 1 true false observedOther),
    ("inc-dec", .inc ⟨0⟩ 1 true false (.dec ⟨0⟩ 1 true false observed))
  ]
  for (label, body) in direct do
    let declaration : Lean.IR.Decl := .fdecl name #[x, y] .uint8 body info
    let result := NativeRust.emit declaration "rc_observation_probe"
    unless result.startsWith "ERROR\n" &&
        (result.splitOn "inc/dec/del").length > 1 do
      throwError "unsafe RC observation {label} was not refused: {result}"

  -- Aliasing can cross join boundaries; do not look only at the top-level
  -- linear continuation when deciding whether isShared is safe.
  let joinBody : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[] observed
      (.inc ⟨0⟩ 1 true false (.jmp ⟨9⟩ #[]))
  let joined := NativeRust.emit (.fdecl name #[x] .uint8 joinBody info) "rc_join_probe"
  unless joined.startsWith "ERROR\n" &&
      (joined.splitOn "inc/dec/del").length > 1 do
    throwError "join-scoped RC observation was not refused: {joined}"

  -- Reference bookkeeping without an RC observation remains in the
  -- bounded value-semantic subset. This checks emission, not a physical
  -- reference-count trace or an executable ownership correspondence.
  let unobserved : Lean.IR.FnBody :=
    .inc ⟨0⟩ 1 true false
      (.dec ⟨0⟩ 1 true false (.ret (.var ⟨0⟩)))
  let allowed := NativeRust.emit (.fdecl name #[x] .object unobserved info) "rc_value_only"
  unless allowed.startsWith "OK\n" do
    throwError "unobserved RC bookkeeping unexpectedly refused: {allowed}"
  unless (allowed.splitOn "source_inc(1, true, false)").length > 1 &&
      (allowed.splitOn "source_dec(1, true, false)").length > 1 do
    throwError "pinned source RC flag layout was not emitted faithfully: {allowed}"

  let persistentBody : Lean.IR.FnBody :=
    .inc ⟨0⟩ 5 false true (.ret (.var ⟨0⟩))
  let persistentOutput :=
    NativeRust.emit (.fdecl name #[x] .object persistentBody info) "rc_persistent"
  unless persistentOutput.startsWith "OK\n" &&
      (persistentOutput.splitOn "source_inc(5, false, true)").length > 1 do
    throwError "pinned persistent source RC flags were misread: {persistentOutput}"

  let delOnly : Lean.IR.FnBody :=
    .del ⟨0⟩ (.vdecl ⟨2⟩ .uint8 (.lit (.num 0)) (.ret (.var ⟨2⟩)))
  let deleteOutput :=
    NativeRust.emit (.fdecl name #[x] .uint8 delOnly info) "rc_del"
  unless deleteOutput.startsWith "OK\n" &&
      (deleteOutput.splitOn "source_del()").length > 1 do
    throwError "source del shell-only operation missing: {deleteOutput}"

  let pure := NativeRust.emit (.fdecl name #[x] .uint8 observed info) "rc_no_bookkeeping"
  unless pure.startsWith "OK\n" do
    throwError "bare isShared observation unexpectedly refused: {pure}"
  -- Optimized Lean constructors check isShared before incrementing fields.
  -- Later bookkeeping cannot change the already-computed Boolean value.
  let checkFirst : Lean.IR.FnBody :=
    .vdecl ⟨2⟩ .uint8 (.isShared ⟨0⟩)
      (.inc ⟨0⟩ 1 true false (.ret (.var ⟨2⟩)))
  let ordered := NativeRust.emit (.fdecl name #[x] .uint8 checkFirst info) "rc_check_before_inc"
  unless ordered.startsWith "OK\n" do
    throwError "pre-mutation source sharing check unexpectedly refused: {ordered}"
  -- The join body executes only at jmp. A sharing check in the
  -- continuation is not tainted by an RC effect later in that join.
  let joinReturn : Lean.IR.FnBody :=
    .vdecl ⟨3⟩ .uint8 (.lit (.num 0)) (.ret (.var ⟨3⟩))
  let orderedJoin : Lean.IR.FnBody :=
    .jdecl ⟨9⟩ #[] (.inc ⟨0⟩ 1 true false joinReturn)
      (.vdecl ⟨2⟩ .uint8 (.isShared ⟨0⟩) (.jmp ⟨9⟩ #[]))
  let acceptedJoin :=
    NativeRust.emit (.fdecl name #[x] .uint8 orderedJoin info) "rc_join_after_observation"
  unless acceptedJoin.startsWith "OK\n" do
    throwError "ordered join RC after sharing check unexpectedly refused: {acceptedJoin}"
  logInfo "Source RC effect observations: 6 refusals, 4 bounded positive emissions"
