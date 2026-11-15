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

  -- The pinned Lean C emitter does not execute RC increments or
  -- decrements marked persistent. They must not taint a later isShared.
  -- The packed C ABI flag decoder is exercised through real Lean.IR terms.
  let persistentCases : Array (String × Lean.IR.FnBody) := #[
    ("persistent-inc", .inc ⟨0⟩ 1 true true observed),
    ("persistent-dec", .dec ⟨0⟩ 1 true true observed),
    ("persistent-pair",
      .inc ⟨0⟩ 1 false true
        (.dec ⟨1⟩ 1 false true observed))
  ]
  for (label, body) in persistentCases do
    let declaration : Lean.IR.Decl := .fdecl name #[x, y] .uint8 body info
    let result := NativeRust.emit declaration "persistent_rc_probe"
    unless result.startsWith "OK\n" do
      throwError "Lean-C-omitted RC effect {label} unexpectedly refused: {result}"

  -- One genuine RC effect still matters even when adjacent operations are
  -- statically persistent. Source-CFG order cannot be erased by a noop.
  let mixed : Lean.IR.FnBody :=
    .inc ⟨0⟩ 1 true true
      (.dec ⟨1⟩ 1 true false observed)
  let mixedResult := NativeRust.emit (.fdecl name #[x, y] .uint8 mixed info) "mixed_rc_probe"
  unless mixedResult.startsWith "ERROR\n" &&
      (mixedResult.splitOn "inc/dec/del").length > 1 do
    throwError "real RC effect after persistent noop was accepted: {mixedResult}"

  -- Reference bookkeeping without an RC observation remains in the
  -- bounded value-semantic subset. This checks emission, not a physical
  -- reference-count trace or an executable ownership correspondence.
  let unobserved : Lean.IR.FnBody :=
    .inc ⟨0⟩ 1 true false
      (.dec ⟨0⟩ 1 true false (.ret (.var ⟨0⟩)))
  let allowed := NativeRust.emit (.fdecl name #[x] .object unobserved info) "rc_value_only"
  unless allowed.startsWith "OK\n" do
    throwError "unobserved RC bookkeeping unexpectedly refused: {allowed}"
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
  logInfo "Source RC effect observations: 7 refusals, 7 bounded positive emissions"
