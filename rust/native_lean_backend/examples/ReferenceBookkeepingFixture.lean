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

  -- Pinned native C backend skips `persistent` source RC bookkeeping.
  -- The reader must use the real FnBody packed flags, not Rust Rc guesses.
  let persistentCases : Array (String × Lean.IR.FnBody) := #[
    ("persistent-inc", .inc ⟨0⟩ 1 true true observed),
    ("persistent-dec", .dec ⟨0⟩ 1 true true observed),
    ("persistent-both",
      .inc ⟨0⟩ 1 false true (.dec ⟨1⟩ 1 false true observed))
  ]
  for (label, body) in persistentCases do
    let result := NativeRust.emit (.fdecl name #[x, y] .uint8 body info) "persistent_rc"
    unless result.startsWith "OK\n" do
      throwError "persistent source RC noop {label} unexpectedly refused: {result}"
  let mixed : Lean.IR.FnBody :=
    .inc ⟨0⟩ 1 true true (.dec ⟨1⟩ 1 true false observed)
  let mixedResult := NativeRust.emit (.fdecl name #[x, y] .uint8 mixed info) "mixed_rc"
  unless mixedResult.startsWith "ERROR\n" &&
      (mixedResult.splitOn "inc/dec/del").length > 1 do
    throwError "real RC effect following persistent noop was accepted: {mixedResult}"

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
  -- Interprocedural effects must be tracked at the actual call site.
  -- Build genuine Lean.IR.Decl objects and pass the same borrowed IR through
  -- the production multi-declaration emitter, not a parallel interpreter.
  let effectName := `ReferenceBookkeepingFixture.effect
  let callerName := `ReferenceBookkeepingFixture.caller
  let witnessName := `ReferenceBookkeepingFixture.witness
  let pureName := `ReferenceBookkeepingFixture.pure
  let closureName := `ReferenceBookkeepingFixture.closure
  let calleeEffects : Lean.IR.Decl :=
    .fdecl effectName #[x] .object
      (.inc ⟨0⟩ 1 true false (.ret (.var ⟨0⟩))) info
  let localCallObservation : Lean.IR.FnBody :=
    .vdecl ⟨5⟩ .object (.fap effectName #[.var ⟨0⟩]) observed
  let crossCall : Lean.IR.Decl :=
    .fdecl callerName #[x] .uint8 localCallObservation info
  let callRefused := NativeRust.emitModule #[calleeEffects, crossCall] callerName "cross_call"
  unless callRefused.startsWith "ERROR\n" &&
      (callRefused.splitOn "interprocedural").length > 1 do
    throwError "source RC effect in direct callee was not refused: {callRefused}"

  -- A caller's RC effect can also precede an observation *inside* a
  -- directly called callee, even when the caller has no isShared itself.
  let calleeObserver : Lean.IR.Decl :=
    .fdecl witnessName #[x] .uint8 observed info
  let observingCall : Lean.IR.FnBody :=
    .inc ⟨0⟩ 1 true false
      (.vdecl ⟨5⟩ .uint8 (.fap witnessName #[.var ⟨0⟩]) (.ret (.var ⟨5⟩)))
  let acrossEntry : Lean.IR.Decl :=
    .fdecl callerName #[x] .uint8 observingCall info
  let entryRefused := NativeRust.emitModule #[calleeObserver, acrossEntry] callerName "caller"
  unless entryRefused.startsWith "ERROR\n" &&
      (entryRefused.splitOn "interprocedural").length > 1 do
    throwError "source RC effect before observer callee was not refused: {entryRefused}"

  -- A source branch can hide a real effect in an alternative. This remains
  -- a may-analysis even when the exact branch condition is unknown.
  let branchEffect : Lean.IR.FnBody :=
    .case `Bool ⟨0⟩ .object #[.default (.inc ⟨0⟩ 1 true false (.ret (.var ⟨0⟩)))]
  let branchCallee : Lean.IR.Decl :=
    .fdecl effectName #[x] .object branchEffect info
  let branchRefused := NativeRust.emitModule #[branchCallee, crossCall] callerName "branch_caller"
  unless branchRefused.startsWith "ERROR\n" &&
      (branchRefused.splitOn "interprocedural").length > 1 do
    throwError "branch-hidden RC effect was not refused: {branchRefused}"

  -- An unknown applied closure can mutate physical counts before the
  -- following isShared, regardless of whether Rust clones a value.
  let applied : Lean.IR.FnBody :=
    .vdecl ⟨5⟩ .object (.ap ⟨1⟩ #[.var ⟨0⟩]) observed
  let appliedDecl : Lean.IR.Decl :=
    .fdecl callerName #[x, y] .uint8 applied info
  let apRefused := NativeRust.emitModule #[appliedDecl] callerName "closure_apply"
  unless apRefused.startsWith "ERROR\n" &&
      (apRefused.splitOn "interprocedural").length > 1 do
    throwError "indirect closure AP before isShared was accepted: {apRefused}"

  -- Capturing an observing function in a PAP crosses the unsupported
  -- closure ownership boundary, even though the closure body is deferred.
  let capturing : Lean.IR.FnBody :=
    .vdecl ⟨5⟩ .object (.pap witnessName #[.var ⟨0⟩]) (.ret (.var ⟨0⟩))
  let captureDecl : Lean.IR.Decl :=
    .fdecl closureName #[x] .object capturing info
  let captureRefused := NativeRust.emitModule #[calleeObserver, captureDecl] closureName "capture"
  unless captureRefused.startsWith "ERROR\n" &&
      (captureRefused.splitOn "closure capture").length > 1 do
    throwError "observer closure capture was not refused: {captureRefused}"

  -- A pure direct callee has no RC effect; preserve this supported path.
  let pureCallee : Lean.IR.Decl :=
    .fdecl pureName #[x] .object (.ret (.var ⟨0⟩)) info
  let pureCaller : Lean.IR.Decl :=
    .fdecl callerName #[x] .uint8
      (.vdecl ⟨5⟩ .object (.fap pureName #[.var ⟨0⟩]) observed) info
  let pureAccepted := NativeRust.emitModule #[pureCallee, pureCaller] callerName "pure_caller"
  unless pureAccepted.startsWith "OK\n" do
    throwError "pure direct callee unexpectedly refused: {pureAccepted}"
  -- Source sequencing is directional: an observation before an effectful
  -- direct call does not see the later mutation.
  let orderedCaller : Lean.IR.Decl :=
    .fdecl callerName #[x] .uint8
      (.vdecl ⟨2⟩ .uint8 (.isShared ⟨0⟩)
        (.vdecl ⟨5⟩ .object (.fap effectName #[.var ⟨0⟩]) (.ret (.var ⟨2⟩)))) info
  let orderedAccepted := NativeRust.emitModule #[calleeEffects, orderedCaller] callerName "ordered"
  unless orderedAccepted.startsWith "OK\n" do
    throwError "observation before effectful direct call unexpectedly refused: {orderedAccepted}"

  logInfo "Source ownership boundary: 5 cross-call/branch/closure refusals, 2 ordered or pure admissions"
  logInfo "Source RC effect observations: 7 refusals, 7 bounded positive emissions"
