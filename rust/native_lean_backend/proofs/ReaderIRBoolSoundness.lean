import ReaderIRSoundness

/-!
# Branch-bearing original Lean IR to modeled Rust semantics

This file extends the proof-carrying original IR scanner to UInt64 comparisons
and two-constructor Bool branching. Both alternatives are checked from their
*actual* IR Alt nodes; a branch receives a fresh, immutable incoming binding
environment, so one alternative cannot leak a definition into another.

The big-step semantics uses original Lean IR nodes and genuine UInt64 operators,
not any Rust source string. ReaderScalarCertificate independently checks the
complete Rust text emitted by the real Reader FFI. Neither component assumes
rustc semantics or source-side reference-count effects.
-/

open Lean
open NativeRustScalarRefinement
open ReaderIRSoundness

namespace ReaderIRBoolSoundness

abbrev SymTests := Nat → Option Condition
abbrev SourceTests := Nat → Option Bool

/-- Source comparison evaluation, distinct from the modeled Condition evaluator. -/
inductive TestRuns (words : SourceEnv) : IR.Expr → Bool → Prop where
  | eq (args : Array IR.Arg) (a b : IR.VarId) (u v : UInt64)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : words a.idx = some u)
      (hv : words b.idx = some v) :
      TestRuns words (.fap `UInt64.decEq args) (decide (u = v))
  | lt (args : Array IR.Arg) (a b : IR.VarId) (u v : UInt64)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : words a.idx = some u)
      (hv : words b.idx = some v) :
      TestRuns words (.fap `UInt64.decLt args) (decide (u < v))
  | le (args : Array IR.Arg) (a b : IR.VarId) (u v : UInt64)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : words a.idx = some u)
      (hv : words b.idx = some v) :
      TestRuns words (.fap `UInt64.decLe args) (decide (u ≤ v))

/-- Reified comparisons are witnessed against exact original primitive names,
operand positions and variable identities. -/
inductive TestMatches (sym : SymbolicEnv) : IR.Expr → Condition → Prop where
  | eq (args : Array IR.Arg) (a b : IR.VarId) (u v : WordExpr)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : sym a.idx = some u)
      (hv : sym b.idx = some v) :
      TestMatches sym (.fap `UInt64.decEq args) (.eq u v)
  | lt (args : Array IR.Arg) (a b : IR.VarId) (u v : WordExpr)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : sym a.idx = some u)
      (hv : sym b.idx = some v) :
      TestMatches sym (.fap `UInt64.decLt args) (.lt u v)
  | le (args : Array IR.Arg) (a b : IR.VarId) (u v : WordExpr)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : sym a.idx = some u)
      (hv : sym b.idx = some v) :
      TestMatches sym (.fap `UInt64.decLe args) (.le u v)

/-- Complete Bool arms have both cidx 0/1, exact constructor names and two
alternatives. Either array order is allowed, never default or repeated arms. -/
def BoolAlts (alts : Array IR.Alt) (falseBody trueBody : IR.FnBody) : Prop :=
  alts.size = 2 ∧
    ((∃ infoF infoT,
      alts[0]? = some (IR.Alt.ctor infoF falseBody) ∧
      alts[1]? = some (IR.Alt.ctor infoT trueBody) ∧
      infoF.cidx = 0 ∧ infoF.name = `Bool.false ∧
      infoT.cidx = 1 ∧ infoT.name = `Bool.true) ∨
     (∃ infoT infoF,
      alts[0]? = some (IR.Alt.ctor infoT trueBody) ∧
      alts[1]? = some (IR.Alt.ctor infoF falseBody) ∧
      infoT.cidx = 1 ∧ infoT.name = `Bool.true ∧
      infoF.cidx = 0 ∧ infoF.name = `Bool.false))

/-- Operational semantics of real compiler IR with two distinct mutable
environments: UInt64 variables and Bool-tag variables. -/
inductive BodyRuns : IR.FnBody → SourceEnv → SourceTests → UInt64 → Prop where
  | ret (words : SourceEnv) (tests : SourceTests)
      (id : IR.VarId) (value : UInt64)
      (h : words id.idx = some value) :
      BodyRuns (.ret (.var id)) words tests value
  | word (words : SourceEnv) (tests : SourceTests) (id : IR.VarId)
      (expr : IR.Expr) (tail : IR.FnBody) (value result : UInt64)
      (hExpr : ExprRuns words expr value)
      (hTail : BodyRuns tail (setVar words id.idx value) tests result) :
      BodyRuns (.vdecl id .uint64 expr tail) words tests result
  | test (words : SourceEnv) (tests : SourceTests) (id : IR.VarId)
      (expr : IR.Expr) (tail : IR.FnBody) (value : Bool) (result : UInt64)
      (hExpr : TestRuns words expr value)
      (hTail : BodyRuns tail words (setVar tests id.idx value) result) :
      BodyRuns (.vdecl id .uint8 expr tail) words tests result
  | branchTrue (words : SourceEnv) (tests : SourceTests)
      (tid : Name) (scr : IR.VarId) (ty : IR.IRType)
      (alts : Array IR.Alt) (fb tb : IR.FnBody) (result : UInt64)
      (htid : tid = `UInt8) (hty : ty = .uint8)
      (arms : BoolAlts alts fb tb)
      (h : tests scr.idx = some true)
      (run : BodyRuns tb words tests result) :
      BodyRuns (.case tid scr ty alts) words tests result
  | branchFalse (words : SourceEnv) (tests : SourceTests)
      (tid : Name) (scr : IR.VarId) (ty : IR.IRType)
      (alts : Array IR.Alt) (fb tb : IR.FnBody) (result : UInt64)
      (htid : tid = `UInt8) (hty : ty = .uint8)
      (arms : BoolAlts alts fb tb)
      (h : tests scr.idx = some false)
      (run : BodyRuns fb words tests result) :
      BodyRuns (.case tid scr ty alts) words tests result

/-- Proof-carrying reification from original IR syntax to the exact source
Program whose modeled Rust target already has an all-inputs theorem. -/
inductive BodyMatches : SymbolicEnv → SymTests → IR.FnBody → Program → Prop where
  | ret (sw : SymbolicEnv) (st : SymTests) (id : IR.VarId)
      (value : WordExpr) (h : sw id.idx = some value) :
      BodyMatches sw st (.ret (.var id)) (.ret value)
  | word (sw : SymbolicEnv) (st : SymTests) (id : IR.VarId)
      (expr : IR.Expr) (tail : IR.FnBody) (value : WordExpr)
      (p : Program) (hExpr : ExprMatches sw expr value)
      (hTail : BodyMatches (setVar sw id.idx value) st tail p) :
      BodyMatches sw st (.vdecl id .uint64 expr tail) p
  | test (sw : SymbolicEnv) (st : SymTests) (id : IR.VarId)
      (expr : IR.Expr) (tail : IR.FnBody) (value : Condition)
      (p : Program) (hExpr : TestMatches sw expr value)
      (hTail : BodyMatches sw (setVar st id.idx value) tail p) :
      BodyMatches sw st (.vdecl id .uint8 expr tail) p
  | branch (sw : SymbolicEnv) (st : SymTests)
      (tid : Name) (scr : IR.VarId) (ty : IR.IRType)
      (alts : Array IR.Alt) (fb tb : IR.FnBody)
      (cond : Condition) (tp fp : Program)
      (htid : tid = `UInt8) (hty : ty = .uint8)
      (arms : BoolAlts alts fb tb)
      (hTest : st scr.idx = some cond)
      (hTrue : BodyMatches sw st tb tp)
      (hFalse : BodyMatches sw st fb fp) :
      BodyMatches sw st (.case tid scr ty alts) (.branch cond tp fp)

structure EnvAgrees (sw : SymbolicEnv) (st : SymTests)
    (words : SourceEnv) (tests : SourceTests)
    (inputs : Nat → UInt64) : Prop where
  word : ReaderIRSoundness.EnvAgrees sw words inputs
  test : ∀ i cond, st i = some cond →
      tests i = some (evalActualCondition inputs cond)

theorem set_word_agrees {sw : SymbolicEnv} {st : SymTests}
    {words : SourceEnv} {tests : SourceTests} {inputs : Nat → UInt64}
    (h : EnvAgrees sw st words tests inputs) (id : Nat) (value : WordExpr) :
    EnvAgrees (setVar sw id value) st
      (setVar words id (evalActualUInt64 inputs value)) tests inputs := by
  exact ⟨ReaderIRSoundness.set_agrees h.word id value, h.test⟩

theorem set_test_agrees {sw : SymbolicEnv} {st : SymTests}
    {words : SourceEnv} {tests : SourceTests} {inputs : Nat → UInt64}
    (h : EnvAgrees sw st words tests inputs) (id : Nat) (value : Condition) :
    EnvAgrees sw (setVar st id value)
      words (setVar tests id (evalActualCondition inputs value)) inputs := by
  refine ⟨h.word, ?_⟩
  intro i cond hi
  by_cases hid : i = id
  · subst i
    simp only [setVar, ↓reduceIte] at hi ⊢
    cases hi
    rfl
  · have old : st i = some cond := by
      simpa only [setVar, if_neg hid] using hi
    simpa only [setVar, if_neg hid] using h.test i cond old

theorem test_sound {sw : SymbolicEnv} {expr : IR.Expr}
    {cond : Condition} (h : TestMatches sw expr cond)
    (inputs : Nat → UInt64) (words : SourceEnv)
    (agree : ReaderIRSoundness.EnvAgrees sw words inputs) :
    TestRuns words expr (evalActualCondition inputs cond) := by
  cases h with
  | eq args a b u v hs ha hb hu hv =>
      exact TestRuns.eq args a b _ _ hs ha hb
        (agree a.idx u hu) (agree b.idx v hv)
  | lt args a b u v hs ha hb hu hv =>
      exact TestRuns.lt args a b _ _ hs ha hb
        (agree a.idx u hu) (agree b.idx v hv)
  | le args a b u v hs ha hb hu hv =>
      exact TestRuns.le args a b _ _ hs ha hb
        (agree a.idx u hu) (agree b.idx v hv)

/-- The source-side all-input theorem, including nested Bool branches and
branch-local variable environments. -/
theorem body_sound {sw : SymbolicEnv} {st : SymTests}
    {body : IR.FnBody} {p : Program} (h : BodyMatches sw st body p) :
    ∀ (inputs : Nat → UInt64) (words : SourceEnv) (tests : SourceTests),
      EnvAgrees sw st words tests inputs →
      BodyRuns body words tests (evalActualProgram inputs p) := by
  induction h with
  | ret sw st id value hv =>
      intro inputs words tests agree
      exact BodyRuns.ret words tests id _ (agree.word id.idx value hv)
  | word sw st id expr tail value p he ht ih =>
      intro inputs words tests agree
      exact BodyRuns.word words tests id expr tail _ _
        (ReaderIRSoundness.expr_sound he inputs words agree.word)
        (ih inputs (setVar words id.idx (evalActualUInt64 inputs value))
          tests (set_word_agrees agree id.idx value))
  | test sw st id expr tail value p he ht ih =>
      intro inputs words tests agree
      exact BodyRuns.test words tests id expr tail _ _
        (test_sound he inputs words agree.word)
        (ih inputs words
          (setVar tests id.idx (evalActualCondition inputs value))
          (set_test_agrees agree id.idx value))
  | branch sw st tid scr ty alts fb tb cond tp fp htid hty arms htest ht hf iht ihf =>
      intro inputs words tests agree
      cases hcond : evalActualCondition inputs cond with
      | true =>
          simp only [evalActualProgram, hcond]
          exact BodyRuns.branchTrue words tests tid scr ty alts fb tb _
            htid hty arms (by simpa only [hcond] using agree.test scr.idx cond htest)
            (iht inputs words tests agree)
      | false =>
          simp only [evalActualProgram, hcond]
          exact BodyRuns.branchFalse words tests tid scr ty alts fb tb _
            htid hty arms (by simpa only [hcond] using agree.test scr.idx cond htest)
            (ihf inputs words tests agree)

structure TestWitness (sym : SymbolicEnv) (expr : IR.Expr) where
  condition : Condition
  derivation : TestMatches sym expr condition

/-- A condition witness can never be produced for an arbitrary function name,
a wrong arity, or an argument outside the current word environment. -/
private def testExpr (sym : SymbolicEnv) (expr : IR.Expr) :
    Option (TestWitness sym expr) :=
  match expr with
  | .fap name args =>
    if hs : args.size = 2 then
      match ha : args[0]? with
      | some (IR.Arg.var a) =>
        match hb : args[1]? with
        | some (IR.Arg.var b) =>
          match hu : sym a.idx with
          | some u =>
            match hv : sym b.idx with
            | some v =>
              if hn : name = `UInt64.decEq then
                some (TestWitness.mk (.eq u v) (by
                  simpa only [hn] using
                    (TestMatches.eq args a b u v hs ha hb hu hv)))
              else if hn : name = `UInt64.decLt then
                some (TestWitness.mk (.lt u v) (by
                  simpa only [hn] using
                    (TestMatches.lt args a b u v hs ha hb hu hv)))
              else if hn : name = `UInt64.decLe then
                some (TestWitness.mk (.le u v) (by
                  simpa only [hn] using
                    (TestMatches.le args a b u v hs ha hb hu hv)))
              else none
            | none => none
          | none => none
        | _ => none
      | _ => none
    else none
  | _ => none

structure ArmWitness (alts : Array IR.Alt) where
  falseBody : IR.FnBody
  trueBody : IR.FnBody
  armsProof : BoolAlts alts falseBody trueBody

private def reifyAlts (alts : Array IR.Alt) : Option (ArmWitness alts) :=
  if hs : alts.size = 2 then
    match h0 : alts[0]? with
    | some (IR.Alt.ctor info0 body0) =>
      match h1 : alts[1]? with
      | some (IR.Alt.ctor info1 body1) =>
        if hc0 : info0.cidx = 0 then
          if hn0 : info0.name = `Bool.false then
            if hc1 : info1.cidx = 1 then
              if hn1 : info1.name = `Bool.true then
                some (ArmWitness.mk body0 body1
                  ⟨hs, Or.inl ⟨info0, info1,
                    h0, h1, hc0, hn0, hc1, hn1⟩⟩)
              else none
            else none
          else none
        else if hc0 : info0.cidx = 1 then
          if hn0 : info0.name = `Bool.true then
            if hc1 : info1.cidx = 0 then
              if hn1 : info1.name = `Bool.false then
                some (ArmWitness.mk body1 body0
                  ⟨hs, Or.inr ⟨info0, info1,
                    h0, h1, hc0, hn0, hc1, hn1⟩⟩)
              else none
            else none
          else none
        else none
      | _ => none
    | _ => none
  else none

structure BodyWitness (sw : SymbolicEnv) (st : SymTests)
    (body : IR.FnBody) where
  program : Program
  bodyProof : BodyMatches sw st body program

/-- Total and fuel-bounded original-IR checker: every accepted node brings
its exact constructor witness into the kernel-checkable proof. -/
private def scan (fuel : Nat) (sw : SymbolicEnv) (st : SymTests)
    (body : IR.FnBody) : Option (BodyWitness sw st body) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match body with
    | .ret (.var id) =>
      match h : sw id.idx with
      | some value =>
        some {program := .ret value, bodyProof := .ret sw st id value h}
      | none => none
    | .vdecl id .uint64 expr tail =>
      match ReaderIRSoundness.wordExpr sw expr with
      | some {word := value, derivation := hexpr} =>
        match scan fuel (setVar sw id.idx value) st tail with
        | some {program := p, bodyProof := htail} =>
          some {program := p, bodyProof := .word sw st id expr tail value p hexpr htail}
        | none => none
      | none => none
    | .vdecl id .uint8 expr tail =>
      match testExpr sw expr with
      | some {condition := value, derivation := hexpr} =>
        match scan fuel sw (setVar st id.idx value) tail with
        | some {program := p, bodyProof := htail} =>
          some {program := p, bodyProof := .test sw st id expr tail value p hexpr htail}
        | none => none
      | none => none
    | .case tid scr .uint8 alts =>
      if htid : tid = `UInt8 then
        match hs : st scr.idx with
        | some cond =>
          match reifyAlts alts with
          | some {falseBody := fb, trueBody := tb, armsProof := harm} =>
            match scan fuel sw st tb with
            | some {program := tp, bodyProof := htp} =>
              match scan fuel sw st fb with
              | some {program := fp, bodyProof := hfp} =>
                some (BodyWitness.mk (.branch cond tp fp)
                  (.branch sw st tid scr .uint8 alts fb tb cond tp fp
                    htid rfl harm hs htp hfp))
              | none => none
            | none => none
          | none => none
        | none => none
      else none
    | _ => none

def initialTests : SymTests := fun _ => none
def initialSourceTests : SourceTests := fun _ => none

theorem initial_agrees (left right : Nat) (a b : UInt64) :
    EnvAgrees (initialSym left right) initialTests
      (initialRuntime left right a b) initialSourceTests
      (inputWords a b) := by
  refine ⟨ReaderIRSoundness.initial_agrees left right a b, ?_⟩
  intro i cond h
  cases h

structure Certificate where
  left : Nat
  right : Nat
  body : IR.FnBody
  program : Program
  sourceProof : BodyMatches (initialSym left right) initialTests body program

/-- Exactly two unborrowed UInt64 parameters and a UInt64 return, with
source-IR semantic evidence for every instruction in the accepted body. -/
def certifyDecl (decl : IR.Decl) : Option Certificate := do
  match decl with
  | .fdecl _ params .uint64 body _ =>
    if params.size != 2 then none else
    let some p0 := params[0]? | none
    let some p1 := params[1]? | none
    if p0.ty != .uint64 || p1.ty != .uint64 ||
       p0.borrow || p1.borrow || p0.x.idx == p1.x.idx then
      none
    else
      let witness ← scan 100000
        (initialSym p0.x.idx p1.x.idx) initialTests body
      some {left := p0.x.idx, right := p1.x.idx, body,
            program := witness.program, sourceProof := witness.bodyProof}
  | _ => none

/-- All input pairs: certified original Lean IR refines independent modeled
Rust target syntax, including arbitrary nested Bool branches. -/
theorem original_ir_target_refines (c : Certificate) (a b : UInt64) :
    ∃ value,
      BodyRuns c.body (initialRuntime c.left c.right a b)
        initialSourceTests value ∧
      evalRustProgramSyntax (fun i => (inputWords a b i).toNat)
        (lowerProgram c.program) = value.toNat := by
  refine ⟨evalActualProgram (inputWords a b) c.program, ?_, ?_⟩
  · exact body_sound c.sourceProof (inputWords a b)
      (initialRuntime c.left c.right a b) initialSourceTests
      (initial_agrees c.left c.right a b)
  · exact modeled_compiler_refines (inputWords a b) c.program

/-- Join actual Reader's FFI-emitted bytes (independently reified in
ReaderScalarCertificate) to the source-IR branch operational theorem. -/
structure LinkedCertificate where
  source : Certificate
  emission : ReaderScalarCertificate.Certificate
  sameProgram : source.program = emission.program

theorem linked_reader_refines (c : LinkedCertificate) (a b : UInt64) :
    ∃ value,
      BodyRuns c.source.body
        (initialRuntime c.source.left c.source.right a b)
        initialSourceTests value ∧
      evalRustProgramSyntax (fun i => (inputWords a b i).toNat)
        (lowerProgram c.emission.program) = value.toNat := by
  rw [← c.sameProgram]
  exact original_ir_target_refines c.source a b

end ReaderIRBoolSoundness

#print axioms ReaderIRBoolSoundness.body_sound
#print axioms ReaderIRBoolSoundness.linked_reader_refines

open Lean Elab Command

run_cmd do
  for root in #[`ScalarFixture.plus, `ScalarFixture.straightChain,
                `ScalarFixture.choose, `ScalarFixture.nested] do
    let emitted ← liftCoreM <| ReaderScalarCertificate.certify root
    let some decl ← liftCoreM <| Lean.IR.findDecl root
      | throwError "source IR not found: {root}"
    let some source := ReaderIRBoolSoundness.certifyDecl decl
      | throwError "source-IR Bool proof checker refused {root}"
    if h : source.program = emitted.program then
      let linked : ReaderIRBoolSoundness.LinkedCertificate :=
        {source, emission := emitted, sameProgram := h}
      let _ := ReaderIRBoolSoundness.linked_reader_refines linked
      logInfo m!"Original IR Bool branch semantics certified against Reader: {root}"
    else
      throwError "Bool source IR model differs from independently rendered Reader output"
  let root := `ScalarFixture.subtract
  let some decl ← liftCoreM <| Lean.IR.findDecl root
    | throwError "negative IR fixture missing"
  if (ReaderIRBoolSoundness.certifyDecl decl).isSome then
    throwError "unproved subtraction received a source IR certificate"
  logInfo "Bool branch source IR checker refused unsupported subtraction"
