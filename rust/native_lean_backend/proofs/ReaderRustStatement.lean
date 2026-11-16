import ReaderIRABIObservation

/-!
# Canonical emitted Rust statements: an independently executable semantics

The previous target theorem covered a pure expression/branch tree. Reader
emits an imperative Rust body: typed let bindings, wrapping arithmetic,
u8::from comparisons, match on the 0/1 tag, and return of a named variable.

We model those statements and their lexical environments explicitly.
A proof-producing verifier checks the independently decoded statement body
against the already proved source program. The exact canonical pretty-print
of this *statement* body must equal the bytes returned by the actual Reader
FFI. No unsupported Rust token can be silently certified.

The semantics here are for a restricted Rust-shaped statement grammar.
The real rustc execution parity is separately checked by compiling exactly
the certified Reader output and comparing it to Lean source oracles, in debug
and optimized modes. This is NOT a formal theorem about arbitrary rustc/MIR.
-/

open Lean
open NativeRustScalarRefinement
open ReaderIRSoundness

namespace ReaderRustStatement

/-- The exact RHS forms admitted by the certified production Rust emitter. -/
inductive WordOp where
  | constant : Nat → WordOp
  | wrappingAdd : Nat → Nat → WordOp
  | wrappingMul : Nat → Nat → WordOp
  deriving Repr, DecidableEq

inductive TestOp where
  | eq : Nat → Nat → TestOp
  | lt : Nat → Nat → TestOp
  | le : Nat → Nat → TestOp
  deriving Repr, DecidableEq

/-- Rust syntax with named registers, typed let statements and a two-arm
match. The Boolean flag preserves original constructor array order for the
text representation; runtime branch selection is by tag, not arm order. -/
inductive Stmt where
  | ret : Nat → Stmt
  | letWord : Nat → WordOp → Stmt → Stmt
  | letTest : Nat → TestOp → Stmt → Stmt
  | switch : Nat → Stmt → Stmt → Bool → Stmt
  deriving Repr, DecidableEq

abbrev WordStore := Nat → Option Nat
abbrev TestStore := Nat → Option Nat

/-- Independent big-step execution of the restricted imperative Rust
operations. Arithmetic wraps at 2^64; comparisons materialize actual 0/1
u8 tags; a match cannot execute on an invalid tag. -/
inductive WordRuns (words : WordStore) : WordOp → Nat → Prop where
  | constant (n : Nat) :
      WordRuns words (.constant n) (n % modulus)
  | add (a b u v : Nat)
      (ha : words a = some u) (hb : words b = some v) :
      WordRuns words (.wrappingAdd a b) ((u + v) % modulus)
  | mul (a b u v : Nat)
      (ha : words a = some u) (hb : words b = some v) :
      WordRuns words (.wrappingMul a b) ((u * v) % modulus)

inductive TestRuns (words : WordStore) : TestOp → Nat → Prop where
  | eq (a b u v : Nat)
      (ha : words a = some u) (hb : words b = some v) :
      TestRuns words (.eq a b) (rustBoolTag (decide (u = v)))
  | lt (a b u v : Nat)
      (ha : words a = some u) (hb : words b = some v) :
      TestRuns words (.lt a b) (rustBoolTag (decide (u < v)))
  | le (a b u v : Nat)
      (ha : words a = some u) (hb : words b = some v) :
      TestRuns words (.le a b) (rustBoolTag (decide (u ≤ v)))

inductive Runs : Stmt → WordStore → TestStore → Nat → Prop where
  | ret (words : WordStore) (tests : TestStore) (id value : Nat)
      (h : words id = some value) :
      Runs (.ret id) words tests value
  | letWord (words : WordStore) (tests : TestStore)
      (id : Nat) (rhs : WordOp) (tail : Stmt) (value result : Nat)
      (rhsRun : WordRuns words rhs value)
      (tailRun : Runs tail (setVar words id value) tests result) :
      Runs (.letWord id rhs tail) words tests result
  | letTest (words : WordStore) (tests : TestStore)
      (id : Nat) (rhs : TestOp) (tail : Stmt) (value result : Nat)
      (rhsRun : TestRuns words rhs value)
      (tailRun : Runs tail words (setVar tests id value) result) :
      Runs (.letTest id rhs tail) words tests result
  | trueArm (words : WordStore) (tests : TestStore)
      (id : Nat) (f t : Stmt) (reversed : Bool) (result : Nat)
      (tag : tests id = some 1) (branch : Runs t words tests result) :
      Runs (.switch id f t reversed) words tests result
  | falseArm (words : WordStore) (tests : TestStore)
      (id : Nat) (f t : Stmt) (reversed : Bool) (result : Nat)
      (tag : tests id = some 0) (branch : Runs f words tests result) :
      Runs (.switch id f t reversed) words tests result

/-- A proof relation from imperative target operations to the existing
source's symbolic expressions, preserving named register dependencies. -/
inductive WordMatches (sw : SymbolicEnv) : WordOp → WordExpr → Prop where
  | constant (n : Nat) :
      WordMatches sw (.constant n) (.lit n)
  | add (a b : Nat) (u v : WordExpr)
      (hu : sw a = some u) (hv : sw b = some v) :
      WordMatches sw (.wrappingAdd a b) (.add u v)
  | mul (a b : Nat) (u v : WordExpr)
      (hu : sw a = some u) (hv : sw b = some v) :
      WordMatches sw (.wrappingMul a b) (.mul u v)

inductive TestMatches (sw : SymbolicEnv) : TestOp → Condition → Prop where
  | eq (a b : Nat) (u v : WordExpr)
      (hu : sw a = some u) (hv : sw b = some v) :
      TestMatches sw (.eq a b) (.eq u v)
  | lt (a b : Nat) (u v : WordExpr)
      (hu : sw a = some u) (hv : sw b = some v) :
      TestMatches sw (.lt a b) (.lt u v)
  | le (a b : Nat) (u v : WordExpr)
      (hu : sw a = some u) (hv : sw b = some v) :
      TestMatches sw (.le a b) (.le u v)

abbrev SymTests := Nat → Option Condition

inductive StmtMatches : SymbolicEnv → SymTests → Stmt → Program → Prop where
  | ret (sw : SymbolicEnv) (st : SymTests)
      (id : Nat) (value : WordExpr) (h : sw id = some value) :
      StmtMatches sw st (.ret id) (.ret value)
  | letWord (sw : SymbolicEnv) (st : SymTests)
      (id : Nat) (rhs : WordOp) (tail : Stmt)
      (value : WordExpr) (p : Program)
      (hr : WordMatches sw rhs value)
      (ht : StmtMatches (setVar sw id value) st tail p) :
      StmtMatches sw st (.letWord id rhs tail) p
  | letTest (sw : SymbolicEnv) (st : SymTests)
      (id : Nat) (rhs : TestOp) (tail : Stmt)
      (value : Condition) (p : Program)
      (hr : TestMatches sw rhs value)
      (ht : StmtMatches sw (setVar st id value) tail p) :
      StmtMatches sw st (.letTest id rhs tail) p
  | switch (sw : SymbolicEnv) (st : SymTests)
      (id : Nat) (f t : Stmt) (reversed : Bool)
      (c : Condition) (tp fp : Program)
      (hc : st id = some c)
      (ht : StmtMatches sw st t tp)
      (hf : StmtMatches sw st f fp) :
      StmtMatches sw st (.switch id f t reversed) (.branch c tp fp)

/-- Extensional agreement of registers with their symbolic source values. -/
structure EnvAgrees (sw : SymbolicEnv) (st : SymTests)
    (words : WordStore) (tests : TestStore)
    (inputs : Nat → Nat) : Prop where
  word : ∀ i e, sw i = some e → words i = some (evalRustWord inputs e)
  test : ∀ i c, st i = some c →
    tests i = some (rustBoolTag (evalRustCondition inputs c))

theorem add_word_agrees {sw : SymbolicEnv} {st : SymTests}
    {words : WordStore} {tests : TestStore} {inputs : Nat → Nat}
    (h : EnvAgrees sw st words tests inputs) (id : Nat) (e : WordExpr) :
    EnvAgrees (setVar sw id e) st
      (setVar words id (evalRustWord inputs e)) tests inputs := by
  refine ⟨?_, h.test⟩
  intro i v hv
  by_cases hid : i = id
  · subst i
    simp only [setVar, ↓reduceIte] at hv ⊢
    cases hv
    rfl
  · have prev : sw i = some v := by
      simpa only [setVar, if_neg hid] using hv
    simpa only [setVar, if_neg hid] using h.word i v prev

theorem add_test_agrees {sw : SymbolicEnv} {st : SymTests}
    {words : WordStore} {tests : TestStore} {inputs : Nat → Nat}
    (h : EnvAgrees sw st words tests inputs) (id : Nat) (c : Condition) :
    EnvAgrees sw (setVar st id c)
      words (setVar tests id (rustBoolTag (evalRustCondition inputs c))) inputs := by
  refine ⟨h.word, ?_⟩
  intro i d hd
  by_cases hid : i = id
  · subst i
    simp only [setVar, ↓reduceIte] at hd ⊢
    cases hd
    rfl
  · have prev : st i = some d := by
      simpa only [setVar, if_neg hid] using hd
    simpa only [setVar, if_neg hid] using h.test i d prev

theorem word_sound {sw : SymbolicEnv} {rhs : WordOp} {e : WordExpr}
    (h : WordMatches sw rhs e) (inputs : Nat → Nat)
    (words : WordStore)
    (agree : ∀ i e, sw i = some e →
      words i = some (evalRustWord inputs e)) :
    WordRuns words rhs (evalRustWord inputs e) := by
  cases h with
  | constant n =>
      exact WordRuns.constant n
  | add a b u v hu hv =>
      exact WordRuns.add a b _ _
        (agree a u hu) (agree b v hv)
  | mul a b u v hu hv =>
      exact WordRuns.mul a b _ _
        (agree a u hu) (agree b v hv)

theorem test_sound {sw : SymbolicEnv} {rhs : TestOp} {c : Condition}
    (h : TestMatches sw rhs c) (inputs : Nat → Nat)
    (words : WordStore)
    (agree : ∀ i e, sw i = some e →
      words i = some (evalRustWord inputs e)) :
    TestRuns words rhs (rustBoolTag (evalRustCondition inputs c)) := by
  cases h with
  | eq a b u v hu hv =>
      exact TestRuns.eq a b _ _ (agree a u hu) (agree b v hv)
  | lt a b u v hu hv =>
      exact TestRuns.lt a b _ _ (agree a u hu) (agree b v hv)
  | le a b u v hu hv =>
      exact TestRuns.le a b _ _ (agree a u hu) (agree b v hv)

/-- For every symbolic target program, every input, and every agreeing
concrete register environment, the imperative Rust-statement rules execute
to the value of the already proved functional Rust target semantics. -/
theorem statement_sound {sw : SymbolicEnv} {st : SymTests}
    {body : Stmt} {p : Program} (h : StmtMatches sw st body p) :
    ∀ (inputs : Nat → Nat) (words : WordStore) (tests : TestStore),
      EnvAgrees sw st words tests inputs →
        Runs body words tests (evalRustProgram inputs p) := by
  induction h with
  | ret sw st id e hv =>
      intro inputs words tests agree
      exact Runs.ret words tests id _ (agree.word id e hv)
  | letWord sw st id rhs tail value p hr ht ih =>
      intro inputs words tests agree
      exact Runs.letWord words tests id rhs tail _ _
        (word_sound hr inputs words agree.word)
        (ih inputs (setVar words id (evalRustWord inputs value)) tests
          (add_word_agrees agree id value))
  | letTest sw st id rhs tail value p hr ht ih =>
      intro inputs words tests agree
      exact Runs.letTest words tests id rhs tail _ _
        (test_sound hr inputs words agree.word)
        (ih inputs words (setVar tests id
            (rustBoolTag (evalRustCondition inputs value)))
          (add_test_agrees agree id value))
  | switch sw st id f t reverse c tp fp hc ht hf iht ihf =>
      intro inputs words tests agree
      cases hcond : evalRustCondition inputs c with
      | true =>
          simp only [evalRustProgram, hcond]
          exact Runs.trueArm words tests id f t reverse _
            (by simpa [hcond, rustBoolTag] using agree.test id c hc)
            (iht inputs words tests agree)
      | false =>
          simp only [evalRustProgram, hcond]
          exact Runs.falseArm words tests id f t reverse _
            (by simpa [hcond, rustBoolTag] using agree.test id c hc)
            (ihf inputs words tests agree)

/-- A witness is built only by the constructor rules above. -/
structure WordWitness (sw : SymbolicEnv) (rhs : WordOp) where
  expression : WordExpr
  sound : WordMatches sw rhs expression

structure TestWitness (sw : SymbolicEnv) (rhs : TestOp) where
  condition : Condition
  sound : TestMatches sw rhs condition

structure StmtWitness (sw : SymbolicEnv) (st : SymTests)
    (body : Stmt) where
  program : Program
  sound : StmtMatches sw st body program

private def checkWord (sw : SymbolicEnv) (rhs : WordOp) :
    Option (WordWitness sw rhs) :=
  match rhs with
  | .constant n => some ⟨.lit n, .constant n⟩
  | .wrappingAdd a b =>
      match ha : sw a with
      | some u =>
        match hb : sw b with
        | some v => some ⟨.add u v, .add a b u v ha hb⟩
        | none => none
      | none => none
  | .wrappingMul a b =>
      match ha : sw a with
      | some u =>
        match hb : sw b with
        | some v => some ⟨.mul u v, .mul a b u v ha hb⟩
        | none => none
      | none => none

private def checkTest (sw : SymbolicEnv) (rhs : TestOp) :
    Option (TestWitness sw rhs) :=
  match rhs with
  | .eq a b =>
      match ha : sw a with
      | some u =>
        match hb : sw b with
        | some v => some ⟨.eq u v, .eq a b u v ha hb⟩
        | none => none
      | none => none
  | .lt a b =>
      match ha : sw a with
      | some u =>
        match hb : sw b with
        | some v => some ⟨.lt u v, .lt a b u v ha hb⟩
        | none => none
      | none => none
  | .le a b =>
      match ha : sw a with
      | some u =>
        match hb : sw b with
        | some v => some ⟨.le u v, .le a b u v ha hb⟩
        | none => none
      | none => none

/-- Total proof-producing verifier for the concrete imperative statement
grammar. Nonexistent registers, dangling tests and unsupported syntax fail. -/
private def checkStmt (fuel : Nat) (sw : SymbolicEnv) (st : SymTests)
    (body : Stmt) : Option (StmtWitness sw st body) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match body with
    | .ret id =>
      match he : sw id with
      | some e => some ⟨.ret e, .ret sw st id e he⟩
      | none => none
    | .letWord id rhs tail =>
      match checkWord sw rhs with
      | some ⟨e, hr⟩ =>
        match checkStmt fuel (setVar sw id e) st tail with
        | some ⟨p, ht⟩ =>
          some ⟨p, .letWord sw st id rhs tail e p hr ht⟩
        | none => none
      | none => none
    | .letTest id rhs tail =>
      match checkTest sw rhs with
      | some ⟨c, hr⟩ =>
        match checkStmt fuel sw (setVar st id c) tail with
        | some ⟨p, ht⟩ =>
          some ⟨p, .letTest sw st id rhs tail c p hr ht⟩
        | none => none
      | none => none
    | .switch id f t reverse =>
      match hc : st id with
      | some c =>
        match checkStmt fuel sw st t with
        | some ⟨tp, ht⟩ =>
          match checkStmt fuel sw st f with
          | some ⟨fp, hf⟩ =>
            some ⟨.branch c tp fp, .switch sw st id f t reverse c tp fp hc ht hf⟩
          | none => none
        | none => none
      | none => none

/-- Canonical text of precisely the Rust operations understood above. -/
def renderWord : WordOp → String
  | .constant n => s!"{n}u64"
  | .wrappingAdd a b => s!"x_{a}.wrapping_add(x_{b})"
  | .wrappingMul a b => s!"x_{a}.wrapping_mul(x_{b})"

def renderTest : TestOp → String
  | .eq a b => s!"u8::from(x_{a} == x_{b})"
  | .lt a b => s!"u8::from(x_{a} < x_{b})"
  | .le a b => s!"u8::from(x_{a} <= x_{b})"

def renderStmt : Stmt → String
  | .ret id => s!"    x_{id}\n"
  | .letWord id rhs tail =>
      s!"    let x_{id}: u64 = {renderWord rhs};\n" ++ renderStmt tail
  | .letTest id rhs tail =>
      s!"    let x_{id}: u8 = {renderTest rhs};\n" ++ renderStmt tail
  | .switch id f t reversed =>
      let a := if reversed then
        "        1 => {\n" ++ renderStmt t ++ "        }\n" ++
        "        0 => {\n" ++ renderStmt f ++ "        }\n"
      else
        "        0 => {\n" ++ renderStmt f ++ "        }\n" ++
        "        1 => {\n" ++ renderStmt t ++ "        }\n"
      "    match x_" ++ toString id ++ " {\n" ++ a ++
      "        _ => unreachable!(\"invalid Lean Bool tag\"),\n    }\n"

/-- Decode the actual Lean compiler IR into the restricted Rust *statement*
grammar, separately from Reader and its existing source-text predictor. -/
private def argVar : IR.Arg → Option Nat
  | .var id => some id.idx
  | .erased => none

private def argPair (args : Array IR.Arg) : Option (Nat × Nat) := do
  if args.size != 2 then none else
  let a ← args[0]? >>= argVar
  let b ← args[1]? >>= argVar
  some (a, b)

private def decodeWord : IR.Expr → Option WordOp
  | .lit (.num n) =>
      if n < modulus then some (.constant n) else none
  | .fap name args => do
      let (a, b) ← argPair args
      if name == `UInt64.add then some (.wrappingAdd a b)
      else if name == `UInt64.mul then some (.wrappingMul a b)
      else none
  | _ => none

private def decodeTest : IR.Expr → Option TestOp
  | .fap name args => do
      let (a, b) ← argPair args
      if name == `UInt64.decEq then some (.eq a b)
      else if name == `UInt64.decLt then some (.lt a b)
      else if name == `UInt64.decLe then some (.le a b)
      else none
  | _ => none

private structure ArmBodies where
  falseBody : IR.FnBody
  trueBody : IR.FnBody
  reversed : Bool

private def decodeArms (alts : Array IR.Alt) : Option ArmBodies := do
  if alts.size != 2 then none else
  let a ← alts[0]?
  let b ← alts[1]?
  match a, b with
  | .ctor fa fb, .ctor ta tb =>
      if fa.cidx == 0 && fa.name == `Bool.false &&
          ta.cidx == 1 && ta.name == `Bool.true then
        some ⟨fb, tb, false⟩
      else if fa.cidx == 1 && fa.name == `Bool.true &&
          ta.cidx == 0 && ta.name == `Bool.false then
        some ⟨tb, fb, true⟩
      else none
  | _, _ => none

private def decodeStmt (fuel : Nat) (body : IR.FnBody) : Option Stmt :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match body with
    | .ret arg => do
        return .ret (← argVar arg)
    | .vdecl id .uint64 expr tail => do
        return .letWord id.idx (← decodeWord expr) (← decodeStmt fuel tail)
    | .vdecl id .uint8 expr tail => do
        return .letTest id.idx (← decodeTest expr) (← decodeStmt fuel tail)
    | .case tid scr .uint8 alts => do
        if tid != `UInt8 then none else
        let arms ← decodeArms alts
        return .switch scr.idx
          (← decodeStmt fuel arms.falseBody)
          (← decodeStmt fuel arms.trueBody)
          arms.reversed
    | _ => none

structure Function where
  name : String
  left : Nat
  right : Nat
  body : Stmt

def decodeDecl (decl : IR.Decl) : Option Function := do
  match decl with
  | .fdecl name params .uint64 body _ =>
      if params.size != 2 then none else
      let some p0 := params[0]? | none
      let some p1 := params[1]? | none
      if p0.ty != .uint64 || p1.ty != .uint64 ||
          p0.borrow || p1.borrow || p0.x.idx == p1.x.idx then none
      else
        let body ← decodeStmt 100000 body
        let name := (name.toString.replace "\n" "_").replace "\r" "_"
        some ⟨name, p0.x.idx, p1.x.idx, body⟩
  | _ => none

def renderFunction (f : Function) : String :=
  s!"// Generated directly from Lean IR declaration: {f.name}\n" ++
  "#[allow(clippy::needless_return)]\n" ++
  "pub fn certified_scalar(x_" ++ toString f.left ++ ": u64, x_" ++
  toString f.right ++ ": u64) -> u64 {\n" ++
  renderStmt f.body ++ "}\n"

def inputNat (a b : UInt64) : Nat → Nat :=
  fun i => (inputWords a b i).toNat

def initialWords (left right : Nat) (a b : UInt64) : WordStore :=
  setVar (setVar (fun _ => none) left (inputNat a b 0))
    right (inputNat a b 1)

def initialTests : TestStore := fun _ => none
def initialSymTests : SymTests := fun _ => none

theorem empty_agrees (inputs : Nat → Nat) :
    EnvAgrees (fun _ => none) (fun _ => none)
      (fun _ => none) (fun _ => none) inputs := by
  constructor
  · intro i e h; cases h
  · intro i c h; cases h

theorem initial_agrees (left right : Nat) (a b : UInt64) :
    EnvAgrees (initialSym left right) initialSymTests
      (initialWords left right a b) initialTests (inputNat a b) := by
  exact add_word_agrees
    (add_word_agrees (empty_agrees (inputNat a b)) left (.arg 0))
    right (.arg 1)

structure Certificate where
  live : ReaderIRABIObservation.LiveCertificate
  statement : Stmt
  text : String
  textMatches : text = live.linked.emission.emitted
  programMatches :
    StmtMatches
      (initialSym live.linked.source.left live.linked.source.right)
      initialSymTests statement live.linked.source.program

/-- Exact native Reader output is matched against a second independently
rendered statement grammar. Source-IR semantics and ABI observations must
already be certified against the same modeled program. -/
def certify (root : Name) : CoreM Certificate := do
  let live ← ReaderIRABIObservation.certifyLive root
  let some original ← IR.findDecl root
    | throwError "Rust statement certification requires source IR: {root}"
  let some function := decodeDecl original
    | throwError "Rust statement grammar refused unsupported IR: {root}"
  let some witness := checkStmt 100000
    (initialSym function.left function.right) initialSymTests function.body
    | throwError "Rust statement grammar found unknown register or operation: {root}"
  if hl : function.left = live.linked.source.left then
    if hr : function.right = live.linked.source.right then
      if hp : witness.program = live.linked.source.program then
        let printed := renderFunction function
        if he : printed = live.linked.emission.emitted then
          return {
            live, statement := function.body, text := printed, textMatches := he,
            programMatches := by
              simpa only [← hl, ← hr, ← hp] using witness.sound
          }
        else
          throwError "Rust statement rendering disagrees with actual Reader text: {root}"
      else
        throwError "Rust statement execution program disagrees with source model: {root}"
    else
      throwError "Rust statement second parameter disagrees with source IR: {root}"
  else
    throwError "Rust statement first parameter disagrees with source IR: {root}"

/-- All source UInt64 inputs, the actual typed imperative statement grammar,
and the original source IR have the same value. The exact emitted string and
live ABI readback equalities appear explicitly in the conclusion. -/
theorem certified_statement_refines (c : Certificate) (a b : UInt64) :
    c.text = c.live.linked.emission.emitted ∧
    c.live.observed = c.live.expected ∧
    ∃ result,
      Runs c.statement
        (initialWords c.live.linked.source.left c.live.linked.source.right a b)
        initialTests result ∧
      result =
        (evalActualProgram (inputWords a b) c.live.linked.source.program).toNat := by
  refine ⟨c.textMatches, c.live.observedEqual, ?_⟩
  let env := inputNat a b
  let result := evalRustProgram env c.live.linked.source.program
  refine ⟨result, ?_, ?_⟩
  · exact statement_sound c.programMatches env
      (initialWords c.live.linked.source.left c.live.linked.source.right a b)
      initialTests
      (initial_agrees c.live.linked.source.left c.live.linked.source.right a b)
  · have h := modeled_compiler_refines (inputWords a b) c.live.linked.source.program
    rw [lowerProgram_correct] at h
    exact h

end ReaderRustStatement

#print axioms ReaderRustStatement.statement_sound
#print axioms ReaderRustStatement.certified_statement_refines

open Lean Elab Command

/-- This wrapper runs the *exact certified Reader function* under rustc.
No compiler backend substitute or textual rewrite of that function is used. -/
private def rustDriver : String :=
  "\nuse std::io::{self, BufRead};\n" ++
  "fn main() {\n" ++
  "    for line in io::stdin().lock().lines() {\n" ++
  "        let line = line.expect(\"read input\");\n" ++
  "        let mut words = line.split_ascii_whitespace();\n" ++
  "        let a: u64 = words.next().expect(\"first\").parse().expect(\"u64\");\n" ++
  "        let b: u64 = words.next().expect(\"second\").parse().expect(\"u64\");\n" ++
  "        assert!(words.next().is_none(), \"extra operand\");\n" ++
  "        println!(\"{}\", certified_scalar(a, b));\n" ++
  "    }\n" ++
  "}\n"

private def sourceResult (root : Name) (a b : UInt64) : UInt64 :=
  if root == `ScalarFixture.plus then ScalarFixture.plus a b
  else if root == `ScalarFixture.straightChain then ScalarFixture.straightChain a b
  else if root == `ScalarFixture.choose then ScalarFixture.choose a b
  else ScalarFixture.nested a b

private def testPairs : Array (UInt64 × UInt64) := Id.run do
  let edges : Array UInt64 := #[
    0, 1, 2, 3, 7, 42, 0x7FFFFFFFFFFFFFFF,
    0x8000000000000000, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF
  ]
  let mut pairs := #[]
  for a in edges do
    for b in edges do
      pairs := pairs.push (a,b)
  let mut x : UInt64 := 0x9E3779B97F4A7C15
  for _ in [:512] do
    x := x * 6364136223846793005 + 1442695040888963407
    let a := x
    x := x * 6364136223846793005 + 1442695040888963407
    let b := x
    pairs := pairs.push (a,b)
  return pairs

run_cmd do
  let pairs := testPairs
  let mut inputs := ""
  for (a,b) in pairs do
    inputs := inputs ++ s!"{a.toNat} {b.toNat}\n"
  liftIO <| IO.FS.writeFile "artifacts/reader-rust-execution-inputs.txt" inputs

  for root in #[`ScalarFixture.plus, `ScalarFixture.straightChain,
                `ScalarFixture.choose, `ScalarFixture.nested] do
    let c ← liftCoreM <| ReaderRustStatement.certify root
    let _ := ReaderRustStatement.certified_statement_refines c
    let name := root.toString.replace "ScalarFixture." ""
    liftIO <| IO.FS.writeFile s!"artifacts/reader-rust-exec-{name}.rs"
      (c.live.linked.emission.emitted ++ rustDriver)
    let mut expected := ""
    for (a,b) in pairs do
      expected := expected ++ s!"{(sourceResult root a b).toNat}\n"
    liftIO <| IO.FS.writeFile s!"artifacts/reader-rust-exec-{name}.expected" expected
    logInfo m!"Certified typed Rust statement execution against Reader: {root}, {pairs.size} original Lean oracles"

  let original ← liftCoreM <| IR.findDecl `ScalarFixture.subtract
  let some decl := original
    | throwError "subtraction negative source fixture missing"
  unless (ReaderRustStatement.decodeDecl decl).isNone do
    throwError "Rust statement grammar admitted unproved subtraction"
  logInfo "Rust statement execution checker correctly refused unsupported subtraction"
