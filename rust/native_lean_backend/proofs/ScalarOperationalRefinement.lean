import Init.Data.UInt.Lemmas

/-!
# Source and Rust-value semantics for a bounded Lean compiler fragment

This is a *model-level*, all-inputs proof for the reviewed UInt64 primitives
and Bool-branching grammar. The source semantics uses Lean's finite-word
addition and multiplication. The target semantics is the integer/modulo
behavior required of generated `u64.wrapping_add` and `wrapping_mul`.

The current Rust emitter is not implemented in Lean. The obligations that
actual `Lean.IR.Decl` decoding, name resolution, Rust text emission, rustc
execution and ownership effects implement these semantics remain open.
Do not cite this file as a general Lean-to-Rust compiler correctness theorem.
-/

namespace NativeRustScalarRefinement

/-- The pinned Linux x86-64 backend represents this IR type as Rust `u64`. -/
def modulus : Nat := 2 ^ 64

abbrev Word := Fin modulus

def literal (n : Nat) : Word :=
  ⟨n % modulus, Nat.mod_lt _ (by decide : 0 < modulus)⟩

/-- A source-level finite word expression; no implicit primitive fallback. -/
inductive WordExpr where
  | arg : Nat → WordExpr
  | lit : Nat → WordExpr
  | add : WordExpr → WordExpr → WordExpr
  | mul : WordExpr → WordExpr → WordExpr
  deriving Repr, DecidableEq

/-- Lean finite-word evaluation of accepted `UInt64.add` / `UInt64.mul`. -/
def evalSourceWord (env : Nat → Word) : WordExpr → Word
  | .arg i => env i
  | .lit n => literal n
  | .add a b => evalSourceWord env a + evalSourceWord env b
  | .mul a b => evalSourceWord env a * evalSourceWord env b

/-- Required Rust wrapping-value semantics, over independent Nat values. -/
def evalRustWord (env : Nat → Nat) : WordExpr → Nat
  | .arg i => env i
  | .lit n => n % modulus
  | .add a b => (evalRustWord env a + evalRustWord env b) % modulus
  | .mul a b => (evalRustWord env a * evalRustWord env b) % modulus

/-- A word-level proof obligation for a single emitted operation. -/
theorem finite_add_is_wrapping (a b : Word) :
    (a + b).val = (a.val + b.val) % modulus := by
  rfl

theorem finite_mul_is_wrapping (a b : Word) :
    (a * b).val = (a.val * b.val) % modulus := by
  rfl

/-- Every expression tree has equal source and modeled Rust values, for all
input environments. Depth and number of operations are unrestricted. -/
theorem word_refines (env : Nat → Word) (e : WordExpr) :
    evalRustWord (fun i => (env i).val) e = (evalSourceWord env e).val := by
  induction e with
  | arg i => rfl
  | lit n => rfl
  | add a b ha hb =>
    simp only [evalRustWord, evalSourceWord, finite_add_is_wrapping, ha, hb]
  | mul a b ha hb =>
    simp only [evalRustWord, evalSourceWord, finite_mul_is_wrapping, ha, hb]

/-- Comparison cases produce Lean Bool and, in the generated code, Rust
`u8::from(bool)`. The condition is stored as the Bool before tag conversion. -/
inductive Condition where
  | eq : WordExpr → WordExpr → Condition
  | lt : WordExpr → WordExpr → Condition
  | le : WordExpr → WordExpr → Condition
  deriving Repr, DecidableEq

def evalSourceCondition (env : Nat → Word) : Condition → Bool
  | .eq a b => decide ((evalSourceWord env a).val = (evalSourceWord env b).val)
  | .lt a b => decide ((evalSourceWord env a).val < (evalSourceWord env b).val)
  | .le a b => decide ((evalSourceWord env a).val ≤ (evalSourceWord env b).val)

def evalRustCondition (env : Nat → Nat) : Condition → Bool
  | .eq a b => decide (evalRustWord env a = evalRustWord env b)
  | .lt a b => decide (evalRustWord env a < evalRustWord env b)
  | .le a b => decide (evalRustWord env a ≤ evalRustWord env b)

/-- The source Bool test and the modeled Rust test agree for every condition. -/
theorem condition_refines (env : Nat → Word) (c : Condition) :
    evalRustCondition (fun i => (env i).val) c = evalSourceCondition env c := by
  cases c with
  | eq a b =>
    simp only [evalRustCondition, evalSourceCondition, word_refines]
  | lt a b =>
    simp only [evalRustCondition, evalSourceCondition, word_refines]
  | le a b =>
    simp only [evalRustCondition, evalSourceCondition, word_refines]

def rustBoolTag (value : Bool) : Nat :=
  if value then 1 else 0

theorem condition_tag_refines (env : Nat → Word) (c : Condition) :
    rustBoolTag (evalRustCondition (fun i => (env i).val) c) =
      (if evalSourceCondition env c then 1 else 0) := by
  rw [condition_refines]
  rfl

/-- The return/conditional part of the actual supported `FnBody` grammar.
Calls, joins, mutable heap updates and RC operations are NOT modeled here. -/
inductive Program where
  | ret : WordExpr → Program
  | branch : Condition → Program → Program → Program
  deriving Repr, DecidableEq

def evalSourceProgram (env : Nat → Word) : Program → Word
  | .ret e => evalSourceWord env e
  | .branch c t f =>
      if evalSourceCondition env c then evalSourceProgram env t
      else evalSourceProgram env f

def evalRustProgram (env : Nat → Nat) : Program → Nat
  | .ret e => evalRustWord env e
  | .branch c t f =>
      if evalRustCondition env c then evalRustProgram env t
      else evalRustProgram env f

/-- Compositional all-inputs refinement: any finite tree of supported
arithmetic expressions, comparisons, and branches preserves its return value. -/
theorem program_refines (env : Nat → Word) (program : Program) :
    evalRustProgram (fun i => (env i).val) program =
      (evalSourceProgram env program).val := by
  induction program with
  | ret e =>
    exact word_refines env e
  | branch c t f ht hf =>
    simp only [evalRustProgram, evalSourceProgram, condition_refines, ht, hf]
    cases evalSourceCondition env c <;> rfl

/-- The *actual* Lean `UInt64` primitive operations, not an independently
chosen finite-word source interpreter. -/
def evalActualUInt64 (env : Nat → UInt64) : WordExpr → UInt64
  | .arg i => env i
  | .lit n => UInt64.ofNat n
  | .add a b => evalActualUInt64 env a + evalActualUInt64 env b
  | .mul a b => evalActualUInt64 env a * evalActualUInt64 env b

/-- The canonical Lean `UInt64` library states the same wrapping equations
required by Rust `u64.wrapping_add` and `wrapping_mul`. -/
theorem actual_uint64_add_mod (a b : UInt64) :
    (a + b).toNat = (a.toNat + b.toNat) % modulus := by
  simpa only [modulus] using (UInt64.toNat_add a b)

theorem actual_uint64_mul_mod (a b : UInt64) :
    (a * b).toNat = (a.toNat * b.toNat) % modulus := by
  simpa only [modulus] using (UInt64.toNat_mul a b)

/-- All trees of real Lean `UInt64` operations refine the independent target
Nat/modulo interpretation. In particular this is stronger than the Fin-only
source model above, but still is not an emitted-code/rustc theorem. -/
theorem actual_uint64_word_refines (env : Nat → UInt64) (e : WordExpr) :
    evalRustWord (fun i => (env i).toNat) e = (evalActualUInt64 env e).toNat := by
  induction e with
  | arg i => rfl
  | lit n =>
    simp only [evalRustWord, evalActualUInt64, UInt64.toNat_ofNat', modulus]
  | add a b ha hb =>
    simp only [evalRustWord, evalActualUInt64, actual_uint64_add_mod, ha, hb]
  | mul a b ha hb =>
    simp only [evalRustWord, evalActualUInt64, actual_uint64_mul_mod, ha, hb]

def evalActualCondition (env : Nat → UInt64) : Condition → Bool
  | .eq a b => decide (evalActualUInt64 env a = evalActualUInt64 env b)
  | .lt a b => decide (evalActualUInt64 env a < evalActualUInt64 env b)
  | .le a b => decide (evalActualUInt64 env a ≤ evalActualUInt64 env b)

theorem actual_uint64_condition_refines (env : Nat → UInt64) (c : Condition) :
    evalRustCondition (fun i => (env i).toNat) c = evalActualCondition env c := by
  cases c with
  | eq a b =>
    simp [evalRustCondition, evalActualCondition, actual_uint64_word_refines,
      UInt64.toNat_inj]
  | lt a b =>
    simp [evalRustCondition, evalActualCondition, actual_uint64_word_refines,
      UInt64.lt_iff_toNat_lt]
  | le a b =>
    simp [evalRustCondition, evalActualCondition, actual_uint64_word_refines,
      UInt64.le_iff_toNat_le]

def evalActualProgram (env : Nat → UInt64) : Program → UInt64
  | .ret e => evalActualUInt64 env e
  | .branch c t f =>
      if evalActualCondition env c then evalActualProgram env t
      else evalActualProgram env f

/-- All inputs and all finite programs in the selected grammar: genuine Lean
UInt64 semantics are equal to the independent Rust wrapping-value model. -/
theorem actual_uint64_program_refines (env : Nat → UInt64) (program : Program) :
    evalRustProgram (fun i => (env i).toNat) program =
      (evalActualProgram env program).toNat := by
  induction program with
  | ret e =>
    exact actual_uint64_word_refines env e
  | branch c t f ht hf =>
    simp only [evalRustProgram, evalActualProgram,
      actual_uint64_condition_refines, ht, hf]
    cases evalActualCondition env c <;> rfl

#print axioms NativeRustScalarRefinement.word_refines
#print axioms NativeRustScalarRefinement.condition_refines
#print axioms NativeRustScalarRefinement.program_refines
#print axioms NativeRustScalarRefinement.actual_uint64_program_refines

end NativeRustScalarRefinement
