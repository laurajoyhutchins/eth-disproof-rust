import Mathlib

/-!
# Algebraic correctness of general affine row-operation traces

The predicates in a linear system are componentwise equalities of
two row vectors over GF(2). Row permutations and adding one row to a
*distinct* row preserve all solutions, in both directions.

This proves the mathematics for arbitrary row counts and arbitrarily long
traces. It does not establish that the native Rust transcript checker
implements these Lean definitions; that refinement is a separate obligation.
-/

namespace IndependentETH.AffineRowOps

abbrev RowValues (m : ℕ) := Fin m → ZMod 2

/-- Replace a target row by target + source over GF(2). -/
def addRow {m : ℕ} (target source : Fin m) (v : RowValues m) : RowValues m :=
  fun i => if i = target then v target + v source else v i

/-- Add-row preserves the conjunction of all row equations, for any RHS. -/
theorem addRow_preserves
    {m : ℕ} (target source : Fin m) (hne : target ≠ source)
    (lhs rhs : RowValues m) :
    (∀ i, lhs i = rhs i) ↔
      (∀ i, addRow target source lhs i = addRow target source rhs i) := by
  classical
  constructor
  · intro h i
    by_cases hi : i = target
    · subst i
      simp [addRow, h target, h source]
    · simpa [addRow, hi] using h i
  · intro h i
    by_cases hi : i = target
    · subst i
      have hs : lhs source = rhs source := by
        have hsrc := h source
        simpa [addRow, Ne.symm hne] using hsrc
      have ht : lhs target + lhs source = rhs target + rhs source := by
        have ht := h target
        simpa [addRow] using ht
      rw [hs] at ht
      exact add_right_cancel ht
    · simpa [addRow, hi] using h i

/-- Any row permutation, including a swap, preserves the equation set. -/
theorem permute_preserves
    {m : ℕ} (σ : Equiv.Perm (Fin m))
    (lhs rhs : RowValues m) :
    (∀ i, lhs i = rhs i) ↔
      (∀ i, lhs (σ i) = rhs (σ i)) := by
  constructor
  · intro h i
    exact h (σ i)
  · intro h i
    simpa using h (σ.symm i)

inductive RowOp (m : ℕ) where
  | permute (σ : Equiv.Perm (Fin m))
  | add (target source : Fin m) (hne : target ≠ source)

def applyOp {m : ℕ} (op : RowOp m) (v : RowValues m) : RowValues m :=
  match op with
  | .permute σ => v ∘ σ
  | .add target source _ => addRow target source v

theorem applyOp_preserves
    {m : ℕ} (op : RowOp m) (lhs rhs : RowValues m) :
    (∀ i, lhs i = rhs i) ↔
      (∀ i, applyOp op lhs i = applyOp op rhs i) := by
  cases op with
  | permute σ =>
      exact permute_preserves σ lhs rhs
  | add target source hne =>
      exact addRow_preserves target source hne lhs rhs

def replay {m : ℕ} (ops : List (RowOp m)) (v : RowValues m) : RowValues m :=
  ops.foldl (fun current op => applyOp op current) v

/-- All finite accepted row transcripts preserve the solution set exactly. -/
theorem replay_preserves
    {m : ℕ} (ops : List (RowOp m)) (lhs rhs : RowValues m) :
    (∀ i, lhs i = rhs i) ↔
      (∀ i, replay ops lhs i = replay ops rhs i) := by
  induction ops generalizing lhs rhs with
  | nil =>
      simp [replay]
  | cons op tail ih =>
      have hfirst := applyOp_preserves op lhs rhs
      have hrest := ih (applyOp op lhs) (applyOp op rhs)
      simpa [replay, List.foldl_cons] using hfirst.trans hrest

#print axioms IndependentETH.AffineRowOps.addRow_preserves
#print axioms IndependentETH.AffineRowOps.permute_preserves
#print axioms IndependentETH.AffineRowOps.applyOp_preserves
#print axioms IndependentETH.AffineRowOps.replay_preserves


/-! ## Total word-level admission into the solution-preserving row language

Rust's raw contract supplies an 8-bit operation tag, 64-bit row indices
and 64-bit pivot indices. Unlike the finite generated audit examples,
this reference decoder and its preservation results quantify over
*every* possible raw word, list length, matrix row count, pivot width
and modeled address width.

The decoder below is a Lean specification, not an independently proven
translation of Rust's implementation. Resource refusal for dense matrix
cells and source parsing occur at distinct boundaries.
-/

namespace WordAdmission

structure RawStep where
  tag : BitVec 8
  first : BitVec 64
  second : BitVec 64
  deriving Repr, DecidableEq

structure RawCertificate where
  version : BitVec 8
  steps : List RawStep
  pivots : List (BitVec 64)
  deriving Repr, DecidableEq

structure DecodedCertificate (rows internal : Nat) where
  operations : List (RowOp rows)
  pivots : List (Fin internal)

/-- An index is representable on the modeled address-width machine AND
is actually in bounds for the indicated native collection. -/
def decodeIndex (count addressWidth : Nat)
    (word : BitVec 64) : Option (Fin count) :=
  if h : word.toNat < count ∧ word.toNat < 2 ^ addressWidth then
    some ⟨word.toNat, h.1⟩
  else none

theorem decoded_index_bounded
    (count addressWidth : Nat) (word : BitVec 64)
    (index : Fin count)
    (h : decodeIndex count addressWidth word = some index) :
    index.val < 2 ^ addressWidth := by
  by_cases hb : word.toNat < count ∧ word.toNat < 2 ^ addressWidth
  · simp only [decodeIndex, dif_pos hb] at h
    cases h
    exact hb.2
  · simp [decodeIndex, hb] at h

/-- Decode only swap and distinct-row XOR operations. Both are carried
by the existing algebraic RowOp type whose semantics are proved. -/
def decodeStep (rows addressWidth : Nat)
    (raw : RawStep) : Option (RowOp rows) := do
  let first ← decodeIndex rows addressWidth raw.first
  let second ← decodeIndex rows addressWidth raw.second
  if h : first ≠ second then
    if raw.tag == (0 : BitVec 8) then
      some (.permute (Equiv.swap first second))
    else if raw.tag == (1 : BitVec 8) then
      some (.add first second h)
    else none
  else none

def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && strictlyIncreasing (b :: rest)

/-- Exact source-independent admission requirements. The count checks
precede allocation, and every concrete index is decoded into Fin. -/
def headerOK (raw : RawCertificate)
    (rows internal maxSteps : Nat) : Bool :=
  (raw.version == (1 : BitVec 8)) &&
  decide (raw.steps.length ≤ maxSteps) &&
  decide (raw.pivots.length ≤ rows) &&
  decide (raw.pivots.length ≤ internal) &&
  strictlyIncreasing (raw.pivots.map BitVec.toNat)

/-- A *total* mathematical decoder: every ill-formed raw word or list
refuses; every accepted index is in-range and addressable. The typed
output contains only invertible row transformations. -/
def decodeCertificate (raw : RawCertificate)
    (rows internal maxSteps addressWidth : Nat) :
    Option (DecodedCertificate rows internal) :=
  if headerOK raw rows internal maxSteps then do
    let operations ← raw.steps.mapM (decodeStep rows addressWidth)
    let pivots ← raw.pivots.mapM (decodeIndex internal addressWidth)
    some ⟨operations, pivots⟩
  else none

/-- Every successfully admitted raw transcript preserves the solution
set for *all* row assignments, independent of transcript length.
There is no finite fixture assumption. -/
theorem admitted_replay_preserves
    (raw : RawCertificate)
    (rows internal maxSteps addressWidth : Nat)
    (decoded : DecodedCertificate rows internal)
    (_h : decodeCertificate raw rows internal maxSteps addressWidth =
      some decoded)
    (lhs rhs : RowValues rows) :
    (∀ i, lhs i = rhs i) ↔
      (∀ i, replay decoded.operations lhs i =
        replay decoded.operations rhs i) :=
  replay_preserves decoded.operations lhs rhs

/-- Even one accepted raw operation cannot turn a valid equality of
equation rows into an invalid one, or vice versa. -/
theorem admitted_step_preserves
    (raw : RawStep) (rows addressWidth : Nat)
    (decoded : RowOp rows)
    (_h : decodeStep rows addressWidth raw = some decoded)
    (lhs rhs : RowValues rows) :
    (∀ i, lhs i = rhs i) ↔
      (∀ i, applyOp decoded lhs i = applyOp decoded rhs i) :=
  applyOp_preserves decoded lhs rhs

/-- Concrete boundary cases are consequences of the word-level model;
the quantified theorems above do not depend on these examples. -/
example :
    (decodeStep 2 32 ⟨0, 0, 1⟩).isSome = true := by decide
example :
    (decodeStep 2 32 ⟨2, 0, 1⟩).isNone = true := by decide
example :
    (decodeStep 2 32 ⟨1, 0, 0⟩).isNone = true := by decide
example :
    (decodeIndex 3 32 (BitVec.ofNat 64 (2 ^ 40))).isNone = true := by decide

#print axioms IndependentETH.AffineRowOps.WordAdmission.decoded_index_bounded
#print axioms IndependentETH.AffineRowOps.WordAdmission.admitted_step_preserves
#print axioms IndependentETH.AffineRowOps.WordAdmission.admitted_replay_preserves

end WordAdmission
