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
