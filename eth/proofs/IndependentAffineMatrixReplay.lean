import Mathlib
import IndependentAffineRowOps

/-!
# Universal matrix-level refinement of row-operation replay

The existing AffineRowOps theorem states that applying the same valid
row operations to both sides of an equality preserves its solutions.

A native verifier instead transforms *coefficient matrices*, then
evaluates the transformed equations on variable assignments. This
file proves that these two orders of computation coincide for every
finite row count, finite variable count, assignment and finite trace.

This closes a mathematical matrix-evaluation/replay commuting square.
The theorem does not imply the compiled Rust Vec, allocator or indexing
operations refine these mathematical operations.
-/

namespace IndependentETH.AffineMatrixReplay

open IndependentETH.AffineRowOps

abbrev GF2 := ZMod 2

/-- An explicit finite source system, with every coefficient and RHS
stored separately, as in the verifier's dense Boolean matrix. -/
structure Matrix (m n : Nat) where
  coeff : Fin m → Fin n → GF2
  rhs : Fin m → GF2

/-- Evaluate the *actual source coefficient matrix* on one assignment. -/
def evaluate {m n : Nat} (a : Matrix m n)
    (assignment : Fin n → GF2) : RowValues m :=
  fun row => ∑ col : Fin n, a.coeff row col * assignment col

/-- Lift one legal row operation pointwise across *every* coefficient
column and across the RHS. -/
def transform {m n : Nat}
    (op : RowOp m) (a : Matrix m n) : Matrix m n where
  coeff := fun row col =>
    applyOp op (fun source => a.coeff source col) row
  rhs := applyOp op a.rhs

/-- Fundamental commuting square: evaluating after a row operation
is the same as applying that operation to the evaluated row values.
All variable assignments and all finite dimensions are quantified. -/
theorem evaluate_transform {m n : Nat} (op : RowOp m)
    (a : Matrix m n) (assignment : Fin n → GF2) :
    evaluate (transform op a) assignment =
      applyOp op (evaluate a assignment) := by
  funext row
  cases op with
  | permute σ =>
      simp [evaluate, transform, applyOp, Function.comp_def]
  | add target source hne =>
      by_cases h : row = target
      · subst row
        simp [evaluate, transform, applyOp, addRow, add_mul,
          Finset.sum_add_distrib]
      · simp [evaluate, transform, applyOp, addRow, h]

/-- Replaying arbitrary valid row operations on a coefficient matrix. -/
def replay {m n : Nat} (operations : List (RowOp m))
    (a : Matrix m n) : Matrix m n :=
  operations.foldl (fun current op => transform op current) a

theorem evaluate_replay {m n : Nat}
    (operations : List (RowOp m)) (a : Matrix m n)
    (assignment : Fin n → GF2) :
    evaluate (replay operations a) assignment =
      IndependentETH.AffineRowOps.replay operations
        (evaluate a assignment) := by
  induction operations generalizing a with
  | nil =>
      rfl
  | cons op rest ih =>
      change evaluate (replay rest (transform op a)) assignment =
        IndependentETH.AffineRowOps.replay rest
          (applyOp op (evaluate a assignment))
      rw [ih, evaluate_transform]

theorem rhs_replay {m n : Nat}
    (operations : List (RowOp m)) (a : Matrix m n) :
    (replay operations a).rhs =
      IndependentETH.AffineRowOps.replay operations a.rhs := by
  induction operations generalizing a with
  | nil =>
      rfl
  | cons op rest ih =>
      change (replay rest (transform op a)).rhs =
        IndependentETH.AffineRowOps.replay rest (applyOp op a.rhs)
      rw [ih]
      rfl

/-- Exact source-to-replay equation correspondence for EVERY
assignment, finite matrix and finite validated transcript.
Neither matrix contents nor source RHS are assumed correct. -/
theorem replay_preserves_source_solutions {m n : Nat}
    (operations : List (RowOp m)) (a : Matrix m n)
    (assignment : Fin n → GF2) :
    (∀ row, evaluate a assignment row = a.rhs row) ↔
      (∀ row, evaluate (replay operations a) assignment row =
        (replay operations a).rhs row) := by
  rw [evaluate_replay, rhs_replay]
  exact IndependentETH.AffineRowOps.replay_preserves operations
    (evaluate a assignment) a.rhs

#print axioms IndependentETH.AffineMatrixReplay.evaluate_transform
#print axioms IndependentETH.AffineMatrixReplay.evaluate_replay
#print axioms IndependentETH.AffineMatrixReplay.rhs_replay
#print axioms IndependentETH.AffineMatrixReplay.replay_preserves_source_solutions

end IndependentETH.AffineMatrixReplay
