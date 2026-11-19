import Mathlib

/-!
# Source-list to GF(2) coefficient correctness

The Rust checker reconstructs its matrix from source variable-name
lists, toggling the coefficient bit for each occurrence. In GF(2),
the coefficient is the sum of unit basis indicators, so repeats cancel.

This proves the mathematical correctness of that source-to-row
transformation for any finite variable type and *any* literal list.
It does not prove the Rust BTreeMap lookup, string encoding or memory
behavior.
-/

namespace IndependentETH.AffineSourceRows

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev GF2 := ZMod 2

/-- Each source occurrence contributes one, so repeated names toggle
the corresponding coefficient exactly as in the Rust row constructor. -/
def sourceCoeff (names : List V) (col : V) : GF2 :=
  (names.map (fun name => if name = col then (1 : GF2) else 0)).sum

/-- A source literal list interpreted as a GF(2) parity sum is exactly
the value obtained by reconstructing the dense coefficient row. -/
theorem sourceCoeff_eval (names : List V) (assignment : V → GF2) :
    (∑ col : V, sourceCoeff names col * assignment col) =
      (names.map assignment).sum := by
  classical
  induction names with
  | nil =>
      simp [sourceCoeff]
  | cons name tail ih =>
      have hBasis :
          (∑ col : V,
            (if name = col then (1 : GF2) else 0) * assignment col) =
          assignment name := by
        simp
      calc
        (∑ col : V, sourceCoeff (name :: tail) col * assignment col) =
            (∑ col : V,
              ((if name = col then (1 : GF2) else 0) +
                sourceCoeff tail col) * assignment col) := by
              rfl
        _ = (∑ col : V,
              (if name = col then (1 : GF2) else 0) * assignment col) +
              (∑ col : V, sourceCoeff tail col * assignment col) := by
                simp [add_mul, Finset.sum_add_distrib]
        _ = assignment name + (tail.map assignment).sum := by
              rw [hBasis, ih]
        _ = ((name :: tail).map assignment).sum := by
              simp

/-- In characteristic two, naming a variable twice cancels it. -/
theorem sourceCoeff_duplicate (name : V) (tail : List V) (col : V) :
    sourceCoeff (name :: name :: tail) col = sourceCoeff tail col := by
  classical
  by_cases h : name = col
  · simp [sourceCoeff, h, ← add_assoc, show (1 : GF2) + 1 = 0 by decide]
  · simp [sourceCoeff, h]

def bit (v : Bool) : GF2 := if v then 1 else 0

theorem bit_xor (a b : Bool) :
    bit (a ^^ b) = bit a + bit b := by
  cases a <;> cases b <;> decide

theorem bit_foldl_xor (values : List Bool) (start : Bool) :
    bit (values.foldl (· ^^ ·) start) =
      bit start + (values.map bit).sum := by
  induction values generalizing start with
  | nil =>
      simp
  | cons a rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, bit_xor]
      abel

/-- Direct XOR evaluation of the original variable-name occurrences
agrees with the independently reconstructed GF(2) coefficient row. -/
theorem sourceRow_boolean_correct
    (names : List V) (assignment : V → Bool) :
    bit ((names.map assignment).foldl (· ^^ ·) false) =
      ∑ col : V, sourceCoeff names col * bit (assignment col) := by
  rw [bit_foldl_xor]
  simp only [bit, Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [sourceCoeff_eval]
  simp only [List.map_map, Function.comp_def]

#print axioms IndependentETH.AffineSourceRows.sourceCoeff_eval
#print axioms IndependentETH.AffineSourceRows.sourceCoeff_duplicate
#print axioms IndependentETH.AffineSourceRows.bit_xor
#print axioms IndependentETH.AffineSourceRows.bit_foldl_xor
#print axioms IndependentETH.AffineSourceRows.sourceRow_boolean_correct
