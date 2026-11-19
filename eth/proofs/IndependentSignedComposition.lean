import Mathlib

/-!
# All-context composition of exact signed Boolean-fiber eliminations

Each local step replaces a function of an internal Boolean variable and
the remaining ports by its exact integer sum over that variable.
For an arbitrary finite list of independently justified local steps,
the resulting boundary function equals the original full fiber sum.

The theorem is intentionally parametric in the *local exactness witnesses*.
The Lean quadratic-splitting, forced-substitution and low-weight interpolation
theorems establish the algebraic ingredients for those witnesses. There is
not yet a Lean proof that the emitted Rust transcript produces them.
-/

namespace IndependentETH.SignedComposition

open scoped BigOperators

/-- The exact integer sum over n Boolean internal coordinates, with
the innermost coordinate prepended to the remaining assignment. -/
def sumAssignments : (n : ℕ) → (List Bool → ℤ) → ℤ
  | 0, f => f []
  | n + 1, f =>
      sumAssignments n (fun tail => ∑ x : Bool, f (x :: tail))

/-- Substitution of pointwise-equal boundary functions is valid
under arbitrary remaining internal quantifiers. -/
theorem sumAssignments_congr
    (n : ℕ) (f g : List Bool → ℤ)
    (h : ∀ xs : List Bool, f xs = g xs) :
    sumAssignments n f = sumAssignments n g := by
  induction n generalizing f g with
  | zero =>
      exact h []
  | succ n ih =>
      change
        sumAssignments n (fun tail => ∑ x : Bool, f (x :: tail)) =
        sumAssignments n (fun tail => ∑ x : Bool, g (x :: tail))
      apply ih
      intro tail
      apply Finset.sum_congr rfl
      intro x _
      exact h (x :: tail)

/-- A local equality is enough to certify exact elimination regardless of
how many other internal variables remain. -/
theorem one_step_exact
    (n : ℕ) (before after : List Bool → ℤ)
    (h : ∀ tail : List Bool,
      after tail = ∑ x : Bool, before (x :: tail)) :
    sumAssignments n after = sumAssignments (n + 1) before := by
  change
    sumAssignments n after =
    sumAssignments n (fun tail => ∑ x : Bool, before (x :: tail))
  apply sumAssignments_congr
  exact h

/-- The certificate obligations for a list of successive one-bit rewrites.
The first item is the first result of eliminating one internal coordinate. -/
def StepChain (before : List Bool → ℤ) :
    List (List Bool → ℤ) → Prop
  | [] => True
  | after :: later =>
      (∀ tail : List Bool,
        after tail = ∑ x : Bool, before (x :: tail)) ∧
      StepChain after later

def terminal (before : List Bool → ℤ) :
    List (List Bool → ℤ) → (List Bool → ℤ)
  | [] => before
  | after :: later => terminal after later

/-- A checked sequence of local signed-interface rewrites is an exact
whole-fiber contraction for all exterior contexts, *independent of the
number of internal Boolean variables*. No independence of signs,
positivity, or low-rank assumption is needed beyond each local witness. -/
theorem chain_exact
    (n : ℕ) (before : List Bool → ℤ)
    (steps : List (List Bool → ℤ))
    (h : StepChain before steps) :
    sumAssignments n (terminal before steps) =
      sumAssignments (n + steps.length) before := by
  induction steps generalizing n before with
  | nil =>
      simp [terminal]
  | cons after later ih =>
      have hlocal : ∀ tail : List Bool,
          after tail = ∑ x : Bool, before (x :: tail) := h.1
      have hrest : StepChain after later := h.2
      change sumAssignments n (terminal after later) =
        sumAssignments (n + (later.length + 1)) before
      calc
        sumAssignments n (terminal after later) =
            sumAssignments (n + later.length) after := ih n after hrest
        _ = sumAssignments ((n + later.length) + 1) before :=
          one_step_exact (n + later.length) before after hlocal
        _ = sumAssignments (n + (later.length + 1)) before := by
          congr 1

/-- Two successive verified local transformations are exact. -/
theorem two_steps_exact
    (n : ℕ) (before middle after : List Bool → ℤ)
    (h₁ : ∀ tail : List Bool,
      middle tail = ∑ x : Bool, before (x :: tail))
    (h₂ : ∀ tail : List Bool,
      after tail = ∑ x : Bool, middle (x :: tail)) :
    sumAssignments n after = sumAssignments (n + 2) before := by
  calc
    sumAssignments n after = sumAssignments (n + 1) middle :=
      one_step_exact n middle after h₂
    _ = sumAssignments ((n + 1) + 1) before :=
      one_step_exact (n + 1) before middle h₁
    _ = sumAssignments (n + 2) before := by congr 1

#print axioms IndependentETH.SignedComposition.sumAssignments_congr
#print axioms IndependentETH.SignedComposition.one_step_exact
#print axioms IndependentETH.SignedComposition.chain_exact
#print axioms IndependentETH.SignedComposition.two_steps_exact

end IndependentETH.SignedComposition
