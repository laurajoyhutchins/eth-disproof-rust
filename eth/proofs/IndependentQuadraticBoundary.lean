import Mathlib

/-!
# Quadratic Boolean boundary modes: first exact algebraic interface

Values live in the integers although the phase is Boolean. Affine and
quadratic phases have explicit bounded-degree coefficient syntax.
The exact projection and stitching rules hold for every exterior setting.

This is not yet a source-specific proof of Anthropic's eight-square
factorization or OpenAI's truncated moment recursion. A computable
canonical RREF and full bit-cost refinement remain separate obligations.
-/

namespace IndependentETH.QuadraticBoundary

open scoped BigOperators

/-- A sign evaluated as an exact integer, never modulo two. -/
def sign (bit : Bool) : ℤ := if bit = true then -1 else 1

theorem sign_xor (a b : Bool) : sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> decide

/-- Summing a linear character over one internal Boolean variable. -/
theorem sum_sign_xor (a ell : Bool) :
    (∑ x : Bool, sign (a ^^ (x && ell))) =
      if ell = true then 0 else 2 * sign a := by
  cases a <;> cases ell <;> decide

/-- An affine ANF with explicitly bounded polynomial degree. -/
structure Affine (n : ℕ) where
  constant : Bool
  linear : Fin n → Bool

/-- A quadratic ANF. Diagonal terms are allowed as redundant input syntax. -/
structure Quadratic (n : ℕ) where
  constant : Bool
  linear : Fin n → Bool
  quadratic : Fin n → Fin n → Bool

/-- XOR parity of finitely many Boolean indicators. -/
def xorParity {α : Type*} [Fintype α] [DecidableEq α] (f : α → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => f i = true)).card % 2 = 1)

def Affine.eval {n : ℕ} (a : Affine n) (b : Fin n → Bool) : Bool :=
  a.constant ^^ xorParity (fun i => a.linear i && b i)

def Quadratic.eval {n : ℕ} (q : Quadratic n) (b : Fin n → Bool) : Bool :=
  q.constant ^^ xorParity (fun i => q.linear i && b i) ^^
    xorParity (fun ij : Fin n × Fin n => q.quadratic ij.1 ij.2 && b ij.1 && b ij.2)

/-- The internal variable x occurs with an affine coefficient, while the
boundary-only phase is quadratic. -/
structure SplitPhase (n : ℕ) where
  base : Quadratic n
  mixed : Affine n

def SplitPhase.eval {n : ℕ} (p : SplitPhase n) (x : Bool)
    (b : Fin n → Bool) : Bool :=
  p.base.eval b ^^ (x && p.mixed.eval b)

/-- The exact value of free-variable elimination for every boundary value. -/
theorem project_free_exact {n : ℕ} (p : SplitPhase n) (b : Fin n → Bool) :
    (∑ x : Bool, sign (p.eval x b)) =
      if p.mixed.eval b = true then 0 else 2 * sign (p.base.eval b) := by
  exact sum_sign_xor (p.base.eval b) (p.mixed.eval b)

/-- Common integer powers of two and boundary feasibility may be retained
through the projection, with a new affine support condition. -/
theorem project_free_weighted_exact {n : ℕ} (p : SplitPhase n)
    (feasible : (Fin n → Bool) → Bool) (k : ℕ) (b : Fin n → Bool) :
    (∑ x : Bool, if feasible b = true then
        (2 : ℤ) ^ k * sign (p.eval x b) else 0) =
      (if (feasible b && !(p.mixed.eval b)) = true then
        (2 : ℤ) ^ (k + 1) * sign (p.base.eval b) else 0) := by
  cases hf : feasible b <;> cases hl : p.mixed.eval b <;>
    cases hq : p.base.eval b <;>
    simp [SplitPhase.eval, sign, hl, hq, pow_succ] <;> ring

/-- Shannon-style stitching of complementary supports in exact integers. -/
theorem stitch_sign (selector a b : Bool) :
    (if selector = true then (0 : ℤ) else sign a) +
      (if selector = true then sign b else 0) =
    sign (a ^^ (selector && (a ^^ b))) := by
  cases selector <;> cases a <;> cases b <;> decide

/-- Stitching is valid if an explicit quadratic witness is supplied. The
degree restriction cannot be inferred from an arbitrary phase expression. -/
theorem quadratic_stitch_exact {n : ℕ} (selector : Affine n)
    (left right combined : Quadratic n)
    (hdegree : ∀ b : Fin n → Bool,
      combined.eval b = (left.eval b ^^ (selector.eval b &&
        (left.eval b ^^ right.eval b))))
    (b : Fin n → Bool) :
    (if selector.eval b = true then (0 : ℤ) else sign (left.eval b)) +
      (if selector.eval b = true then sign (right.eval b) else 0) =
        sign (combined.eval b) := by
  rw [hdegree b]
  exact stitch_sign (selector.eval b) (left.eval b) (right.eval b)

/-- Two different supported modes collapse to one quadratic phase. -/
theorem two_to_one_example (b₀ b₁ : Bool) :
    (if b₀ = true then (0 : ℤ) else 1) +
      (if b₀ = true then sign b₁ else 0) =
        sign (b₀ && b₁) := by
  cases b₀ <;> cases b₁ <;> decide

#print axioms IndependentETH.QuadraticBoundary.sum_sign_xor
#print axioms IndependentETH.QuadraticBoundary.project_free_exact
#print axioms IndependentETH.QuadraticBoundary.project_free_weighted_exact
#print axioms IndependentETH.QuadraticBoundary.quadratic_stitch_exact
#print axioms IndependentETH.QuadraticBoundary.two_to_one_example

end IndependentETH.QuadraticBoundary
