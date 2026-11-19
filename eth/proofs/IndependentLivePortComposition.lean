import Mathlib

/-!
# Live-port composition: exact finite-sum boundary semantics

A shared port p must remain available while any future factor g depends
on p. Private variables of independent factors can be summed out before
multiplying their interfaces. These are generic finite-sum theorems over
a commutative semiring, not a Rust refinement or a complexity theorem.
-/

namespace IndependentETH.LivePorts

open scoped BigOperators

variable {A B P : Type*} [Fintype A] [Fintype B] [Fintype P]
variable {R : Type*} [CommSemiring R]

/-- Two independently eliminated private blocks can be combined without
enumerating their joint assignment table. The shared port stays fixed. -/
theorem merge_at_live_port
    (left : A → P → R) (right : B → P → R) (p : P) :
    (∑ a, left a p) * (∑ b, right b p) =
      ∑ a, ∑ b, left a p * right b p := by
  simp only [Finset.sum_mul, Finset.mul_sum]

/-- A future continuation may inspect the shared port. Exact interfaces
are contextual: they agree after weighting by *any* continuation. -/
theorem merge_preserves_future
    (left : A → P → R) (right : B → P → R) (future : P → R) :
    (∑ p, ((∑ a, left a p) * (∑ b, right b p)) * future p) =
      ∑ p, (∑ a, ∑ b, left a p * right b p) * future p := by
  simp only [merge_at_live_port]

/-- Once no future factor observes the port, summing it out is legal.
The theorem also identifies the final closed count exactly. -/
theorem close_dead_port
    (left : A → P → R) (right : B → P → R) :
    (∑ p, (∑ a, left a p) * (∑ b, right b p)) =
      ∑ p, ∑ a, ∑ b, left a p * right b p := by
  simp only [merge_at_live_port]

/-- A continuation that still depends on a live port cannot generally be
moved outside its sum. The following Boolean witness rules out that
incorrect early-elimination transformation. -/
theorem early_elimination_counterexample :
    (∑ p : Bool, (if p then (1 : ℕ) else 0) *
      (if p then 0 else (1 : ℕ))) ≠
    (∑ p : Bool, (if p then (1 : ℕ) else 0)) *
    (∑ p : Bool, (if p then 0 else (1 : ℕ))) := by
  decide

#print axioms IndependentETH.LivePorts.merge_at_live_port
#print axioms IndependentETH.LivePorts.merge_preserves_future
#print axioms IndependentETH.LivePorts.close_dead_port
#print axioms IndependentETH.LivePorts.early_elimination_counterexample
