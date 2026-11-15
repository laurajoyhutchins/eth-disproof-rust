/-
Borrowed formal mathematics: Mathlib (pinned revision d13f23b723b8a846827a245b89c10fc7d3f11612).
Literature context: Markov and Shi, SIAM J. Comput. 38 (2008), 963-981,
DOI 10.1137/050644756, tensor-network contraction formalism.
This file does NOT claim that Markov and Shi proved the exact Mathlib lemma,
nor does it prove the source OAI factor-routing bijection.
-/
import Mathlib

open scoped BigOperators
open Finset

namespace ETH.LiteratureImports

universe u v w
variable {Group : Type u} [Fintype Group]
variable {Choice : Group → Type v}
variable {R : Type w} [CommSemiring R]

/--
The many-group algebraic part of the ETH `mode_product_contraction` obligation.

The actual source routing remains an explicit input:
* `route` must be a bijection between global and group-local assignments;
* `hvalid` must identify exactly the assignments permitted by the child domains;
* `hfactor` must show the source integrand equals the product of the child terms.

Once these conditions are proved, the *already formalized* Mathlib theorem
`Finset.prod_univ_sum` performs all many-group distribution. The result
is over a commutative semiring, so it is compatible with truncated coefficient
rings; it does not divide by any interpolation denominator.
-/
theorem mode_product_contraction
    {Global : Type*}
    (globalAssignments : Finset Global)
    (choices : ∀ g : Group, Finset (Choice g))
    (route : Global ≃ (∀ g : Group, Choice g))
    (contribution : Global → R)
    (child : ∀ g : Group, Choice g → R)
    (hvalid : ∀ a : Global,
      a ∈ globalAssignments ↔ route a ∈ Fintype.piFinset choices)
    (hfactor : ∀ a ∈ globalAssignments,
      contribution a = ∏ g : Group, child g (route a g)) :
    (∑ a ∈ globalAssignments, contribution a) =
      ∏ g : Group, ∑ x ∈ choices g, child g x := by
  classical
  calc
    (∑ a ∈ globalAssignments, contribution a) =
        ∑ x ∈ Fintype.piFinset choices, ∏ g : Group, child g (x g) := by
      apply Finset.sum_equiv route
      · exact hvalid
      · exact hfactor
    _ = ∏ g : Group, ∑ x ∈ choices g, child g x :=
      (Finset.prod_univ_sum choices child).symm

/-- The two-group case is a direct specialization, not the source routing proof. -/
theorem independent_pair
    {A B : Type*} [Fintype A] [Fintype B]
    (left : A → R) (right : B → R) :
    (∑ a : A, ∑ b : B, left a * right b) =
      (∑ a : A, left a) * (∑ b : B, right b) := by
  exact (Fintype.sum_mul_sum left right).symm

-- Evidence: the source-side obligations are visible in the elaborated theorem.
#print axioms mode_product_contraction
#print axioms independent_pair

end ETH.LiteratureImports
