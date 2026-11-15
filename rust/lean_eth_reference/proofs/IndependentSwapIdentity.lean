import Mathlib

/-!
# Exact swap decomposition and arbitrary finite contraction

Anthropic, *A 2^o(n) Time Algorithm for 3-SAT*, summarized in
anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
eth/README.md: SWAP = I - 2·singlet.

In the ordered two-bit basis (00, 01, 10, 11), put
v = (0, 1, -1, 0). Then 2·singlet = v vᵀ, so SWAP = I - v vᵀ
over the integers.

The finite contraction theorem below takes an arbitrary finite set
of crossings and an arbitrary finite sum of weighted boundary states.
The weight may incorporate all other node tensors, equality constraints,
and edge incidences. Thus it does not require independent crossing states.

These are exact integer identities. The powerset expansion is not an
efficient algorithm: it has 2^|crossings| terms before grouping.
No relation to OpenAI's packet indices, 2-adic precision, source
routing, or recursive complexity is asserted.
-/

namespace IndependentETH

/-- Exchange 01 and 10, leaving 00 and 11 fixed. -/
def swapIndex (i : Fin 4) : Fin 4 :=
  if i = 1 then 2 else if i = 2 then 1 else i

/-- Integer numerator of the antisymmetric singlet vector. -/
def antisymmetric (i : Fin 4) : ℤ :=
  if i = 1 then 1 else if i = 2 then -1 else 0

/-- Entry-wise identity SWAP = I - vvᵀ, with v=(0,1,-1,0). -/
theorem swap_eq_identity_sub_singlet (i j : Fin 4) :
    (if swapIndex i = j then (1 : ℤ) else 0) =
      (if i = j then (1 : ℤ) else 0) -
        antisymmetric i * antisymmetric j := by
  fin_cases i <;> fin_cases j <;> norm_num [swapIndex, antisymmetric]

/-- The local swap entry, for explicit use in network contractions. -/
def swapEntry (i j : Fin 4) : ℤ :=
  if swapIndex i = j then 1 else 0

/-- The identity part of a local crossing. -/
def identityEntry (i j : Fin 4) : ℤ :=
  if i = j then 1 else 0

/-- The **signed** rank-one correction: -vᵢvⱼ, not an extra power of two. -/
def negativeSinglet (i j : Fin 4) : ℤ :=
  -(antisymmetric i * antisymmetric j)

theorem swapEntry_eq_singlet_plus_identity (i j : Fin 4) :
    swapEntry i j = negativeSinglet i j + identityEntry i j := by
  unfold swapEntry negativeSinglet identityEntry
  rw [swap_eq_identity_sub_singlet]
  ring

/--
Expand a finite contraction of local sums and group the terms by the
number of selected correction factors.

* 'crossings' is an arbitrary finite set, including the empty set.
* 'states' is an arbitrary finite set of shared boundary assignments.
* 'coeff' can encode all surrounding tensors and incidence constraints.
* 'correction' and 'baseline' may depend on the entire assignment.

No independence of boundary variables or nonzero/positivity hypothesis
is needed. In particular this is valid for negative integer tensors.
-/
theorem finite_contraction_grouped {ι κ : Type*} [DecidableEq ι]
    (crossings : Finset ι) (states : Finset κ)
    (coeff : κ → ℤ) (correction baseline : κ → ι → ℤ) :
    (∑ x ∈ states, coeff x *
      ∏ e ∈ crossings, (correction x e + baseline x e)) =
    ∑ weight ∈ Finset.range (crossings.card + 1),
      ∑ selected ∈ crossings.powersetCard weight,
        ∑ x ∈ states, coeff x *
          ((∏ e ∈ selected, correction x e) *
            (∏ e ∈ crossings \ selected, baseline x e)) := by
  classical
  calc
    (∑ x ∈ states, coeff x *
      ∏ e ∈ crossings, (correction x e + baseline x e)) =
        ∑ x ∈ states, coeff x *
          (∑ selected ∈ crossings.powerset,
            (∏ e ∈ selected, correction x e) *
              (∏ e ∈ crossings \ selected, baseline x e)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.prod_add]
    _ = ∑ x ∈ states,
          ∑ selected ∈ crossings.powerset,
            coeff x * ((∏ e ∈ selected, correction x e) *
              (∏ e ∈ crossings \ selected, baseline x e)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = ∑ selected ∈ crossings.powerset,
          ∑ x ∈ states, coeff x *
            ((∏ e ∈ selected, correction x e) *
              (∏ e ∈ crossings \ selected, baseline x e)) := by
          rw [Finset.sum_comm]
    _ = ∑ weight ∈ Finset.range (crossings.card + 1),
          ∑ selected ∈ crossings.powersetCard weight,
            ∑ x ∈ states, coeff x *
              ((∏ e ∈ selected, correction x e) *
                (∏ e ∈ crossings \ selected, baseline x e)) := by
          rw [Finset.sum_powerset]

/--
Every integer network contraction with finitely many two-bit SWAP
crossings equals its exact signed-singlet expansion grouped by weight.

Here 'row' and 'col' may depend on the entire common state. Hence
wiring, shared variables, and external tensors are already covered
by the universally quantified input data, not assumed independent.
-/
theorem finite_swap_contraction_grouped {ι κ : Type*} [DecidableEq ι]
    (crossings : Finset ι) (states : Finset κ)
    (coeff : κ → ℤ) (row col : κ → ι → Fin 4) :
    (∑ x ∈ states, coeff x *
      ∏ e ∈ crossings, swapEntry (row x e) (col x e)) =
    ∑ weight ∈ Finset.range (crossings.card + 1),
      ∑ selected ∈ crossings.powersetCard weight,
        ∑ x ∈ states, coeff x *
          ((∏ e ∈ selected,
              negativeSinglet (row x e) (col x e)) *
            (∏ e ∈ crossings \ selected,
              identityEntry (row x e) (col x e))) := by
  classical
  calc
    (∑ x ∈ states, coeff x *
      ∏ e ∈ crossings, swapEntry (row x e) (col x e)) =
        ∑ x ∈ states, coeff x *
          ∏ e ∈ crossings,
            (negativeSinglet (row x e) (col x e) +
              identityEntry (row x e) (col x e)) := by
          simp_rw [swapEntry_eq_singlet_plus_identity]
    _ = _ := finite_contraction_grouped crossings states coeff
      (fun x e => negativeSinglet (row x e) (col x e))
      (fun x e => identityEntry (row x e) (col x e))

#print axioms IndependentETH.swap_eq_identity_sub_singlet
#print axioms IndependentETH.finite_contraction_grouped
#print axioms IndependentETH.finite_swap_contraction_grouped

end IndependentETH
