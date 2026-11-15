import Mathlib

/-!
# A local exact swap decomposition

Anthropic, *A 2^o(n) Time Algorithm for 3-SAT*, summarized in
anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
eth/README.md: SWAP = I - 2·singlet.

In the ordered two-bit basis (00, 01, 10, 11), put
v = (0, 1, -1, 0). Then 2·singlet = v vᵀ, so SWAP = I - v vᵀ
over the integers. This theorem checks the 4×4 **local identity**;
it makes no claim about the original OpenAI network, grouped ranks,
routing, tensor precision, or the end-to-end recursion cost.
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

#print axioms IndependentETH.swap_eq_identity_sub_singlet

end IndependentETH
