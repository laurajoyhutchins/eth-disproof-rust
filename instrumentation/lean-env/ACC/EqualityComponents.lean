import Mathlib

/-!
# Exact contraction by equality components

An equality-only factor graph is closed under introducing further equality
edges: the edge-induced equivalence classes are the right representation.
The statement is intentionally about a *given surjective component map*.
Constructing that map from edges (e.g. by union-find) and its amortized
operational cost are separate executable/refinement obligations.

Every compatible assignment is uniquely determined by one Boolean value
per nonempty component. Its weighted sum factors into two-term component
sums without expanding the Boolean cube. The proof works over integers,
including negative weights.
-/

namespace ACC.EqualityComponents

open scoped BigOperators

/-- Assignments constant on every component of a class map. -/
def Compatible {I C : Type*} (classOf : I → C) (x : I → Bool) : Prop :=
  ∀ i j, classOf i = classOf j → x i = x j

/-- A finite set of compatible assignments inherits finiteness from
    the full finite Boolean cube. No enumeration algorithm is asserted. -/
noncomputable instance compatibleFintype
    {I C : Type*} [Fintype I] [DecidableEq I]
    (classOf : I → C) :
    Fintype {x : I → Bool // Compatible classOf x} := by
  classical
  exact Fintype.ofFinite _

/-- Every nonempty component contributes exactly one Boolean decision.
    Surjectivity is necessary: empty labels otherwise overcount by two. -/
noncomputable def compatibleEquiv {I C : Type*}
    (classOf : I → C) (hs : Function.Surjective classOf) :
    {x : I → Bool // Compatible classOf x} ≃ (C → Bool) where
  toFun x c := x.1 (Classical.choose (hs c))
  invFun y := ⟨fun i => y (classOf i), by
    intro i j hij
    exact congrArg y hij⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    change x.1 (Classical.choose (hs (classOf i))) = x.1 i
    exact x.2 _ _ (Classical.choose_spec (hs (classOf i)))
  right_inv y := by
    funext c
    change y (classOf (Classical.choose (hs c))) = y c
    rw [Classical.choose_spec (hs c)]

/-- Change variables from compatible wire assignments to one Boolean
    assignment per component. This does not enumerate equivalence classes. -/
theorem sum_compatible_eq_class_choices
    {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C]
    (classOf : I → C) (hs : Function.Surjective classOf)
    (weight : I → Bool → ℤ) :
    (∑ x : {x : I → Bool // Compatible classOf x},
       ∏ i : I, weight i (x.1 i)) =
    ∑ y : C → Bool, ∏ i : I, weight i (y (classOf i)) := by
  classical
  refine Fintype.sum_equiv (compatibleEquiv classOf hs) _ _ ?_
  intro x
  apply Finset.prod_congr rfl
  intro i _
  change weight i (x.1 i) =
    weight i (x.1 (Classical.choose (hs (classOf i))))
  exact congrArg (weight i)
    (x.2 i _ (Classical.choose_spec (hs (classOf i))).symm)

/-- A fixed class assignment groups a product into its component fibers. -/
theorem product_by_components
    {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C]
    (classOf : I → C) (weight : I → Bool → ℤ)
    (y : C → Bool) :
    (∏ i : I, weight i (y (classOf i))) =
    ∏ c : C, ∏ i ∈ (Finset.univ : Finset I) with classOf i = c,
      weight i (y c) := by
  classical
  calc
    (∏ i : I, weight i (y (classOf i))) =
      ∏ c : C, ∏ i ∈ (Finset.univ : Finset I) with classOf i = c,
        weight i (y (classOf i)) := by
      simpa using
        (Finset.prod_fiberwise_eq_prod_filter
          (Finset.univ : Finset I) (Finset.univ : Finset C)
          classOf (fun i => weight i (y (classOf i)))).symm
    _ = ∏ c : C, ∏ i ∈ (Finset.univ : Finset I) with classOf i = c,
          weight i (y c) := by
      apply Finset.prod_congr rfl
      intro c _
      apply Finset.prod_congr rfl
      intro i hi
      have hc : classOf i = c := (Finset.mem_filter.mp hi).2
      rw [hc]

/-- Exact finite contraction as independent weighted component choices.
    In particular, arbitrary overlapping equality constraints do not force
    exponentially many separated terms when the component map is known. -/
theorem sum_compatible_eq_component_product
    {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C]
    (classOf : I → C) (hs : Function.Surjective classOf)
    (weight : I → Bool → ℤ) :
    (∑ x : {x : I → Bool // Compatible classOf x},
       ∏ i : I, weight i (x.1 i)) =
    ∏ c : C, ∑ bit : Bool,
      ∏ i ∈ (Finset.univ : Finset I) with classOf i = c,
        weight i bit := by
  classical
  rw [sum_compatible_eq_class_choices classOf hs weight]
  calc
    (∑ y : C → Bool, ∏ i : I, weight i (y (classOf i))) =
      ∑ y : C → Bool,
        ∏ c : C, ∏ i ∈ (Finset.univ : Finset I) with classOf i = c,
          weight i (y c) := by
      apply Finset.sum_congr rfl
      intro y _
      exact product_by_components classOf weight y
    _ = ∏ c : C, ∑ bit : Bool,
          ∏ i ∈ (Finset.univ : Finset I) with classOf i = c,
            weight i bit := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset
          (Finset.univ : Finset Bool)
          (fun c bit =>
            ∏ i ∈ (Finset.univ : Finset I) with classOf i = c,
              weight i bit))

#print axioms ACC.EqualityComponents.sum_compatible_eq_class_choices
#print axioms ACC.EqualityComponents.product_by_components
#print axioms ACC.EqualityComponents.sum_compatible_eq_component_product

end ACC.EqualityComponents
