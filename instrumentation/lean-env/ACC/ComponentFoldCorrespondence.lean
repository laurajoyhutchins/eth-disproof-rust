import Mathlib
import ACC.CheckedComponentArithmetic

/-!
# Class-indexed partial arithmetic with a vertex-major update schedule

The earlier arithmetic interpreter accepted already-grouped weight lists. The
Rust kernel instead initializes two products for each certified class, scans
input variables in order, and updates the two products belonging to the
current variable's class. Only after that scan does it add the two products
per class and multiply the class sums.

This model makes the *actual accumulator update shape* explicit, including
the order of source-variable updates and independent checked i128 operations.
We prove successful runs refine an unbounded integer fold and establish a
fiber-product invariant for every class. It is a Lean reference semantics,
not a proof of the compiled Rust loops.
-/

namespace ACC.ComponentFoldCorrespondence

open ACC.CheckedComponentArithmetic

abbrev Products (c : ℕ) := Fin c → ℤ × ℤ

/-- Exactly one class entry is updated, using the two unary weights. -/
def uncheckedStep {c : ℕ}
    (acc : Products c) (item : Fin c × (ℤ × ℤ)) : Products c :=
  fun k =>
    if item.1 = k then
      ((acc k).1 * item.2.1, (acc k).2 * item.2.2)
    else acc k

/-- The Rust-style partial update refuses if either class product
    leaves the signed 128-bit range. -/
def checkedStep {c : ℕ}
    (acc : Products c) (item : Fin c × (ℤ × ℤ)) : Option (Products c) := do
  let zero ← checkedMul (acc item.1).1 item.2.1
  let one ← checkedMul (acc item.1).2 item.2.2
  some (fun k => if item.1 = k then (zero, one) else acc k)

/-- A successful local update is exactly the unbounded update. -/
theorem checkedStep_sound {c : ℕ}
    (acc : Products c) (item : Fin c × (ℤ × ℤ))
    (result : Products c) (h : checkedStep acc item = some result) :
    result = uncheckedStep acc item := by
  cases hz : checkedMul (acc item.1).1 item.2.1 with
  | none =>
      simp [checkedStep, hz] at h
  | some zero =>
      cases ho : checkedMul (acc item.1).2 item.2.2 with
      | none =>
          simp [checkedStep, hz, ho] at h
      | some one =>
          have hout : (fun k => if item.1 = k then (zero, one) else acc k) = result := by
            simpa [checkedStep, hz, ho] using h
          rw [← hout]
          funext k
          by_cases hk : item.1 = k
          · simp [uncheckedStep, hk, checkedMul_some hz, checkedMul_some ho]
          · simp [uncheckedStep, hk]

/-- The source-variable-major checked scan. -/
def checkedScanFrom {c : ℕ}
    (acc : Products c) : List (Fin c × (ℤ × ℤ)) → Option (Products c)
  | [] => some acc
  | item :: rest =>
      (checkedStep acc item).bind (fun next => checkedScanFrom next rest)

/-- Its corresponding unbounded left-to-right fold. -/
def uncheckedScanFrom {c : ℕ}
    (acc : Products c) (items : List (Fin c × (ℤ × ℤ))) : Products c :=
  items.foldl uncheckedStep acc

/-- Successful checked scans equal the unbounded left-to-right scan,
    with no arithmetic overflow hidden by later cancellation. -/
theorem checkedScanFrom_sound {c : ℕ}
    (acc : Products c) (items : List (Fin c × (ℤ × ℤ)))
    (result : Products c) (h : checkedScanFrom acc items = some result) :
    result = uncheckedScanFrom acc items := by
  induction items generalizing acc with
  | nil =>
      simp [checkedScanFrom, uncheckedScanFrom] at h ⊢
      exact h.symm
  | cons item rest ih =>
      cases hs : checkedStep acc item with
      | none =>
          simp [checkedScanFrom, hs] at h
      | some next =>
          have htail : checkedScanFrom next rest = some result := by
            simpa [checkedScanFrom, hs] using h
          calc
            result = uncheckedScanFrom next rest := ih next htail
            _ = uncheckedScanFrom acc (item :: rest) := by
              rw [checkedStep_sound acc item next hs]
              rfl

/-- The exact class-specific fiber product in an ordered item stream.
    Off-class items contribute one, and hence can be scanned without
    changing the class product. -/
def fiberProduct {c : ℕ}
    (items : List (Fin c × (ℤ × ℤ)))
    (k : Fin c) (bit : Bool) : ℤ :=
  (items.map (fun item =>
    if item.1 = k then
      if bit then item.2.2 else item.2.1
    else 1)).prod

def choose (pair : ℤ × ℤ) (bit : Bool) : ℤ :=
  if bit then pair.2 else pair.1

/-- The invariant of the vertex-major loop: each entry accumulates
    precisely the factors of its class, in input order. -/
theorem uncheckedScanFrom_fiber {c : ℕ}
    (acc : Products c) (items : List (Fin c × (ℤ × ℤ)))
    (k : Fin c) (bit : Bool) :
    choose ((uncheckedScanFrom acc items) k) bit =
      choose (acc k) bit * fiberProduct items k bit := by
  induction items generalizing acc with
  | nil =>
      simp [uncheckedScanFrom, fiberProduct]
  | cons item rest ih =>
      calc
        choose ((uncheckedScanFrom acc (item :: rest)) k) bit =
            choose ((uncheckedScanFrom (uncheckedStep acc item) rest) k) bit := rfl
        _ = choose ((uncheckedStep acc item) k) bit *
            fiberProduct rest k bit := ih (uncheckedStep acc item)
        _ = choose (acc k) bit * fiberProduct (item :: rest) k bit := by
          cases bit <;> by_cases hk : item.1 = k <;>
            simp [choose, uncheckedStep, fiberProduct, hk, mul_assoc]

/-- Checked summation and multiplication of the class products in
    increasing class-index order, matching Rust's second loop. -/
def checkedFinishFrom {c : ℕ}
    (products : Products c) (acc : ℤ) : List (Fin c) → Option ℤ
  | [] => some acc
  | k :: rest =>
      (checkedAdd (products k).1 (products k).2).bind (fun factor =>
        (checkedMul acc factor).bind (fun next =>
          checkedFinishFrom products next rest))

/-- Successful class-finalization computes the exact product of sums. -/
theorem checkedFinishFrom_sound {c : ℕ}
    (products : Products c) (acc : ℤ) (classes : List (Fin c))
    (value : ℤ) (h : checkedFinishFrom products acc classes = some value) :
    value = acc * (classes.map (fun k =>
      (products k).1 + (products k).2)).prod := by
  induction classes generalizing acc with
  | nil =>
      simp [checkedFinishFrom] at h
      simpa using h.symm
  | cons k rest ih =>
      cases ha : checkedAdd (products k).1 (products k).2 with
      | none =>
          simp [checkedFinishFrom, ha] at h
      | some factor =>
          cases hm : checkedMul acc factor with
          | none =>
              simp [checkedFinishFrom, ha, hm] at h
          | some next =>
              have htail : checkedFinishFrom products next rest = some value := by
                simpa [checkedFinishFrom, ha, hm] using h
              calc
                value =
                    next * (rest.map (fun j =>
                      (products j).1 + (products j).2)).prod :=
                    ih next htail
                _ = acc * ((k :: rest).map (fun j =>
                    (products j).1 + (products j).2)).prod := by
                  rw [checkedMul_some hm, checkedAdd_some ha]
                  simp only [List.map_cons, List.prod_cons]
                  ring

def initialProducts (c : ℕ) : Products c := fun _ => (1, 1)

/-- The two Rust loop phases, represented without any DSU pointer access. -/
def checkedClassFold {c : ℕ} (items : List (Fin c × (ℤ × ℤ))) :
    Option ℤ := do
  let products ← checkedScanFrom (initialProducts c) items
  checkedFinishFrom products 1 (List.finRange c)

/-- Full success implies exactly the product of the two fiber products
    for each class. This also handles c=0, with the empty product = 1. -/
theorem checkedClassFold_sound {c : ℕ}
    (items : List (Fin c × (ℤ × ℤ))) (value : ℤ)
    (h : checkedClassFold items = some value) :
    value = ((List.finRange c).map (fun k =>
      fiberProduct items k false + fiberProduct items k true)).prod := by
  cases hs : checkedScanFrom (initialProducts c) items with
  | none =>
      simp [checkedClassFold, hs] at h
  | some products =>
      have hf : checkedFinishFrom products 1 (List.finRange c) = some value := by
        simpa [checkedClassFold, hs] using h
      have hprod := checkedFinishFrom_sound products 1 (List.finRange c) value hf
      have hstate : products = uncheckedScanFrom (initialProducts c) items :=
        checkedScanFrom_sound (initialProducts c) items products hs
      have hclass (k : Fin c) :
          (products k).1 + (products k).2 =
            fiberProduct items k false + fiberProduct items k true := by
        rw [hstate]
        have hzero := uncheckedScanFrom_fiber (initialProducts c) items k false
        have hone := uncheckedScanFrom_fiber (initialProducts c) items k true
        have hzero' :
            (uncheckedScanFrom (initialProducts c) items k).1 =
              fiberProduct items k false := by
          simpa [choose, initialProducts] using hzero
        have hone' :
            (uncheckedScanFrom (initialProducts c) items k).2 =
              fiberProduct items k true := by
          simpa [choose, initialProducts] using hone
        rw [hzero', hone']
      simpa only [one_mul, hclass] using hprod

/-- Source-indexed stream in the same vertex order as the Rust zip loop. -/
def sourceItems {n c : ℕ}
    (label : Fin n → Fin c) (weights : Fin n → Bool → ℤ) :
    List (Fin c × (ℤ × ℤ)) :=
  (List.finRange n).map (fun i =>
    (label i, (weights i false, weights i true)))

/-- The fiber product over labelled items is exactly the product of
    the appropriate unary weights for that class. -/
theorem fiberProduct_sourceItems {n c : ℕ}
    (label : Fin n → Fin c)
    (weights : Fin n → Bool → ℤ)
    (k : Fin c) (bit : Bool) :
    fiberProduct (sourceItems label weights) k bit =
      ((List.finRange n).map (fun i =>
        if label i = k then weights i bit else 1)).prod := by
  cases bit <;>
    simp [fiberProduct, sourceItems, List.map_map, Function.comp_def]

#print axioms ACC.ComponentFoldCorrespondence.checkedStep_sound
#print axioms ACC.ComponentFoldCorrespondence.checkedScanFrom_sound
#print axioms ACC.ComponentFoldCorrespondence.uncheckedScanFrom_fiber
#print axioms ACC.ComponentFoldCorrespondence.checkedFinishFrom_sound
#print axioms ACC.ComponentFoldCorrespondence.checkedClassFold_sound
#print axioms ACC.ComponentFoldCorrespondence.fiberProduct_sourceItems

end ACC.ComponentFoldCorrespondence
