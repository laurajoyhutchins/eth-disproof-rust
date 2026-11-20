import Mathlib
import ACC.ArrayScanSimulation

/-!
# Checked array finalization and complete source-edge contraction

The vertex-major array scan has already been simulated by the
function-valued checked accumulator. The remaining concrete-shaped
finalization reads each component's two products *in class order*, adds
them with a signed-i128 range check, then multiplies the running answer
with another checked operation.

The array-to-function representation relation is sufficient for an
*exact* equality between the two Option-valued finalization interpreters.
This includes failure, rather than just equality after successful runs.
The resulting complete array-model theorem then composes with the
previous certified equality-edge counting result.

These statements are about Lean interpreters. They are not a translation
or proof of compiled Rust, CPU arithmetic, allocator behavior, or cost.
-/

namespace ACC.ArrayFinishSimulation

open ACC.ArrayStepSimulation
open ACC.ArrayScanSimulation
open ACC.ComponentFoldCorrespondence
open ACC.CheckedComponentArithmetic

/-- One immutable array read per class, followed by checked addition and
    multiplication. The accumulator and class iteration order match the
    source-level Rust finalization loop. -/
def checkedArrayFinishFrom {c : ℕ}
    (products : Array (ℤ × ℤ)) (acc : ℤ) :
    List (Fin c) → Option ℤ
  | [] => some acc
  | k :: rest => do
      let pair ← products[k.val]?
      let sum ← checkedAdd pair.1 pair.2
      let next ← checkedMul acc sum
      checkedArrayFinishFrom products next rest

/-- Stronger than success-only refinement: if the array represents the
    functional state, the concrete-shaped and mathematical finalizations
    return the exact same Option, including overflow refusal. -/
theorem checkedArrayFinishFrom_eq {c : ℕ}
    (products : Array (ℤ × ℤ)) (state : Products c)
    (hrep : Represents products state)
    (acc : ℤ) (classes : List (Fin c)) :
    checkedArrayFinishFrom products acc classes =
      checkedFinishFrom state acc classes := by
  induction classes generalizing acc with
  | nil =>
      rfl
  | cons k rest ih =>
      simp [checkedArrayFinishFrom, checkedFinishFrom, hrep.2 k, ih]

/-- A successful immutable array finalization has the exact mathematical
    product-of-component-sums value, with no hidden overflow. -/
theorem checkedArrayFinishFrom_sound {c : ℕ}
    (products : Array (ℤ × ℤ)) (state : Products c)
    (hrep : Represents products state)
    (acc : ℤ) (classes : List (Fin c)) (value : ℤ)
    (h : checkedArrayFinishFrom products acc classes = some value) :
    value = acc * (classes.map (fun k =>
      (state k).1 + (state k).2)).prod := by
  have hstate : checkedFinishFrom state acc classes = some value := by
    rw [← checkedArrayFinishFrom_eq products state hrep acc classes]
    exact h
  exact checkedFinishFrom_sound state acc classes value hstate

/-- The complete two-pass array interpreter, with the actual all-ones
    initialization and class-major finalization. -/
def checkedArrayContraction {c : ℕ}
    (items : List (Fin c × (ℤ × ℤ))) : Option ℤ := do
  let products ← checkedArrayScanFrom (Array.replicate c (1, 1)) items
  checkedArrayFinishFrom products 1 (List.finRange c)

/-- If the complete array calculation succeeds, so does the previously
    proven function-valued checked fold, with precisely the same result. -/
theorem checkedArrayContraction_refines {c : ℕ}
    (items : List (Fin c × (ℤ × ℤ))) (value : ℤ)
    (h : checkedArrayContraction items = some value) :
    checkedClassFold items = some value := by
  cases hscan :
      checkedArrayScanFrom (Array.replicate c (1, 1)) items with
  | none =>
      simp [checkedArrayContraction, hscan] at h
  | some products =>
      have hfinish :
          checkedArrayFinishFrom products 1 (List.finRange c) = some value := by
        simpa [checkedArrayContraction, hscan] using h
      obtain ⟨state, hstate, hrep⟩ :=
        checkedArrayScan_initial_refines items products hscan
      have hcheckedFinish :
          checkedFinishFrom state 1 (List.finRange c) = some value := by
        rw [← checkedArrayFinishFrom_eq products state hrep 1 (List.finRange c)]
        exact hfinish
      simp [checkedClassFold, hstate, hcheckedFinish]

/-- Kernel-level end-to-end conditional correctness of the *Lean array
    model*: given a source-edge indexed certificate and successful checked
    array contraction, the returned integer is the original weighted
    equality-edge Boolean sum, not an assumed per-class oracle.

    This does not prove the compiled Rust verifier/scan/finalization. -/
theorem checkedArrayContraction_source_edges {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c)
    (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weights : Fin n → Bool → ℤ)
    (value : ℤ)
    (hcert : ACC.IndexedRankedCertificate.checkIndexed
      edges label root sourceIndex rank = true)
    (hresult :
      checkedArrayContraction (sourceItems label weights) = some value) :
    value =
      (∑ x : {x : Fin n → Bool // ∀ e ∈ edges, x e.1 = x e.2},
        ∏ i : Fin n, weights i (x.1 i)) := by
  exact checkedClassFold_source_edges
    edges label root sourceIndex rank weights value hcert
    (checkedArrayContraction_refines (sourceItems label weights) value hresult)

/-- No classes, no variables: the initial empty array yields one. -/
example :
    checkedArrayContraction
      ([] : List (Fin 0 × (ℤ × ℤ))) = some 1 := by decide

/-- An empty class has two possible weights, each empty product one. -/
example :
    checkedArrayContraction
      ([] : List (Fin 1 × (ℤ × ℤ))) = some 2 := by decide

/-- The checked finalizer may reject even when the mathematical sum
    would later be multiplied by zero. Refusal is not a wrong count. -/
example :
    checkedArrayFinishFrom
      (#[(2 ^ 127 - 1 : ℤ, 1), (0, 0)])
      1 ([⟨0, by decide⟩, ⟨1, by decide⟩] : List (Fin 2)) = none := by decide

#print axioms ACC.ArrayFinishSimulation.checkedArrayFinishFrom_eq
#print axioms ACC.ArrayFinishSimulation.checkedArrayFinishFrom_sound
#print axioms ACC.ArrayFinishSimulation.checkedArrayContraction_refines
#print axioms ACC.ArrayFinishSimulation.checkedArrayContraction_source_edges

end ACC.ArrayFinishSimulation
