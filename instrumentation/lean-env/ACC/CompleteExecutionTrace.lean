import Mathlib
import ACC.ArrayFinishSimulation
import ACC.ArithmeticReceipts

/-!
# Source-bound, ordered complete contraction traces

A trace is not an unordered bag of individually correct arithmetic receipts.
The checker independently reconstructs *every expected call in order*, from
the supplied source weights and certified class labels. It checks the
observed operand words, operation kinds, successful values, and first
overflow refusal, without consuming an untrusted intermediate array.

For a successful result, a second independent check re-executes the already
proved Lean integer-array reference. The resulting theorem connects the
accepted finite run to the exact source-edge-constrained weighted count.

This is finite, input-bound translation validation. It does not prove the
Rust emitter captured real hardware instructions or that the Rust guard
loop implements the Lean indexed guard for all inputs.
-/

namespace ACC.CompleteExecutionTrace

open ACC.ArithmeticReceipts
open ACC.CheckedI128BitVec
open ACC.IndexedRankedCertificate
open ACC.ArrayFinishSimulation
open ACC.ComponentFoldCorrespondence

abbrev WordPair := Word × Word

/-- The vertex stream used by Rust's component array scan. -/
def wordItems {n c : ℕ}
    (label : Fin n → Fin c) (weight : Fin n → Bool → Word) :
    List (Fin c × WordPair) :=
  (List.finRange n).map fun i =>
    (label i, (weight i false, weight i true))

/-- Model-generated receipts never trust an external reported result. -/
def recorded (kind : Kind) (left right : Word) : Receipt :=
  { kind := kind, left := left, right := right
    observed := expected kind left right }

/-- The atomic per-vertex update logs both multiplications only when the
    first succeeds. No array slot changes until both have succeeded. -/
def scanTrace {c : ℕ} (products : Array WordPair) :
    List (Fin c × WordPair) → List Receipt × Option (Array WordPair)
  | [] => ([], some products)
  | item :: rest =>
      match products[item.1.val]? with
      | none => ([], none)
      | some old =>
          let first := recorded .mul old.1 item.2.1
          match first.observed with
          | none => ([first], none)
          | some zero =>
              let second := recorded .mul old.2 item.2.2
              match second.observed with
              | none => ([first, second], none)
              | some one =>
                  let (later, result) :=
                    scanTrace (products.setIfInBounds item.1.val (zero, one)) rest
                  (first :: second :: later, result)

/-- Exactly one checked addition followed by one checked multiplication for
    each class, stopping at the first refusing operation. -/
def finishTrace {c : ℕ} (products : Array WordPair)
    (acc : Word) : List (Fin c) → List Receipt × Option Word
  | [] => ([], some acc)
  | k :: rest =>
      match products[k.val]? with
      | none => ([], none)
      | some pair =>
          let addition := recorded .add pair.1 pair.2
          match addition.observed with
          | none => ([addition], none)
          | some factor =>
              let multiplication := recorded .mul acc factor
              match multiplication.observed with
              | none => ([addition, multiplication], none)
              | some next =>
                  let (later, result) := finishTrace products next rest
                  (addition :: multiplication :: later, result)

/-- The complete deterministic arithmetic schedule, including refusal.
    This reconstructs the expected trace independently of Rust's emitter. -/
def expectedExecution {n c : ℕ}
    (label : Fin n → Fin c) (weight : Fin n → Bool → Word) :
    List Receipt × Option Word :=
  let one : Word := BitVec.ofInt 128 1
  let (scan, finalProducts) :=
    scanTrace (Array.replicate c (one, one)) (wordItems label weight)
  match finalProducts with
  | none => (scan, none)
  | some products =>
      let (finish, result) := finishTrace products one (List.finRange c)
      (scan ++ finish, result)

/-- Both the full trace and the final answer are *untrusted data*.
    The indexed guard is checked again from source edges, and the complete
    integer array interpreter is independently re-run. On failure the latter
    also checks precise refusal, but no equality-to-count is then claimed. -/
def checkComplete {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word) : Bool :=
  (checkIndexed edges label root sourceIndex rank && checkTrace trace) &&
  (decide (expectedExecution label weight = (trace, reported)) &&
   decide (checkedArrayContraction
     (sourceItems label (fun i bit => (weight i bit).toInt)) =
       reported.map BitVec.toInt))

/-- An accepted witness is the whole reconstructed schedule. In particular
    dropping, reordering, or appending any operation changes the answer
    of the checker unless it is the *same* trace. -/
theorem checkComplete_schedule {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ) (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word)
    (h : checkComplete edges label root sourceIndex rank
      weight trace reported = true) :
    expectedExecution label weight = (trace, reported) := by
  simp only [checkComplete, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

/-- Every accepted reported operation is valid against the signed-word
    specification, including all overflow refusals. -/
theorem checkComplete_receipts {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ) (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word)
    (h : checkComplete edges label root sourceIndex rank
      weight trace reported = true) :
    ∀ receipt ∈ trace,
      receipt.observed =
        expected receipt.kind receipt.left receipt.right := by
  simp only [checkComplete, Bool.and_eq_true, decide_eq_true_eq] at h
  exact checkTrace_sound trace h.1.2

/-- Kernel-level finite-execution soundness for a successful witness:
    the accepted reported integer is the *literal source-edge count*.
    The proof consumes neither the Rust emitter nor its claimed result as
    an axiom: the typed edge guard and the full checked array interpreter
    must both accept the data. -/
theorem checkComplete_success_sound {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ) (weight : Fin n → Bool → Word)
    (trace : List Receipt) (value : Word)
    (h : checkComplete edges label root sourceIndex rank
      weight trace (some value) = true) :
    value.toInt =
      (∑ x : {x : Fin n → Bool // ∀ e ∈ edges, x e.1 = x e.2},
        ∏ i : Fin n, (weight i (x.1 i)).toInt) := by
  simp only [checkComplete, Bool.and_eq_true, decide_eq_true_eq] at h
  exact checkedArrayContraction_source_edges
    edges label root sourceIndex rank
    (fun i bit => (weight i bit).toInt) value.toInt
    h.1.1 (by simpa using h.2.2)

/-- Zero vertices and zero classes require no reported operations. -/
example :
    expectedExecution (n := 0) (c := 0)
      (fun i => i.elim0) (fun i _ => i.elim0) =
        ([], some (BitVec.ofInt 128 1)) := by decide

#print axioms ACC.CompleteExecutionTrace.checkComplete_schedule
#print axioms ACC.CompleteExecutionTrace.checkComplete_receipts
#print axioms ACC.CompleteExecutionTrace.checkComplete_success_sound

end ACC.CompleteExecutionTrace
