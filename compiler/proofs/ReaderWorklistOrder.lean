import Lean

/-!
# Eager constructor worklist versus recursive release

The pinned C++ constructor destructor visits fields left-to-right but queues
last-owned children using push_back and pop_back. Its *destruction order* is
therefore LIFO, not the same order as a recursive left-to-right traversal.

This model is intentionally restricted to finite binary constructor trees.
The retained constructor is a frontier whose independent RC prevents the
destructor from visiting it or its descendants. Identity uniqueness and
correctness of the actual C++ implementation remain separate obligations.

The theorems are structural mathematical facts, not a compiler or C++ runtime
refinement theorem. The source-pinned C++ diagnostic's concrete event traces
are independently audited by scripts/check-internal-worklist.py.
-/

namespace ReaderWorklistOrder

inductive Tree where
  | leaf (id : Nat)
  | fork (id : Nat) (left right : Tree)
  | retained (subtree : Tree)
  deriving Repr, DecidableEq

/-- Logical recursive release order: process the left child first. -/
def recursiveVisits : Tree → List Nat
  | .leaf id => [id]
  | .fork id left right =>
      id :: (recursiveVisits left ++ recursiveVisits right)
  | .retained _ => []

/-- Eager worklist visits last-enqueued children first. The two children
are inspected left-to-right, hence the right child is processed first.
The retained frontier is never visited. -/
def worklistVisits : Tree → List Nat
  | .leaf id => [id]
  | .fork id left right =>
      id :: (worklistVisits right ++ worklistVisits left)
  | .retained _ => []

/-- The worklist and recursive traversals visit exactly the same identities
as sets, even though their order may differ. If IDs are unique, this also
identifies the set of constructors released by either semantics. -/
theorem same_visited_identities (tree : Tree) (id : Nat) :
    id ∈ worklistVisits tree ↔ id ∈ recursiveVisits tree := by
  induction tree with
  | leaf n =>
      simp [worklistVisits, recursiveVisits]
  | fork n left right ihLeft ihRight =>
      simp [worklistVisits, recursiveVisits, ihLeft, ihRight,
        or_comm, or_left_comm, or_assoc]
  | retained subtree ih =>
      simp [worklistVisits, recursiveVisits]

/-- No constructor visit is lost or invented when replacing the
depth-first left-to-right schedule with LIFO worklist scheduling. -/
theorem same_number_of_visits (tree : Tree) :
    (worklistVisits tree).length = (recursiveVisits tree).length := by
  induction tree with
  | leaf n =>
      simp [worklistVisits, recursiveVisits]
  | fork n left right ihLeft ihRight =>
      simp [worklistVisits, recursiveVisits, ihLeft, ihRight,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | retained subtree ih =>
      simp [worklistVisits, recursiveVisits]

/-- A retained owner prevents either release mechanism from visiting the
protected subtree, whatever its shape. -/
theorem retained_subtree_is_a_frontier (subtree : Tree) :
    worklistVisits (.retained subtree) = [] ∧
    recursiveVisits (.retained subtree) = [] := by
  simp [worklistVisits, recursiveVisits]

def forkWitness : Tree :=
  .fork 0 (.fork 1 (.leaf 2) (.leaf 3)) (.leaf 4)

def retainedForkWitness : Tree :=
  .fork 0 (.fork 1 (.leaf 2) (.leaf 3)) (.retained (.leaf 4))

theorem fork_lifo_visitation :
    worklistVisits forkWitness = [0, 4, 1, 3, 2] := by decide

theorem fork_recursive_visitation :
    recursiveVisits forkWitness = [0, 1, 2, 3, 4] := by decide

/-- Equality of final effects cannot be used to infer equality of
destructor visitation order. -/
theorem same_released_nodes_but_different_order :
    worklistVisits forkWitness ≠ recursiveVisits forkWitness := by decide

theorem retained_right_branch_stops :
    worklistVisits retainedForkWitness = [0, 1, 3, 2] ∧
    recursiveVisits retainedForkWitness = [0, 1, 2, 3] := by decide

end ReaderWorklistOrder

#print axioms ReaderWorklistOrder.same_visited_identities
#print axioms ReaderWorklistOrder.same_number_of_visits
#print axioms ReaderWorklistOrder.retained_subtree_is_a_frontier
#print axioms ReaderWorklistOrder.fork_lifo_visitation
#print axioms ReaderWorklistOrder.same_released_nodes_but_different_order
#print axioms ReaderWorklistOrder.retained_right_branch_stops
