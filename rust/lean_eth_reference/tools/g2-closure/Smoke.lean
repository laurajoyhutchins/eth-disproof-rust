import G2Inventory

namespace InventorySmoke
axiom oracle : Nat
noncomputable def intermediate : Nat := oracle
noncomputable def originalRoot : Nat := intermediate
opaque sealed : Nat := 7
noncomputable def opaqueRoot : Nat := sealed
def ordinary (x : Nat) : Nat := x
end InventorySmoke

#eth_closure_inventory InventorySmoke.originalRoot
#eth_closure_inventory InventorySmoke.opaqueRoot
#eth_closure_inventory InventorySmoke.ordinary

-- The inventory is deterministic and deliberately reports bounded truncation.
-- Even a truncated observation must never become an ETH-ready certificate.
run_cmd do
  let first ← liftCoreM <| G2Inventory.inventory ``InventorySmoke.originalRoot
  let second ← liftCoreM <| G2Inventory.inventory ``InventorySmoke.originalRoot
  unless first.compress == second.compress do
    throwError "G2 closure inventory is nondeterministic"
  let bounded ← liftCoreM <| G2Inventory.inventory ``InventorySmoke.originalRoot 1
  let json := bounded.compress
  unless (json.splitOn "bounded-incomplete").length > 1 do
    throwError "bounded source inventory did not expose truncation"
  match bounded.getObjValAs? Bool "eth_ready" with
  | .ok false => pure ()
  | _ => throwError "a truncated closure was incorrectly marked ETH ready"
