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
