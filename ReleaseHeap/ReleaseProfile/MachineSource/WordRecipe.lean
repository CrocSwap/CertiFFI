import ReleaseProfile.MachineSource.Recipe
import Init.Data.BitVec.Lemmas
import Init.Data.List.OfFn

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024

namespace ReleaseProfile.MachineSource.WordRecipe

/-- Each source bit is declared, symbolic, or an explicit caller slot. -/
abbrev Plan (width : Nat) := Fin width → Slot Bool

#check "CURRENT_DECL WordRecipe.assemble"
/-- A registered typed encoder. No zero word or previous register state supplies missing bits. -/
def assemble {width : Nat} (bits : Fin width → Bool) : BitVec width :=
  (BitVec.ofBoolListLE (List.ofFn bits)).cast List.length_ofFn

theorem assemble_bit {width : Nat} (bits : Fin width → Bool) (index : Fin width) :
    (assemble bits).getLsbD index.val = bits index := by
  simp only [assemble, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, index.isLt]

def evaluate {width : Nat} (plan : Plan width)
    (unknowns : UnknownValues plan) (caller : CallerValues plan) : BitVec width :=
  assemble (interpret plan unknowns caller)

theorem bit_exact {width : Nat} (plan : Plan width)
    (unknowns : UnknownValues plan) (caller : CallerValues plan) (index : Fin width) :
    (evaluate plan unknowns caller).getLsbD index.val =
      interpret plan unknowns caller index :=
  assemble_bit _ index

theorem declared_bit {width : Nat} (plan : Plan width)
    (unknowns : UnknownValues plan) (caller : CallerValues plan)
    (index : Fin width) (expected : Bool) (authority : AuthorityRef)
    (record : plan index = .literal expected authority) :
    (evaluate plan unknowns caller).getLsbD index.val = expected := by
  exact (bit_exact plan unknowns caller index).trans
    (interpret_literal plan unknowns caller index expected authority record)

theorem unresolved_bit {width : Nat} (plan : Plan width)
    (unknowns : UnknownValues plan) (caller : CallerValues plan)
    (index : Fin width) (symbolKey : String)
    (record : plan index = .unresolved symbolKey) :
    (evaluate plan unknowns caller).getLsbD index.val =
      unknowns index (by rw [record]; rfl) := by
  exact (bit_exact plan unknowns caller index).trans
    (interpret_unknown plan unknowns caller index symbolKey record)

theorem caller_bit {width : Nat} (plan : Plan width)
    (unknowns : UnknownValues plan) (caller : CallerValues plan)
    (index : Fin width) (slotKey : String)
    (record : plan index = .caller slotKey) :
    (evaluate plan unknowns caller).getLsbD index.val =
      caller index (by rw [record]; rfl) := by
  exact (bit_exact plan unknowns caller index).trans
    (interpret_caller plan unknowns caller index slotKey record)

end ReleaseProfile.MachineSource.WordRecipe

#print axioms ReleaseProfile.MachineSource.WordRecipe.assemble_bit
#print axioms ReleaseProfile.MachineSource.WordRecipe.bit_exact
#print axioms ReleaseProfile.MachineSource.WordRecipe.declared_bit
#print axioms ReleaseProfile.MachineSource.WordRecipe.unresolved_bit
#print axioms ReleaseProfile.MachineSource.WordRecipe.caller_bit
