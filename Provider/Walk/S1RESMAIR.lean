import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1RESMAIR
/- Replace only the source's three literal pattern matches by explicit guards.
   The source feature reads and all attribute cases remain unchanged. -/
def action (attr : BitVec 8) : SailM Bool := do
  if ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb attr 7 4)) == 0#4) &&
      ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb attr 1 0)) == 1#2) then
    return !(← HaveFeatXS ())
  else if (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb attr 7 4)) == 0#4 then
    return (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb attr 1 0)) != 0#2
  else if attr = 64#8 then return !(← HaveFeatXS ())
  else if attr = 160#8 then return !(← HaveFeatXS ())
  else if attr = 240#8 then return !(← HaveMTE2Ext ())
  else return (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb attr 3 0)) == 0#4

theorem source_eq (attr : BitVec 8) : S1ConstrainUnpredictableRESMAIR attr true = action attr := by
  unfold S1ConstrainUnpredictableRESMAIR action
  simp only [↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · split <;> simp_all
      congr 1

drive_spec native, action_eq :
  fun (attr : BitVec 8) (s : SequentialState Regs oracleChoiceSource) => action attr s
theorem complete (attr : BitVec 8) (s : SequentialState Regs oracleChoiceSource) :
    S1ConstrainUnpredictableRESMAIR attr true s = native attr s := by
  rw [source_eq, action_eq]
attribute [step_summary] complete
#print axioms complete
end S1RESMAIR
