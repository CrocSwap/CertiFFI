import Walk.S2MPAMCombine
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2MPAMCombinedFrame
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State MPAMinfo
def value : Result → MPAMinfo
  | .ok v _ => v
  | .error _ _ => {partid := 0#16, pmg := 0#8, mpam_sp := .PIdSpace_NonSecure}
def occ : Result → Std.ExtHashMap Nat Nat
  | .ok _ s => s.choiceOcc
  | .error _ s => s.choiceOcc
noncomputable def normal (el : BitVec 2) (pspace : PARTIDspaceType) (s : State) : Result :=
  .ok (value (S2MPAMCombine.native el pspace s))
    {s with choiceOcc := occ (S2MPAMCombine.native el pspace s)}
theorem packed (el : BitVec 2) (pspace : PARTIDspaceType) (s : State) :
    S2MPAMCombine.native el pspace s = normal el pspace s := by
  delta normal S2MPAMCombine.native
  s2_pack_partid
theorem complete (el : BitVec 2) (pspace : PARTIDspaceType) (s : State) :
    genMPAM el false false pspace s = normal el pspace s :=
  (S2MPAMCombine.complete el pspace s).trans (packed el pspace s)
attribute [-step_summary] S2MPAMCombine.complete
attribute [step_summary] complete
#print axioms complete
end S2MPAMCombinedFrame
