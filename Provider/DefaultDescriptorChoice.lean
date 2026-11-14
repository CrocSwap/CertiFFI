import TagCheckFrames.Auxiliary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open TagCheckFrames
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option profiler true
set_option profiler.threshold 1000
namespace ReleaseProfile.DefaultDescriptorChoice
#check "CURRENT_DECL descriptor source"
theorem create_gpr_preserves (operation : MemOp) (nontemporal unprivileged tagchecked : Bool) :
    Preserves (CreateAccDescGPR operation nontemporal unprivileged tagchecked) := by
  oracle_frame
#print axioms create_gpr_preserves
end ReleaseProfile.DefaultDescriptorChoice
