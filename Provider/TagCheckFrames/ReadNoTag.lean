import TagCheckFrames.Auxiliary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open TagCheckFrames
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace TagCheckFrames
theorem single_read_no_tag (address : BitVec 64) (size : Nat) (acc : AccessDescriptor)
    (aligned ispair : Bool) (tag : acc.tagchecked = false) :
    Preserves (AArch64_MemSingle_read__1 address size acc aligned ispair) := by
  unfold AArch64_MemSingle_read__1
  simp only [tag, Bool.and_false, bind_assoc, pure_bind, Bool.false_eq_true, ite_false]
  oracle_frame
#print axioms single_read_no_tag
theorem read_no_tag (address : BitVec 64) (size : Nat) (acc : AccessDescriptor)
    (aligned : Bool) (tag : acc.tagchecked = false) :
    Preserves (AArch64_MemSingle_read address size acc aligned) := by
  unfold AArch64_MemSingle_read
  apply map_frame
  exact single_read_no_tag address size acc aligned false tag

#print axioms read_no_tag
end TagCheckFrames
