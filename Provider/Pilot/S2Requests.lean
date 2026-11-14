import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2Requests
@[simp] theorem read_pa (acc : AccessDescriptor) (ti : Option TranslationInfo) (n : Nat)
    (va : BitVec 64) (pa : BitVec 56) : (read_request acc ti n va pa).pa = pa := rfl
@[simp] theorem write_pa (acc : AccessDescriptor) (ti : Option TranslationInfo) (n : Nat)
    (va : BitVec 64) (pa : BitVec 56) (data : BitVec (8 * n)) :
    (write_request acc ti n va pa data).pa = pa := rfl
end S2Requests
