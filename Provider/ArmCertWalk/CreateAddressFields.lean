import ArmCertWalk.TranslateFinishCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
/-- Recover the actual address constructor's fault field from its PAST call. -/
theorem create_output_fault_of_call (va : BitVec 64) (pa : FullAddress)
    (attrs : MemoryAttributes) (state : State) (address : AddressDescriptor) (other : State)
    (call : CreateAddressDescriptor va pa attrs state = .ok address other) :
    address.fault.statuscode = .Fault_None := by
  rw [create_output_eq] at call
  delta create_output_native at call
  cases call
  rfl
#print axioms create_output_fault_of_call
end ArmCertWalk
