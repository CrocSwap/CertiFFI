-- The actual ifetch memRead appended by MemSingle_read is an Isla V2 traffic record.
import ArmCertWalk.WalkTrafficRecords
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace ArmCertWalk
open ArmCertCT.Native

theorem ifetch_read_record (pa va : Nat) :
    V2.trafficRec (.memRead pa 4 (some va) (AK_ifetch ()) false : Event) = some ⟨pa, 4, .ifetch⟩ := rfl

#print axioms ifetch_read_record
end ArmCertWalk
