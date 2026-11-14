import Walk.S1WalkSuffixSource
import Walk.S1Normality
import Pilot.S1DecodeFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1CacheGuard
abbrev State := S1Normality.State

theorem disabled (d : BitVec 64) (fault : FaultRecord) (s : State)
    (h : (s.regs.bank_Bool .__tlb_enabled) = false) :
    S1WalkSuffixSource.cacheGuard 64 d fault s = .ok (.ok false) s := by
  change (EStateM.Result.ok (.ok
    (((s.regs.bank_Bool .__tlb_enabled) && (fault.statuscode == .Fault_None)) &&
      (S1DecodeFacts.bit d 10 == 1#1))) s :
      EStateM.Result (Sail.Error exception) State
        (Except (Sail.Error exception ⊕ (FaultRecord × AddressDescriptor × TTWState × BitVec 64)) Bool)) = .ok (.ok false) s
  rw [h]
  rfl
#print axioms disabled
end S1CacheGuard
