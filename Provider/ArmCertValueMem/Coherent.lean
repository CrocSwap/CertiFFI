-- Memory: the generic region coherence hypothesis of step_agrees / run_agrees, discharged.
import HeapV2StepCerts.RegBindCore
import ArmCertValue.Bytes
import ArmCertValueMem.Region
set_option autoImplicit false
namespace ArmCertValue.MemRegion
open ArmCertValue

/-- RegionCoherent holds for every deployment mapping and pin valuation. -/
theorem regionCoherent (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) : RegionCoherent mapping pinv :=
  fun s r w v h k hk => (regionWord_bytes mapping pinv s r w v).1 h k hk

#print axioms regionCoherent
end ArmCertValue.MemRegion
