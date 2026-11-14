import DefaultHeapNormal
import ArmCert.HookQuiet.V0.Predicate

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace ReleaseProfile.HeapFinalLeaf

theorem security_of_noRME (r : Regs) (noRME : r.FeatureImpl[232]! = false) :
    ArmCert.HookQuiet.V0.feature r .FEAT_RME = false ∨
    _get_SCR_EL3_Type_NSE (ArmCert.HookQuiet.V0.reg64 r .SCR_EL3) = 0#1 ∨
      ArmCert.HookQuiet.V0.effectiveNS r = 1#1 := by
  left
  simpa [ArmCert.HookQuiet.V0.feature, num_of_Feature] using noRME

theorem guard_of_fields {a b : TranslateGuardView}
    (tbi : a.tbi = b.tbi) (tbid : a.tbid = b.tbid)
    (nfd : a.nfd = b.nfd) (e0pd : a.e0pd = b.e0pd) : a = b := by
  cases a
  cases b
  cases tbi
  cases tbid
  cases nfd
  cases e0pd
  rfl

#print axioms security_of_noRME
#print axioms guard_of_fields
end ReleaseProfile.HeapFinalLeaf
