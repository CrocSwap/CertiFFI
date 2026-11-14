import DefaultHeapRunBase
import TranslateMem.WalkE17

/-! F21 (CertiFFI,): AccessLeaf from the catalogue deployment premises (provider analogue of
`TranslateMem.accessLeaf_of_dp`, which takes the E17General premises). Body-entry closed membership is
`dp.init.core.closed`, over `cmap = HeapV2E17.consumerMap`, which permits every declared data access. -/

open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft TranslateMem
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace ReleaseProfile.DefaultHeapF21

theorem accessLeaf_of_cdp {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {pins : HeapV2E17.Pins}
    {entry : NativeState} {budget : Nat} {catalogue : NativeMteTagCheck.ControlCatalogue} {capacity : Nat}
    {drawsBefore : Nat → Nat}
    (dp : ReleaseProfile.DefaultHeapRun.DeploymentPremises spec config rows mapping base pins entry budget catalogue
      capacity drawsBefore) :
    AccessLeaf pins mapping := by
  intro e he
  exact leaf_of_closed dp.init.core.closed (acc := dataAcc e.2.2.2.2) (aligned := true)
    (size := (e.2.2.2.1 : Int)) (Or.inl ⟨e, he, rfl, rfl, dataAcc_shape _⟩)

end ReleaseProfile.DefaultHeapF21

#print axioms ReleaseProfile.DefaultHeapF21.accessLeaf_of_cdp
