-- CallerControls at any ChainInv v3 state. Everything but SCR_EL3.GCSEn
-- follows from ChainInv3's StepPins / BranchPinsV2PA; that one bit is the CallerResidue v4 field.
import RtBl.BlStepV3
open Sail ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace RtBl.CallerInv
open NativeEntryCallerParts ArmBridge.CruxGenGuarded.ChainInvV3

/-- The one CallerControls bit ChainInv3 does not carry (FEAT_GCS is absent: BranchPinsV2PA.gcs). -/
def CallerResidue (x : NativeState) : Prop :=
  _get_SCR_EL3_Type_GCSEn (x.regs.bank_BitVec_64 .SCR_EL3) = 0#1

/-- CallerControls from the step pins and branch pins plus the residue. -/
theorem callerControls_of_pins {x : NativeState} (pins : StepPins x) (bp : Crypto.BranchV2.BranchPinsV2PA x)
    (res : CallerResidue x) : CallerControls x where
  f4 := pins.f4
  f2 := bp.base.hFeature_AA32EL2
  f3 := bp.base.hFeature_AA32EL3
  f6 := bp.base.hFeature_AA64EL2
  f7 := bp.base.hFeature_AA64EL3
  rme := pins.rme
  vhe := by have h := bp.vhe; simpa [getElem!_pos] using h
  brbe := bp.base.hFeature_BRBE
  el := pins.el
  nrw := pins.nrw
  e2h := bp.base.hE2H
  tge := bp.base.hTGE
  ns := bp.base.hSCR_NS
  pmb := bp.base.hPMB_E
  spe := pins.spe
  pmbs := pins.pmbs
  nspb := bp.base.hNSPB
  nspbe := bp.base.hNSPBE
  gcsEn := res

theorem callerControls_of_inv3 {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    {config : ArmCertWalk.AttributeConfig} {rows : List ArmCert.Translate.Model.PermissionRow}
    {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word} {base : BitVec 64}
    {offset : Nat → BitVec 64} {budget : Nat} {p : ArmCert.Translate.Model.HeapV2E17.Pins} {k : Nat} {x : NativeState}
    (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (res : CallerResidue x) : CallerControls x :=
  callerControls_of_pins inv.v2.v1.pins inv.v2.branch res

/-- The residue's carry: any step that keeps SCR_EL3. -/
theorem residue_carry {x fin : NativeState}
    (h : fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3)
    (res : CallerResidue x) : CallerResidue fin := by
  unfold CallerResidue; rw [h]; exact res

#print axioms callerControls_of_pins
#print axioms callerControls_of_inv3
#print axioms residue_carry
end RtBl.CallerInv
