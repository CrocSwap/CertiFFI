import SDKPA.BranchPins
import Crypto.BranchV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace Crypto.BranchV2
open ArmBridge.Draft ArmBridge.DraftM ArmBridge.Boundary ArmBridge.BoundaryV2
open ArmCert.Premises.TranslationAgreesV1

/-- BranchPinsPA v2 (a design decision + 71): driver's 86-pin GB10 EL2&0 block, plus FEAT_VHE (FeatureImpl[54], the
 BEPins.vhe bit) and FEAT_GCS absent. -/
structure BranchPinsV2PA (s : NativeState) : Prop where
  base : Crypto.BranchPinsPA s
  vhe : s.regs.FeatureImpl[54] = true
  gcs : s.regs.FeatureImpl[245] = false


theorem BranchPinsV2.toPA {s : NativeState} (h : BranchPinsV2 s) : BranchPinsV2PA s :=
  { base := h.base.toPA, vhe := h.vhe, gcs := h.gcs }

end Crypto.BranchV2
