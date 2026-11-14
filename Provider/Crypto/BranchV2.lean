import Crypto.BcondBridge
import Crypto.CbzBridge
import Crypto.BlBridge
import Crypto.RetBridge
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.BoundaryV2
open ArmCert.Premises.TranslationAgreesV1
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.BranchV2LNSym.
namespace Crypto.BranchV2

/-- BranchPins v2 (a design decision + 71): driver's 86-pin GB10 EL2&0 block, plus FEAT_VHE (FeatureImpl[54], the
 BEPins.vhe bit) and FEAT_GCS absent. -/
structure BranchPinsV2 (s : NativeState) : Prop where
  base : Crypto.BranchPins s
  vhe : s.regs.FeatureImpl[54] = true
  gcs : s.regs.FeatureImpl[245] = false

end Crypto.BranchV2

