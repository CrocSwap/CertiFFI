import BranchObs.Cbz
-- d193 (certiffi, condition: fresh module, not an SDKPA overlay): Sail-only CBZ core. Crypto.CbzCore.cbz_obs_pa states the branch condition through
-- LNSym (condition_holds on projectM m S0 p) and splits on it via Crypto.CbzLink.cbz_link; cbz_obs_sail states the
-- same facts with the condition as cbz_link's Sail side (`cbzCond`), so the proof is the original one minus the link.
-- Consumers needing the branch outcome (NativeEntryBodyBranch.Cbz.run / CbzExtra) drop `m p`; frame-only consumers use
-- RtBr.CbzFrame.cbz_frame_pa_any.
import RtBr.BrToRwPA
import BR8.CBZ
import Crypto.CbzDecode
import SDKPA.BranchPins
import SDKPA.BranchPinsF
import Crypto.Tac
import Crypto.Tac2
import Crypto.BrSimp
import Crypto.BranchDefs
import Crypto.BrToRw
import BR8.BCond
import Crypto.BcondDecode
import Crypto.BranchPins
import Crypto.BranchPinsF
import Crypto.BrSimp
import Pilot.ObservationSimp
import Bridge.CruxNonProj
import Crypto.Tac
import Crypto.Tac2
import Bridge.StepM
import Pilot.ObservationSimp
import Bridge.StepM
import Bridge.Proj
import BridgeV2.BoundaryV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace Crypto.CbzFrame
open Crypto.CbzDec Crypto.BcondCore
open ArmBridge.Draft

/-- The CBZ/CBNZ branch condition on the Sail state (cbz_link's right-hand side). -/
def cbzCond (s : NativeState) (sf op : BitVec 1) (Rt : BitVec 5) : Prop :=
  IsZero (if ((Rt.toNat : Nat) : Int) = 31 then (Zeros : BitVec (Sail.Int.toNatChecked (if sf = 1#1 then 64 else 32)))
      else BitVec.castWidth (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rt.toNat).val]
        (Sail.Int.toNatChecked (↑(Sail.Int.toNatChecked (if sf = 1#1 then 64 else 32)) - 1)) 0)) = (op == 0#1)

set_option maxHeartbeats 40000000 in
theorem cbz_obs_sail (real : Type) [Sail.SailReal real]
    (Rt : BitVec 5) (imm19 : BitVec 19) (op sf : BitVec 1) (S0 : NativeState)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_CBZ.native real Rt imm19 op sf (cbzWord sf op imm19 Rt) (-1) S0 = .ok () t ∧ BrFrame S0 t ∧
      ((cbzCond S0 sf op Rt ∧
          t.regs.__BranchTaken = true ∧ t.regs._PC = S0.regs._PC + sign_extend (imm19 ++ 0#2) 64 ∧ t.regs.Branchtypetaken ≠ BranchType.BranchType_RESET) ∨
       (¬ cbzCond S0 sf op Rt ∧
          t.regs.__BranchTaken = S0.regs.__BranchTaken ∧ t.regs._PC = S0.regs._PC ∧ t.regs.Branchtypetaken = S0.regs.Branchtypetaken)) := by
  exact ReleaseProfile.HeapCbzAction.cbz_obs_sail real Rt imm19 op sf S0 { hBP with } hVHE hlow

#print axioms cbz_obs_sail

end Crypto.CbzFrame
