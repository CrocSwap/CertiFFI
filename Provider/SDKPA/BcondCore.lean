import BranchObs.Bcond
import RtBr.BrToRwPA
import Crypto.BranchDefs
import Bridge.CruxNonProj
import Crypto.Tac
import Crypto.Tac2
import Bridge.StepM
import Bridge.CruxNonProj
import BR8.BCond
import Crypto.BcondDecode
import SDKPA.BranchPins
import SDKPA.BranchPinsF
import Crypto.Tac
import Crypto.Tac2
import Crypto.BrSimp
import Pilot.ObservationSimp
import Bridge.StepM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace Crypto.BcondCore
open Crypto.BcondDec

set_option maxHeartbeats 40000000 in
theorem bcond_obs_pa (real : Type) [Sail.SailReal real] (cond : BitVec 4) (imm19 : BitVec 19) (S0 : SequentialState Regs oracleChoiceSource)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_BCondH.native real cond imm19 (bcondWord imm19 cond) (-1) S0 = .ok () t ∧ BrFrame S0 t ∧
      ((bcondC cond S0.regs ∧ t.regs.__BranchTaken = true ∧ t.regs._PC = S0.regs._PC + sign_extend (imm19 ++ 0#2) 64 ∧ t.regs.Branchtypetaken ≠ BranchType.BranchType_RESET) ∨
       (¬ bcondC cond S0.regs ∧ t.regs.__BranchTaken = S0.regs.__BranchTaken ∧ t.regs._PC = S0.regs._PC ∧ t.regs.Branchtypetaken = S0.regs.Branchtypetaken)) :=
  ReleaseProfile.BcondAction.bcond_obs_current real cond imm19 S0 { hBP with } hVHE hlow
#print axioms bcond_obs_pa
end Crypto.BcondCore
