import BranchObs.Cbz
import RtBr.BrToRwPA
import BR8.CBZ
import SDKPA.BranchPins
import RtBr.CbzCond
import Crypto.BranchDefs
import Bridge.CruxNonProj
import Crypto.Tac
import Crypto.Tac2
import Bridge.StepM
import SDKPA.BranchPinsF
import Crypto.BrSimp
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
set_option autoImplicit false
namespace RtBr.CbzFrame
open Crypto.BcondCore
set_option maxHeartbeats 40000000 in
theorem cbz_frame_pa (real : Type) [Sail.SailReal real] (Rt : BitVec 5) (imm19 : BitVec 19) (opc : BitVec 32)
    (S0 : SequentialState Regs oracleChoiceSource) (hRt : ¬ (Rt.toNat : Int) = 31)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_CBZ.native real Rt imm19 0#1 1#1 opc (-1) S0 = .ok () t ∧ Crypto.BcondCore.BrFrame S0 t := by
  obtain ⟨t, h, f, -⟩ := ReleaseProfile.HeapCbzAction.cbz_obs_sail real Rt imm19 0#1 1#1 S0 { hBP with } hVHE hlow
  exact ⟨t, h, f⟩

set_option maxHeartbeats 40000000 in
theorem cbz_frame_pa31 (real : Type) [Sail.SailReal real] (imm19 : BitVec 19) (opc : BitVec 32)
    (S0 : SequentialState Regs oracleChoiceSource) 
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_CBZ.native real 31#5 imm19 0#1 1#1 opc (-1) S0 = .ok () t ∧ Crypto.BcondCore.BrFrame S0 t := by
  obtain ⟨t, h, f, -⟩ := ReleaseProfile.HeapCbzAction.cbz_obs_sail real 31#5 imm19 0#1 1#1 S0 { hBP with } hVHE hlow
  exact ⟨t, h, f⟩

theorem cbz_frame_pa_any (real : Type) [Sail.SailReal real] (Rt : BitVec 5) (imm19 : BitVec 19) (opc : BitVec 32)
    (S0 : SequentialState Regs oracleChoiceSource)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_CBZ.native real Rt imm19 0#1 1#1 opc (-1) S0 = .ok () t ∧ Crypto.BcondCore.BrFrame S0 t := by
  by_cases hRt : (Rt.toNat : Int) = 31
  · have e : Rt = 31#5 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst e
    exact cbz_frame_pa31 real imm19 opc S0 hBP hVHE hlow
  · exact cbz_frame_pa real Rt imm19 opc S0 hRt hBP hVHE hlow

#print axioms cbz_frame_pa
#print axioms cbz_frame_pa_any
end RtBr.CbzFrame
