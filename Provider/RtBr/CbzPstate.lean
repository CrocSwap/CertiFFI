import BranchObs.Cbz
import RtBr.BrToRwPA
import BR8.CBZ
import SDKPA.BranchPins
import RtBr.CbzCond
import SDKPA.BranchPinsF
import Crypto.BrSimp
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
set_option autoImplicit false
namespace RtBr.CbzPstate
set_option maxHeartbeats 40000000 in
theorem pstate (real : Type) [Sail.SailReal real] (Rt : BitVec 5) (imm19 : BitVec 19) (opc : BitVec 32)
    (S0 : SequentialState Regs oracleChoiceSource) (hRt : ¬ (Rt.toNat : Int) = 31)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_CBZ.native real Rt imm19 0#1 1#1 opc (-1) S0 = .ok () t ∧ t.regs.PSTATE = S0.regs.PSTATE := by
  obtain ⟨t, h, f, -⟩ := ReleaseProfile.HeapCbzAction.cbz_obs_sail real Rt imm19 0#1 1#1 S0 { hBP with } hVHE hlow
  exact ⟨t, h, f.pstate⟩

theorem nzcv (real : Type) [Sail.SailReal real] (Rt : BitVec 5) (imm19 : BitVec 19) (opc : BitVec 32)
    (S0 : SequentialState Regs oracleChoiceSource) (hRt : ¬ (Rt.toNat : Int) = 31)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (t : SequentialState Regs oracleChoiceSource) (ht : BR_CBZ.native real Rt imm19 0#1 1#1 opc (-1) S0 = .ok () t) :
    t.regs.PSTATE.N = S0.regs.PSTATE.N ∧ t.regs.PSTATE.Z = S0.regs.PSTATE.Z ∧
    t.regs.PSTATE.C = S0.regs.PSTATE.C ∧ t.regs.PSTATE.V = S0.regs.PSTATE.V := by
  obtain ⟨u, hu, hp⟩ := pstate real Rt imm19 opc S0 hRt hBP hVHE hlow
  rw [hu] at ht; cases ht
  exact ⟨by rw [hp], by rw [hp], by rw [hp], by rw [hp]⟩

#print axioms nzcv
end RtBr.CbzPstate
