-- BR8 L2: BcondAction = Obs + Extra (parallel) + run.
import TranslateSpan.BrToRwMTE
import NativeEntryBodyBranch.Bcond
import TranslateSpan.BranchMTE2
import DropUnusedPremise
import BcondAction.Obs
import BcondAction.Extra
-- Actual B.cond action with no MTE2 premise.
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace ReleaseProfile.BcondAction
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondDec Crypto.BcondCore
attribute [local instance 10] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 512
set_option Elab.async false


#check "CURRENT_DECL bcond_obs_current"
set_option maxHeartbeats 200000 in
theorem run (real : Type) [Sail.SailReal real] (cond : BitVec 4) (imm19 : BitVec 19) (s : NativeState)
    (hBP : TranslateSpan.BranchMTE2.Base s) (hVHE : s.regs.FeatureImpl[54] = true)
    (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (hbtt0 : s.regs.Branchtypetaken ≠ BranchType.BranchType_RESET) :
    ∃ u, (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19 : SailM Unit) s = .ok () u ∧
      ActFrameBr s u ∧ u.mem = s.mem ∧ u.events = s.events ∧ u.regs.BTypeNext = s.regs.BTypeNext ∧
      u.regs._PC = (Crypto.CruxBcond.spec cond imm19).fPC s ∧
      u.regs.__BranchTaken = (Crypto.CruxBcond.spec cond imm19).fBT s ∧
      u.regs.PhysicalCount = s.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap s.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = s.regs.gpr ∧ u.regs.SP_EL0 = s.regs.SP_EL0 ∧ u.regs.PSTATE = s.regs.PSTATE := by
  obtain ⟨u, hN, hF, hcase⟩ := bcond_obs_current real cond imm19 s hBP hVHE hlow
  obtain ⟨u', hN', hph, hmask, hgic⟩ := extra real cond imm19 s hBP hVHE hlow
  have hu : u' = u := by
    have := hN'.symm.trans hN
    cases this; rfl
  subst hu
  have hA : (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19 : SailM Unit) s = .ok () u' := by
    rw [complete_pa real cond imm19 (bcondWord imm19 cond) (-1)
    s hBP.hFeature_AA32EL0 hBP.hFeature_AA32EL1 hBP.hFeature_AA32EL2 hBP.hFeature_AA32EL3 hBP.hFeature_AA64EL0 hBP.hFeature_AA64EL1 hBP.hFeature_AA64EL2 hBP.hFeature_AA64EL3 hBP.hFeature_AES hBP.hFeature_AFP hBP.hFeature_AdvSIMD hBP.hFeature_BF16 hBP.hFeature_BRBE hBP.hFeature_BTI hBP.hFeature_CRC32 hBP.hFeature_DGH hBP.hFeature_DIT hBP.hFeature_DPB hBP.hFeature_DPB2 hBP.hFeature_Debugv8p9 hBP.hFeature_DotProd hBP.hFeature_ECV hBP.hFeature_FCMA hBP.hFeature_FHM hBP.hFeature_FP hBP.hFeature_FP16 hBP.hFeature_FRINTTS hBP.hFeature_FlagM hBP.hFeature_FlagM2 hBP.hFeature_I8MM hBP.hFeature_JSCVT hBP.hFeature_LRCPC hBP.hFeature_LRCPC2 hBP.hFeature_LSE hBP.hFeature_LSE2 hBP.hFeature_MOPS hBP.hFeature_MTE hBP.hFeature_PACIMP hBP.hFeature_PFAR hBP.hFeature_PMULL hBP.hFeature_RDM hBP.hFeature_RME hBP.hFeature_SB hBP.hFeature_SHA1 hBP.hFeature_SHA256 hBP.hFeature_SHA3 hBP.hFeature_SHA512 hBP.hFeature_SM3 hBP.hFeature_SM4 hBP.hFeature_SME hBP.hFeature_SME_F64F64 hBP.hFeature_SME_FA64 hBP.hFeature_SME_I16I64 hBP.hFeature_SVE hBP.hFeature_SVE2 hBP.hFeature_SVE_AES hBP.hFeature_SVE_BitPerm hBP.hFeature_SVE_PMULL128 hBP.hFeature_SVE_SHA3 hBP.hFeature_SVE_SM4 hBP.hFeature_TME hBP.hFeature_WFxT hBP.hDebugBP hBP.hDebugWP hBP.hDebugCTX hBP.hEDSCR_STATUS hBP.hSPE hBP.hEL hBP.hnRW hBP.hIL hBP.hE2H hBP.hTGE hBP.hSCR_NS hBP.hSCR_NSE hBP.hMDSCR_SS hBP.hPSTATE_SS hBP.hOSUC hBP.hPMB_E hBP.hSCR_RW hBP.hSCR_EEL2 hBP.hTBI0 hBP.hTBID0 hBP.hNSPB hBP.hNSPBE
      (Crypto.BcondBridge.inv_word imm19 cond) (Crypto.BcondBridge.inv_word imm19 cond) (Crypto.BcondBridge.arg_cond imm19 cond) (Crypto.BcondBridge.arg_imm19 imm19 cond) (by decide)]
    exact hN'
  refine ⟨u', hA, actFrame_of s u' hF, hF.mem, hF.events, hF.btn, ?_, ?_, hph, hmask, hgic, ?_, hF.gpr, hF.sp, hF.pstate⟩
  · rcases hcase with ⟨hC, hbt, hpc, hbtt⟩ | ⟨hC, hbt, hpc, hbtt⟩
    · show _ = (if bcondC cond s.regs then _ else _); rw [if_pos hC]; exact hpc
    · show _ = (if bcondC cond s.regs then _ else _); rw [if_neg hC]; exact hpc
  · rcases hcase with ⟨hC, hbt, hpc, hbtt⟩ | ⟨hC, hbt, hpc, hbtt⟩
    · show _ = (if bcondC cond s.regs then _ else _); rw [if_pos hC]; exact hbt
    · show _ = (if bcondC cond s.regs then _ else _); rw [if_neg hC]; exact hbt
  · rcases hcase with ⟨hC, hbt, hpc, hbtt⟩ | ⟨hC, hbt, hpc, hbtt⟩
    · exact hbtt
    · rw [hbtt]; exact hbtt0

#print axioms run
end ReleaseProfile.BcondAction
