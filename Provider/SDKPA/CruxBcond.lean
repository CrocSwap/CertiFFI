import Crypto.CruxBcond
import SDKPA.Roots
import SDKPA.BranchV2
import SDKPA.CbzCore
import SDKPA.BcondCore
import SDKPA.BrToCore
import Crypto.CruxBrObl
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace Crypto.CruxBcond
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondDec Crypto.BcondCore
attribute [local instance 10] Classical.propDecidable

set_option maxHeartbeats 4000000 in
theorem obs_pa (real : Type) [Sail.SailReal real] (cond : BitVec 4) (imm19 : BitVec 19) (s : NativeState)
    (hPins : ∀ t, PreBr s t → Crypto.BranchV2.BranchPinsV2PA t)
    (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∀ t, PreBr s t → ∃ u, Good (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19 : SailM Unit)
      (spec cond imm19) t u := by
  intro t ht
  have hBP := hPins t ht
  have hlow' : (t.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55 := by rw [ht.pc]; exact hlow
  obtain ⟨u, hN, hF, hcase⟩ := bcond_obs_pa real cond imm19 t hBP.base hBP.vhe hlow'
  have hA : (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19 : SailM Unit) t = .ok () u := by
    rw [BR_BCondH.complete_pa real cond imm19 (bcondWord imm19 cond) (-1)
    t hBP.base.hFeature_AA32EL0 hBP.base.hFeature_AA32EL1 hBP.base.hFeature_AA32EL2 hBP.base.hFeature_AA32EL3 hBP.base.hFeature_AA64EL0 hBP.base.hFeature_AA64EL1 hBP.base.hFeature_AA64EL2 hBP.base.hFeature_AA64EL3 hBP.base.hFeature_AES hBP.base.hFeature_AFP hBP.base.hFeature_AdvSIMD hBP.base.hFeature_BF16 hBP.base.hFeature_BRBE hBP.base.hFeature_BTI hBP.base.hFeature_CRC32 hBP.base.hFeature_DGH hBP.base.hFeature_DIT hBP.base.hFeature_DPB hBP.base.hFeature_DPB2 hBP.base.hFeature_Debugv8p9 hBP.base.hFeature_DotProd hBP.base.hFeature_ECV hBP.base.hFeature_FCMA hBP.base.hFeature_FHM hBP.base.hFeature_FP hBP.base.hFeature_FP16 hBP.base.hFeature_FRINTTS hBP.base.hFeature_FlagM hBP.base.hFeature_FlagM2 hBP.base.hFeature_I8MM hBP.base.hFeature_JSCVT hBP.base.hFeature_LRCPC hBP.base.hFeature_LRCPC2 hBP.base.hFeature_LSE hBP.base.hFeature_LSE2 hBP.base.hFeature_MOPS hBP.base.hFeature_MTE hBP.base.hFeature_MTE2 hBP.base.hFeature_PACIMP hBP.base.hFeature_PFAR hBP.base.hFeature_PMULL hBP.base.hFeature_RDM hBP.base.hFeature_RME hBP.base.hFeature_SB hBP.base.hFeature_SHA1 hBP.base.hFeature_SHA256 hBP.base.hFeature_SHA3 hBP.base.hFeature_SHA512 hBP.base.hFeature_SM3 hBP.base.hFeature_SM4 hBP.base.hFeature_SME hBP.base.hFeature_SME_F64F64 hBP.base.hFeature_SME_FA64 hBP.base.hFeature_SME_I16I64 hBP.base.hFeature_SVE hBP.base.hFeature_SVE2 hBP.base.hFeature_SVE_AES hBP.base.hFeature_SVE_BitPerm hBP.base.hFeature_SVE_PMULL128 hBP.base.hFeature_SVE_SHA3 hBP.base.hFeature_SVE_SM4 hBP.base.hFeature_TME hBP.base.hFeature_WFxT hBP.base.hDebugBP hBP.base.hDebugWP hBP.base.hDebugCTX hBP.base.hEDSCR_STATUS hBP.base.hSPE hBP.base.hEL hBP.base.hnRW hBP.base.hIL hBP.base.hE2H hBP.base.hTGE hBP.base.hSCR_NS hBP.base.hSCR_NSE hBP.base.hMDSCR_SS hBP.base.hPSTATE_SS hBP.base.hOSUC hBP.base.hPMB_E hBP.base.hSCR_RW hBP.base.hSCR_EEL2 hBP.base.hTBI0 hBP.base.hTBID0 hBP.base.hNSPB hBP.base.hNSPBE
      (Crypto.BcondBridge.inv_word imm19 cond) (Crypto.BcondBridge.inv_word imm19 cond) (Crypto.BcondBridge.arg_cond imm19 cond) (Crypto.BcondBridge.arg_imm19 imm19 cond) (by decide)]
    exact hN
  refine ⟨u, ?_⟩
  rcases hcase with ⟨hC, hbt, hpc, hbtt⟩ | ⟨hC, hbt, hpc, hbtt⟩
  · refine ⟨hA, actFrame_of t u hF, hF.mem, hF.gpr, hF.sp, hF.z, hF.pstate, ?_, ?_, hbtt, hF.npe, hF.gic⟩
    · show _ = (if bcondC cond t.regs then _ else _); rw [if_pos hC]; exact hpc
    · show _ = (if bcondC cond t.regs then _ else _); rw [if_pos hC]; exact hbt
  · refine ⟨hA, actFrame_of t u hF, hF.mem, hF.gpr, hF.sp, hF.z, hF.pstate, ?_, ?_, hbtt ▸ ht.btt, hF.npe, hF.gic⟩
    · show _ = (if bcondC cond t.regs then _ else _); rw [if_neg hC]; exact hpc
    · show _ = (if bcondC cond t.regs then _ else _); rw [if_neg hC]; exact hbt

/-- The five `crux_gen_br` obligations for B.cond. -/
theorem crux_obl_pa (real : Type) [Sail.SailReal real] (cond : BitVec 4) (imm19 : BitVec 19) (s : NativeState)
    (hPins : ∀ t, PreBr s t → Crypto.BranchV2.BranchPinsV2PA t)
    (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    let A : SailM Unit := decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19
    let R := Rg A (spec cond imm19)
    (∀ t, PreBr s t → A t = .ok () (R t)) ∧ (∀ t, ActFrameBr t (R t)) ∧
    (∀ t, ((R t).regs.__BranchTaken = t.regs.__BranchTaken ∧ (R t).regs._PC = t.regs._PC) ∨
      (R t).regs.__BranchTaken = true) ∧
    (∀ t, (R t).regs.Branchtypetaken ≠ BranchType.BranchType_RESET) ∧
    (∀ t1 t2, CongInBr t1 t2 → CongOutBr (R t1) (R t2)) := by
  intro A R
  refine obligations A (spec cond imm19) s (fun t => ?_) (fun t1 t2 h => ?_) (obs_pa real cond imm19 s hPins hlow)
  · by_cases hC : bcondC cond t.regs
    · right; show (if bcondC cond t.regs then _ else _) = true; rw [if_pos hC]
    · left; constructor
      · show (if bcondC cond t.regs then _ else _) = _; rw [if_neg hC]
      · show (if bcondC cond t.regs then _ else _) = _; rw [if_neg hC]
  · have hc := bcondC_congr cond t1.regs t2.regs h.base.ps
    refine ⟨h.base.gpr, ?_, ?_⟩
    · show (if bcondC cond t1.regs then _ else _) = (if bcondC cond t2.regs then _ else _)
      by_cases hC : bcondC cond t1.regs
      · rw [if_pos hC, if_pos (hc.1 hC), h.pc]
      · rw [if_neg hC, if_neg (fun h' => hC (hc.2 h')), h.pc]
    · show (if bcondC cond t1.regs then _ else _) = (if bcondC cond t2.regs then _ else _)
      by_cases hC : bcondC cond t1.regs
      · rw [if_pos hC, if_pos (hc.1 hC)]
      · rw [if_neg hC, if_neg (fun h' => hC (hc.2 h')), h.bt]

#print axioms crux_obl_pa
end Crypto.CruxBcond
