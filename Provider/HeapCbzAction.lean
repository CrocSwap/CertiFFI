-- BR8 L2: HeapCbzAction = Base + Obs + Extra (parallel) + run.
import HeapCbzAction.Obs
import HeapCbzAction.Extra
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace ReleaseProfile.HeapCbzAction
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.CbzDec Crypto.BcondCore
attribute [local instance 10] Classical.propDecidable

/- CBZ (X, sf=1) body run on the ACTUAL successor (Core 5d65/f10a): success,
ActFrameBr, mem, events, BTypeNext, the actual successor PC/BranchTaken (taken target
vs unchanged), PhysicalCount, full bkHeap NPE and GIC. From the canonical
Crypto.CbzCore.cbz_obs_pa (BrFrame) + BR_CBZ.complete_pa (as in Crypto.CruxCbz.obs) and
NativeEntryBodyBranch.CbzExtra on the SAME native result. m p (dead in the conclusion) are instantiated internally with default. -/
#check "CURRENT_DECL CBZ X run"
set_option maxHeartbeats 4000000 in
theorem run (real : Type) [Sail.SailReal real]
    (imm19 : BitVec 19) (Rt : BitVec 5) (s : NativeState)
    (hBP : TranslateSpan.BranchMTE2.Base s) (hVHE : s.regs.FeatureImpl[54] = true)
    (hlow : (s.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (hbtt0 : s.regs.Branchtypetaken ≠ BranchType.BranchType_RESET) :
    ∃ u, (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 1#1 : SailM Unit) s = .ok () u ∧
      ActFrameBr s u ∧ u.mem = s.mem ∧ u.events = s.events ∧ u.regs.BTypeNext = s.regs.BTypeNext ∧
      u.regs._PC = (Crypto.CruxCbz.spec 1#1 imm19 Rt).fPC s ∧
      u.regs.__BranchTaken = (Crypto.CruxCbz.spec 1#1 imm19 Rt).fBT s ∧
      u.regs.PhysicalCount = s.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap s.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = s.regs.gpr ∧ u.regs.SP_EL0 = s.regs.SP_EL0 ∧
      u.regs.PSTATE = s.regs.PSTATE := by
  obtain ⟨u, hN, hF, hcase⟩ := cbz_obs_sail real Rt imm19 0#1 1#1 s hBP hVHE hlow
  obtain ⟨u', hN', hph, hmask, hgic⟩ := extra real Rt imm19 0#1 1#1 s hBP hVHE hlow
  have hu : u' = u := by
    have := hN'.symm.trans hN
    cases this; rfl
  subst hu
  have hA : (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 1#1 : SailM Unit) s = .ok () u' := by
    rw [complete_pa real Rt imm19 0#1 1#1 (cbzWord 1#1 0#1 imm19 Rt) (-1)
      s hBP.hFeature_AA32EL0 hBP.hFeature_AA32EL1 hBP.hFeature_AA32EL2 hBP.hFeature_AA32EL3 hBP.hFeature_AA64EL0 hBP.hFeature_AA64EL1 hBP.hFeature_AA64EL2 hBP.hFeature_AA64EL3 hBP.hFeature_AES hBP.hFeature_AFP hBP.hFeature_AdvSIMD hBP.hFeature_BF16 hBP.hFeature_BRBE hBP.hFeature_BTI hBP.hFeature_CRC32 hBP.hFeature_DGH hBP.hFeature_DIT hBP.hFeature_DPB hBP.hFeature_DPB2 hBP.hFeature_Debugv8p9 hBP.hFeature_DotProd hBP.hFeature_ECV hBP.hFeature_FCMA hBP.hFeature_FHM hBP.hFeature_FP hBP.hFeature_FP16 hBP.hFeature_FRINTTS hBP.hFeature_FlagM hBP.hFeature_FlagM2 hBP.hFeature_I8MM hBP.hFeature_JSCVT hBP.hFeature_LRCPC hBP.hFeature_LRCPC2 hBP.hFeature_LSE hBP.hFeature_LSE2 hBP.hFeature_MOPS hBP.hFeature_MTE hBP.hFeature_PACIMP hBP.hFeature_PFAR hBP.hFeature_PMULL hBP.hFeature_RDM hBP.hFeature_RME hBP.hFeature_SB hBP.hFeature_SHA1 hBP.hFeature_SHA256 hBP.hFeature_SHA3 hBP.hFeature_SHA512 hBP.hFeature_SM3 hBP.hFeature_SM4 hBP.hFeature_SME hBP.hFeature_SME_F64F64 hBP.hFeature_SME_FA64 hBP.hFeature_SME_I16I64 hBP.hFeature_SVE hBP.hFeature_SVE2 hBP.hFeature_SVE_AES hBP.hFeature_SVE_BitPerm hBP.hFeature_SVE_PMULL128 hBP.hFeature_SVE_SHA3 hBP.hFeature_SVE_SM4 hBP.hFeature_TME hBP.hFeature_WFxT hBP.hDebugBP hBP.hDebugWP hBP.hDebugCTX hBP.hEDSCR_STATUS hBP.hSPE hBP.hEL hBP.hnRW hBP.hIL hBP.hE2H hBP.hTGE hBP.hSCR_NS hBP.hSCR_NSE hBP.hMDSCR_SS hBP.hPSTATE_SS hBP.hOSUC hBP.hPMB_E hBP.hSCR_RW hBP.hSCR_EEL2 hBP.hTBI0 hBP.hTBID0 hBP.hNSPB hBP.hNSPBE
      (Crypto.CbzBridge.inv_word 1#1 imm19 Rt) (Crypto.CbzBridge.inv_word 1#1 imm19 Rt)
      (Crypto.CbzBridge.arg_Rt 1#1 0#1 imm19 Rt) (Crypto.CbzBridge.arg_imm19 1#1 0#1 imm19 Rt) (Crypto.CbzBridge.arg_op 1#1 0#1 imm19 Rt) (Crypto.CbzBridge.arg_sf 1#1 0#1 imm19 Rt) (by decide)]
    exact hN'
  refine ⟨u', hA, actFrame_of s u' hF, hF.mem, hF.events, hF.btn, ?_, ?_, hph, hmask, hgic, ?_, hF.gpr, hF.sp, hF.pstate⟩
  · rcases hcase with ⟨hL, hbt, hpc, hbtt⟩ | ⟨hL, hbt, hpc, hbtt⟩
    · have hC : Crypto.CruxCbz.cbzC 1#1 Rt s := hL
      show _ = (if Crypto.CruxCbz.cbzC 1#1 Rt s then _ else _); rw [if_pos hC]; exact hpc
    · have hC : ¬ Crypto.CruxCbz.cbzC 1#1 Rt s := hL
      show _ = (if Crypto.CruxCbz.cbzC 1#1 Rt s then _ else _); rw [if_neg hC]; exact hpc
  · rcases hcase with ⟨hL, hbt, hpc, hbtt⟩ | ⟨hL, hbt, hpc, hbtt⟩
    · have hC : Crypto.CruxCbz.cbzC 1#1 Rt s := hL
      show _ = (if Crypto.CruxCbz.cbzC 1#1 Rt s then _ else _); rw [if_pos hC]; exact hbt
    · have hC : ¬ Crypto.CruxCbz.cbzC 1#1 Rt s := hL
      show _ = (if Crypto.CruxCbz.cbzC 1#1 Rt s then _ else _); rw [if_neg hC]; exact hbt
  · rcases hcase with ⟨hL, hbt, hpc, hbtt⟩ | ⟨hL, hbt, hpc, hbtt⟩
    · exact hbtt
    · rw [hbtt]; exact hbtt0

#print axioms run
end ReleaseProfile.HeapCbzAction
