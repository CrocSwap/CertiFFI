import NativeR14B.CbzPinsPrefix
import NativeR14B.Run
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace NativeR14B
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.BcondCore
set_option autoImplicit false
set_option maxRecDepth 1024
/-! runtime14 CBZ (32-bit, CBZ W: op = 0, sf = 0). CbzPinsPrefix_native (drive_spec, BR8 pins, BranchTo opaque):
IsZero (X[Rt]<31:0>) gives BranchTo (PC + sext(imm19 ++ 00)) DIR true; otherwise registers untouched. Full tuples as Run. -/

/-- The decoder's branch condition, verbatim from the native. -/
abbrev cbz32Cond (Rt : BitVec 5) (s : NativeState) : Prop :=
  IsZero (BitVec.castWidth
    (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rt.toNat).val] (Int.toNatChecked 31) 0) : BitVec 32) = true

abbrev cbz32Target (imm19 : BitVec 19) (s : NativeState) : BitVec 64 := s.regs._PC + sign_extend (imm19 +++ 0#2) 64

set_option maxHeartbeats 8000000 in
theorem cbz32_run_taken (Rt : BitVec 5) (imm19 : BitVec 19) (t : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hrt : Rt.toNat < 31) (hc : cbz32Cond Rt t) (hlow : (cbz32Target imm19 t).toNat < 2 ^ 55) :
    ∃ u, (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs.BTypeNext = t.regs.BTypeNext ∧
      u.regs._PC = cbz32Target imm19 t ∧ u.regs.__BranchTaken = true ∧
      u.regs.PhysicalCount = t.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = t.regs.gpr ∧ u.regs.SP_EL0 = t.regs.SP_EL0 ∧ u.regs.PSTATE = t.regs.PSTATE := by
  have hBP1 := hBP.base
  rw [CbzPinsPrefix_complete Rt imm19 t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold CbzPinsPrefix_native
  rw [dite_cond_eq_true (eq_true hc)]
  exact brto_tuple _ _ _ t hBP hlow (fun h => BranchType.noConfusion h)

set_option maxHeartbeats 8000000 in
theorem cbz32_run_not_taken (Rt : BitVec 5) (imm19 : BitVec 19) (t : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hrt : Rt.toNat < 31) (hc : ¬ cbz32Cond Rt t) :
    ∃ u, (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs = t.regs ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs := by
  have hBP1 := hBP.base
  rw [CbzPinsPrefix_complete Rt imm19 t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold CbzPinsPrefix_native
  rw [dite_cond_eq_false (eq_false hc)]
  have hr : ∀ u : NativeState, u.regs = t.regs → ActFrameBr t u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs :=
    fun u h => ⟨actFrame_refl_of h, nonProj_of h⟩
  refine ⟨_, rfl, (hr _ ?_).1, ?_, ?_, ?_, (hr _ ?_).2⟩ <;> (repeat' split) <;> rfl

#print axioms cbz32_run_taken
#print axioms cbz32_run_not_taken
end NativeR14B
