import LoopNative.Cbnz64.Prefix
import LoopNative.Branch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace LoopNative.Cbnz64
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.BcondCore LoopNative.Branch
set_option autoImplicit false
set_option maxRecDepth 100000

/-! route7 Cbnz64 (full 64-bit X: op = 1, sf = 1). prefix_native (drive_spec, BR8 pins, BranchTo opaque):
IsZero (X[Rt]<63:0>) gives BranchTo (PC + sext(imm19 ++ 00)) DIR true; otherwise registers untouched. Full tuples as Run. -/

/-- The decoder's branch condition, verbatim from the native. -/
abbrev condition (Rt : BitVec 5) (s : NativeState) : Prop :=
  IsZero (BitVec.castWidth
    (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rt.toNat).val] (Int.toNatChecked 63) 0) : BitVec 64) = false

abbrev target (imm19 : BitVec 19) (s : NativeState) : BitVec 64 := s.regs._PC + sign_extend (imm19 +++ 0#2) 64

set_option maxHeartbeats 200000 in
theorem run_taken (Rt : BitVec 5) (imm19 : BitVec 19) (t : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hrt : Rt.toNat < 31) (hc : condition Rt t) (hlow : (target imm19 t).toNat < 2 ^ 55) :
    ∃ u, (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 1#1 1#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs.BTypeNext = t.regs.BTypeNext ∧
      u.regs._PC = target imm19 t ∧ u.regs.__BranchTaken = true ∧
      u.regs.PhysicalCount = t.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = t.regs.gpr ∧ u.regs.SP_EL0 = t.regs.SP_EL0 ∧ u.regs.PSTATE = t.regs.PSTATE := by
  have hBP1 := hBP.base
  rw [prefix_complete Rt imm19 t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold prefix_native
  rw [dite_eq_left_of_eq_true (eq_true hc)]
  exact brto_tuple _ _ _ t hBP hlow (fun h => BranchType.noConfusion h)

set_option maxHeartbeats 200000 in
theorem run_not_taken (Rt : BitVec 5) (imm19 : BitVec 19) (t : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hrt : Rt.toNat < 31) (hc : ¬ condition Rt t) :
    ∃ u, (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 1#1 1#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs = t.regs ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs := by
  have hBP1 := hBP.base
  rw [prefix_complete Rt imm19 t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold prefix_native
  rw [dite_eq_right_of_eq_false (eq_false hc)]
  have hr : ∀ u : NativeState, u.regs = t.regs → ActFrameBr t u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs :=
    fun u h => ⟨actFrame_refl_of h, nonProj_of h⟩
  refine ⟨_, rfl, (hr _ ?_).1, ?_, ?_, ?_, (hr _ ?_).2⟩ <;> (repeat' split) <;> rfl

#print axioms run_taken
#print axioms run_not_taken
set_option maxHeartbeats 200000 in
theorem taken_z (Rt : BitVec 5) (imm19 : BitVec 19) (t u : NativeState) (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hrt : Rt.toNat < 31) (hc : condition Rt t) (hlow : (target imm19 t).toNat < 2 ^ 55)
    (hrun : (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 1#1 1#1 : SailM Unit) t = .ok () u) :
    u.regs._Z = t.regs._Z := by
  have hBP1 := hBP.base
  rw [prefix_complete Rt imm19 t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt] at hrun
  unfold prefix_native at hrun
  rw [dite_eq_left_of_eq_true (eq_true hc)] at hrun
  exact brto_z _ _ _ t u hBP hlow hrun

#print axioms taken_z

/-- Guard uses every bit of the 64-bit source register, not its low word. -/
theorem condition_iff (Rt : BitVec 5) (s : NativeState) :
    condition Rt s ↔ s.regs.gpr[(GPRSummary.key Rt.toNat).val] ≠ 0#64 := by
  simp [condition, IsZero, Sail.BitVec.extractLsb, Sail.Int.toNatChecked, BitVec.extractLsb, BitVec.length]

#print axioms condition_iff
end LoopNative.Cbnz64
