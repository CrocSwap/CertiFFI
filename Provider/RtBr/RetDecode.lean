-- RtBr.RetDecode (, /): RET NZCV frame at decode level, Sail-only.
import BR8.BranchToPins
import SDKPA.Roots
import RtBr.BrToPstate
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
set_option autoImplicit false
namespace RtBr.RetDecode

theorem cw63 (x : BitVec 64) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked 63) 0) : BitVec 64) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.castWidth, BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.Int.toNatChecked]

theorem xread64 (s : SequentialState Regs oracleChoiceSource) (R : BitVec 5) (hR : R.toNat < 31) :
    X_read ((R.toNat : Nat) : Int) 64 s = .ok (s.regs.gpr[(GPRSummary.key R.toNat).val]) s := by
  unfold X_read get_R
  have htn : Sail.Int.toNatChecked ((R.toNat : Nat) : Int) = R.toNat := rfl
  have h1 : ((R.toNat : Int) ≤ 31) := by omega
  have h2 : ¬ ((R.toNat : Int) = 31) := by omega
  simp [PreSail.assert, bind, EStateM.bind, pure, EStateM.pure, GPRSummary.read_complete, htn, h1, h2, cw63]

theorem gcs_off (s : SequentialState Regs oracleChoiceSource) (h : s.regs.FeatureImpl[245] = false) :
    HaveGCS () s = .ok false s := by
  have h' : (Register.FeatureImpl.get s.regs)[Sail.Int.toNatChecked (num_of_Feature Feature.FEAT_GCS)]! = false := h
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Sail.Int.toNatChecked (num_of_Feature Feature.FEAT_GCS)]! s = _
  rw [h']

/-- The BranchTo tail of RET keeps PSTATE. -/
theorem brto_tail (tgt : BitVec 64) (S1 u : SequentialState Regs oracleChoiceSource)
    (hB : Crypto.BranchPinsPA S1) (hVHE : S1.regs.FeatureImpl[54] = true) (hlow : tgt.toNat < 2 ^ 55)
    (h : (BranchTo tgt BranchType.BranchType_RET false : SailM Unit) S1 = .ok () u) :
    u.regs.PSTATE = S1.regs.PSTATE := by
  rw [BR8_BranchTo.complete_pa tgt BranchType.BranchType_RET false S1 hB.hFeature_AA32EL0 hB.hFeature_AA32EL1 hB.hFeature_AA32EL2 hB.hFeature_AA32EL3 hB.hFeature_AA64EL0 hB.hFeature_AA64EL1 hB.hFeature_AA64EL2 hB.hFeature_AA64EL3 hB.hFeature_AES hB.hFeature_AFP hB.hFeature_AdvSIMD hB.hFeature_BF16 hB.hFeature_BRBE hB.hFeature_BTI hB.hFeature_CRC32 hB.hFeature_DGH hB.hFeature_DIT hB.hFeature_DPB hB.hFeature_DPB2 hB.hFeature_Debugv8p9 hB.hFeature_DotProd hB.hFeature_ECV hB.hFeature_FCMA hB.hFeature_FHM hB.hFeature_FP hB.hFeature_FP16 hB.hFeature_FRINTTS hB.hFeature_FlagM hB.hFeature_FlagM2 hB.hFeature_I8MM hB.hFeature_JSCVT hB.hFeature_LRCPC hB.hFeature_LRCPC2 hB.hFeature_LSE hB.hFeature_LSE2 hB.hFeature_MOPS hB.hFeature_MTE hB.hFeature_MTE2 hB.hFeature_PACIMP hB.hFeature_PFAR hB.hFeature_PMULL hB.hFeature_RDM hB.hFeature_RME hB.hFeature_SB hB.hFeature_SHA1 hB.hFeature_SHA256 hB.hFeature_SHA3 hB.hFeature_SHA512 hB.hFeature_SM3 hB.hFeature_SM4 hB.hFeature_SME hB.hFeature_SME_F64F64 hB.hFeature_SME_FA64 hB.hFeature_SME_I16I64 hB.hFeature_SVE hB.hFeature_SVE2 hB.hFeature_SVE_AES hB.hFeature_SVE_BitPerm hB.hFeature_SVE_PMULL128 hB.hFeature_SVE_SHA3 hB.hFeature_SVE_SM4 hB.hFeature_TME hB.hFeature_WFxT hB.hDebugBP hB.hDebugWP hB.hDebugCTX hB.hEDSCR_STATUS hB.hSPE hB.hEL hB.hnRW hB.hIL hB.hE2H hB.hTGE hB.hSCR_NS hB.hSCR_NSE hB.hMDSCR_SS hB.hPSTATE_SS hB.hOSUC hB.hPMB_E hB.hSCR_RW hB.hSCR_EEL2 hB.hTBI0 hB.hTBID0 hB.hNSPB hB.hNSPBE (BR8Pins.vhe_bang _ hVHE) (BR8Pins.bit55_of_lt _ hlow)] at h
  obtain ⟨t, ht, hp⟩ := RtBr.BrToPstate.pstate tgt BranchType.BranchType_RET false S1 hB hVHE hlow
  rw [ht] at h; cases h; exact hp

set_option maxHeartbeats 8000000 in
/-- RET Xn (decode level): N, Z, C, V unchanged. -/
theorem decode_nzcv (Rn : BitVec 5) (hRn : Rn.toNat < 31) (t u : SequentialState Regs oracleChoiceSource)
    (hB : Crypto.BranchPinsPA t) (hVHE : t.regs.FeatureImpl[54] = true) (hGCS0 : t.regs.FeatureImpl[245] = false)
    (hlow : (t.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (h : (decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1 : SailM Unit) t = .ok () u) :
    u.regs.PSTATE.N = t.regs.PSTATE.N ∧ u.regs.PSTATE.Z = t.regs.PSTATE.Z ∧
    u.regs.PSTATE.C = t.regs.PSTATE.C ∧ u.regs.PSTATE.V = t.regs.PSTATE.V := by
  unfold decode_ret_aarch64_instrs_branch_unconditional_register execute_aarch64_instrs_branch_unconditional_register at h
  have htn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  simp (config := {decide := true}) only [undefined_BranchType, undefined_GCSInstruction, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, modifyGet, Functor.map, EStateM.map, MonadStateOf.modifyGet,
    EStateM.modifyGet, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true,
    ite_false, Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.true_and,
    Bool.and_true, beq_self_eq_true, htn] at h
  simp only [xread64 _ Rn hRn] at h
  have wrBTN : ∀ (st : SequentialState Regs oracleChoiceSource) (v : BitVec 2), (writeReg BTypeNext v : SailM Unit) st =
      .ok () { st with regs := { st.regs with BTypeNext := v } } := fun _ _ => rfl
  simp (config := {decide := true}) only [gcs_off, hGCS0, wrBTN, EStateM.bind, EStateM.pure, ite_false,
    ite_true, Bool.false_eq_true, beq_self_eq_true, pure] at h
  have hp := brto_tail _ _ u (by exact ⟨hB.hFeature_AA32EL0, hB.hFeature_AA32EL1, hB.hFeature_AA32EL2, hB.hFeature_AA32EL3, hB.hFeature_AA64EL0, hB.hFeature_AA64EL1, hB.hFeature_AA64EL2, hB.hFeature_AA64EL3, hB.hFeature_AES, hB.hFeature_AFP, hB.hFeature_AdvSIMD, hB.hFeature_BF16, hB.hFeature_BRBE, hB.hFeature_BTI, hB.hFeature_CRC32, hB.hFeature_DGH, hB.hFeature_DIT, hB.hFeature_DPB, hB.hFeature_DPB2, hB.hFeature_Debugv8p9, hB.hFeature_DotProd, hB.hFeature_ECV, hB.hFeature_FCMA, hB.hFeature_FHM, hB.hFeature_FP, hB.hFeature_FP16, hB.hFeature_FRINTTS, hB.hFeature_FlagM, hB.hFeature_FlagM2, hB.hFeature_I8MM, hB.hFeature_JSCVT, hB.hFeature_LRCPC, hB.hFeature_LRCPC2, hB.hFeature_LSE, hB.hFeature_LSE2, hB.hFeature_MOPS, hB.hFeature_MTE, hB.hFeature_MTE2, hB.hFeature_PACIMP, hB.hFeature_PFAR, hB.hFeature_PMULL, hB.hFeature_RDM, hB.hFeature_RME, hB.hFeature_SB, hB.hFeature_SHA1, hB.hFeature_SHA256, hB.hFeature_SHA3, hB.hFeature_SHA512, hB.hFeature_SM3, hB.hFeature_SM4, hB.hFeature_SME, hB.hFeature_SME_F64F64, hB.hFeature_SME_FA64, hB.hFeature_SME_I16I64, hB.hFeature_SVE, hB.hFeature_SVE2, hB.hFeature_SVE_AES, hB.hFeature_SVE_BitPerm, hB.hFeature_SVE_PMULL128, hB.hFeature_SVE_SHA3, hB.hFeature_SVE_SM4, hB.hFeature_TME, hB.hFeature_WFxT, hB.hDebugBP, hB.hDebugWP, hB.hDebugCTX, hB.hEDSCR_STATUS, hB.hSPE, hB.hEL, hB.hnRW, hB.hIL, hB.hE2H, hB.hTGE, hB.hSCR_NS, hB.hSCR_NSE, hB.hMDSCR_SS, hB.hPSTATE_SS, hB.hOSUC, hB.hPMB_E, hB.hSCR_RW, hB.hSCR_EEL2, hB.hTBI0, hB.hTBID0, hB.hNSPB, hB.hNSPBE⟩) (by exact hVHE) (by exact hlow) h
  exact ⟨by rw [hp], by rw [hp], by rw [hp], by rw [hp]⟩

#print axioms decode_nzcv
end RtBr.RetDecode
