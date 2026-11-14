-- rich-v6 (B1): BranchFrame + _Z (BrFrame.z / Good.z).
-- branch GPR/SP frames for heap-v2's actual Cbz, B.cond and RET
-- action steps: the action successor's GPR file and SP_EL0 equal the action state's (branches write no GPR;
-- RET does not write X30). Route: the SDKPA PA-free branch cores (cbz_obs_pa / bcond_obs_pa / RET BranchTo
-- core) + *.complete_pa, instantiated at the action state with the decision-175 PA-free pins held there
-- (BranchPinsV2PA, the < 2^55 target bound); the result is identified with the given action run by .ok
-- uniqueness. Proof blocks are reused verbatim from SDKPA.Crux{Cbz,Bcond,Ret}.obs_pa at t := act.
import BR8.BranchToPins
import SDKPA.CruxCbz
import RtBr.CbzFrame
import SDKPA.CruxBcond
import SDKPA.CruxRet
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
set_option autoImplicit false

namespace Crypto.CruxCbz
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.CbzDec
attribute [local instance 10] Classical.propDecidable

set_option maxHeartbeats 4000000 in
/-- CBZ Xt (sf = 1, op = 0): GPRs and SP_EL0 unchanged across the actual action. -/
theorem cbz_regsZ (real : Type) [Sail.SailReal real] (t a : NativeState) (imm19 : BitVec 19) (Rt : BitVec 5)
    (action : (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 1#1 : SailM Unit) t = .ok () a)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hlow : (t.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    a.regs.gpr = t.regs.gpr ∧ a.regs.SP_EL0 = t.regs.SP_EL0 ∧ a.regs._Z = t.regs._Z := by
  have hlow' := hlow
  obtain ⟨u, hN, hF⟩ := RtBr.CbzFrame.cbz_frame_pa_any real Rt imm19 (cbzWord 1#1 0#1 imm19 Rt) t hBP.base hBP.vhe hlow'
  have hA : (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 1#1 : SailM Unit) t = .ok () u := by
    rw [BR_CBZ.complete_pa real Rt imm19 0#1 1#1 (cbzWord 1#1 0#1 imm19 Rt) (-1)
      t hBP.base.hFeature_AA32EL0 hBP.base.hFeature_AA32EL1 hBP.base.hFeature_AA32EL2 hBP.base.hFeature_AA32EL3 hBP.base.hFeature_AA64EL0 hBP.base.hFeature_AA64EL1 hBP.base.hFeature_AA64EL2 hBP.base.hFeature_AA64EL3 hBP.base.hFeature_AES hBP.base.hFeature_AFP hBP.base.hFeature_AdvSIMD hBP.base.hFeature_BF16 hBP.base.hFeature_BRBE hBP.base.hFeature_BTI hBP.base.hFeature_CRC32 hBP.base.hFeature_DGH hBP.base.hFeature_DIT hBP.base.hFeature_DPB hBP.base.hFeature_DPB2 hBP.base.hFeature_Debugv8p9 hBP.base.hFeature_DotProd hBP.base.hFeature_ECV hBP.base.hFeature_FCMA hBP.base.hFeature_FHM hBP.base.hFeature_FP hBP.base.hFeature_FP16 hBP.base.hFeature_FRINTTS hBP.base.hFeature_FlagM hBP.base.hFeature_FlagM2 hBP.base.hFeature_I8MM hBP.base.hFeature_JSCVT hBP.base.hFeature_LRCPC hBP.base.hFeature_LRCPC2 hBP.base.hFeature_LSE hBP.base.hFeature_LSE2 hBP.base.hFeature_MOPS hBP.base.hFeature_MTE hBP.base.hFeature_MTE2 hBP.base.hFeature_PACIMP hBP.base.hFeature_PFAR hBP.base.hFeature_PMULL hBP.base.hFeature_RDM hBP.base.hFeature_RME hBP.base.hFeature_SB hBP.base.hFeature_SHA1 hBP.base.hFeature_SHA256 hBP.base.hFeature_SHA3 hBP.base.hFeature_SHA512 hBP.base.hFeature_SM3 hBP.base.hFeature_SM4 hBP.base.hFeature_SME hBP.base.hFeature_SME_F64F64 hBP.base.hFeature_SME_FA64 hBP.base.hFeature_SME_I16I64 hBP.base.hFeature_SVE hBP.base.hFeature_SVE2 hBP.base.hFeature_SVE_AES hBP.base.hFeature_SVE_BitPerm hBP.base.hFeature_SVE_PMULL128 hBP.base.hFeature_SVE_SHA3 hBP.base.hFeature_SVE_SM4 hBP.base.hFeature_TME hBP.base.hFeature_WFxT hBP.base.hDebugBP hBP.base.hDebugWP hBP.base.hDebugCTX hBP.base.hEDSCR_STATUS hBP.base.hSPE hBP.base.hEL hBP.base.hnRW hBP.base.hIL hBP.base.hE2H hBP.base.hTGE hBP.base.hSCR_NS hBP.base.hSCR_NSE hBP.base.hMDSCR_SS hBP.base.hPSTATE_SS hBP.base.hOSUC hBP.base.hPMB_E hBP.base.hSCR_RW hBP.base.hSCR_EEL2 hBP.base.hTBI0 hBP.base.hTBID0 hBP.base.hNSPB hBP.base.hNSPBE
      (Crypto.CbzBridge.inv_word 1#1 imm19 Rt) (Crypto.CbzBridge.inv_word 1#1 imm19 Rt)
      (Crypto.CbzBridge.arg_Rt 1#1 0#1 imm19 Rt) (Crypto.CbzBridge.arg_imm19 1#1 0#1 imm19 Rt) (Crypto.CbzBridge.arg_op 1#1 0#1 imm19 Rt) (Crypto.CbzBridge.arg_sf 1#1 0#1 imm19 Rt) (by decide)]
    exact hN
  have same : a = u := by
    have h := action.symm.trans hA
    injection h
  subst same
  exact ⟨hF.gpr, hF.sp, hF.z⟩

end Crypto.CruxCbz

namespace Crypto.CruxBcond
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondDec Crypto.BcondCore
attribute [local instance 10] Classical.propDecidable

set_option maxHeartbeats 4000000 in
/-- B.cond: GPRs and SP_EL0 unchanged across the actual action. -/
theorem bcond_regsZ (real : Type) [Sail.SailReal real] (t a : NativeState) (cond : BitVec 4) (imm19 : BitVec 19)
    (action : (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19 : SailM Unit) t = .ok () a)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hlow : (t.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    a.regs.gpr = t.regs.gpr ∧ a.regs.SP_EL0 = t.regs.SP_EL0 ∧ a.regs._Z = t.regs._Z := by
  have hlow' := hlow
  obtain ⟨u, hN, hF, -⟩ := bcond_obs_pa real cond imm19 t hBP.base hBP.vhe hlow'
  have hA : (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19 : SailM Unit) t = .ok () u := by
    rw [BR_BCondH.complete_pa real cond imm19 (bcondWord imm19 cond) (-1)
    t hBP.base.hFeature_AA32EL0 hBP.base.hFeature_AA32EL1 hBP.base.hFeature_AA32EL2 hBP.base.hFeature_AA32EL3 hBP.base.hFeature_AA64EL0 hBP.base.hFeature_AA64EL1 hBP.base.hFeature_AA64EL2 hBP.base.hFeature_AA64EL3 hBP.base.hFeature_AES hBP.base.hFeature_AFP hBP.base.hFeature_AdvSIMD hBP.base.hFeature_BF16 hBP.base.hFeature_BRBE hBP.base.hFeature_BTI hBP.base.hFeature_CRC32 hBP.base.hFeature_DGH hBP.base.hFeature_DIT hBP.base.hFeature_DPB hBP.base.hFeature_DPB2 hBP.base.hFeature_Debugv8p9 hBP.base.hFeature_DotProd hBP.base.hFeature_ECV hBP.base.hFeature_FCMA hBP.base.hFeature_FHM hBP.base.hFeature_FP hBP.base.hFeature_FP16 hBP.base.hFeature_FRINTTS hBP.base.hFeature_FlagM hBP.base.hFeature_FlagM2 hBP.base.hFeature_I8MM hBP.base.hFeature_JSCVT hBP.base.hFeature_LRCPC hBP.base.hFeature_LRCPC2 hBP.base.hFeature_LSE hBP.base.hFeature_LSE2 hBP.base.hFeature_MOPS hBP.base.hFeature_MTE hBP.base.hFeature_MTE2 hBP.base.hFeature_PACIMP hBP.base.hFeature_PFAR hBP.base.hFeature_PMULL hBP.base.hFeature_RDM hBP.base.hFeature_RME hBP.base.hFeature_SB hBP.base.hFeature_SHA1 hBP.base.hFeature_SHA256 hBP.base.hFeature_SHA3 hBP.base.hFeature_SHA512 hBP.base.hFeature_SM3 hBP.base.hFeature_SM4 hBP.base.hFeature_SME hBP.base.hFeature_SME_F64F64 hBP.base.hFeature_SME_FA64 hBP.base.hFeature_SME_I16I64 hBP.base.hFeature_SVE hBP.base.hFeature_SVE2 hBP.base.hFeature_SVE_AES hBP.base.hFeature_SVE_BitPerm hBP.base.hFeature_SVE_PMULL128 hBP.base.hFeature_SVE_SHA3 hBP.base.hFeature_SVE_SM4 hBP.base.hFeature_TME hBP.base.hFeature_WFxT hBP.base.hDebugBP hBP.base.hDebugWP hBP.base.hDebugCTX hBP.base.hEDSCR_STATUS hBP.base.hSPE hBP.base.hEL hBP.base.hnRW hBP.base.hIL hBP.base.hE2H hBP.base.hTGE hBP.base.hSCR_NS hBP.base.hSCR_NSE hBP.base.hMDSCR_SS hBP.base.hPSTATE_SS hBP.base.hOSUC hBP.base.hPMB_E hBP.base.hSCR_RW hBP.base.hSCR_EEL2 hBP.base.hTBI0 hBP.base.hTBID0 hBP.base.hNSPB hBP.base.hNSPBE
      (Crypto.BcondBridge.inv_word imm19 cond) (Crypto.BcondBridge.inv_word imm19 cond) (Crypto.BcondBridge.arg_cond imm19 cond) (Crypto.BcondBridge.arg_imm19 imm19 cond) (by decide)]
    exact hN
  have same : a = u := by
    have h := action.symm.trans hA
    injection h
  subst same
  exact ⟨hF.gpr, hF.sp, hF.z⟩

end Crypto.CruxBcond

namespace Crypto.CruxRet
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.CruxBrObl

set_option maxHeartbeats 8000000 in
/-- RET Xn: GPRs (incl. X30) and SP_EL0 unchanged across the actual action. -/
theorem ret_regsZ (real : Type) [Sail.SailReal real] (t a : NativeState) (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (action : (decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1 : SailM Unit) t = .ok () a)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hlow : (t.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) (btn : t.regs.BTypeNext = 0#2) :
    a.regs.gpr = t.regs.gpr ∧ a.regs.SP_EL0 = t.regs.SP_EL0 ∧ a.regs._Z = t.regs._Z := by
  have hlow' : (t.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55 := hlow
  have hGCS0 : t.regs.FeatureImpl[245] = false := hBP.gcs
  have key : ∃ u, (decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1 : SailM Unit) t = .ok () u ∧
      RFacts (spec Rn) t u := by
    unfold decode_ret_aarch64_instrs_branch_unconditional_register execute_aarch64_instrs_branch_unconditional_register
    have htn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
    simp (config := {decide := true}) only [undefined_BranchType, undefined_GCSInstruction, PreSail.internal_pick_at,
      PreSail.chooseAt, PreSail.choose, PreSail.occLabel, modifyGet, Functor.map, EStateM.map, MonadStateOf.modifyGet,
      EStateM.modifyGet, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true,
      ite_false, Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.and_true, beq_self_eq_true, htn]
    simp only [Crypto.BrRegs.xread64 _ Rn hRn]
    have wrBTN : ∀ (st : NativeState) (v : BitVec 2), (writeReg BTypeNext v : SailM Unit) st =
        .ok () { st with regs := { st.regs with BTypeNext := v } } := fun _ _ => rfl
    simp (config := {decide := true}) only [Crypto.BrRegs.gcs_off, hGCS0, wrBTN, EStateM.bind, EStateM.pure, ite_false,
      ite_true, Bool.false_eq_true, beq_self_eq_true, pure]
    name_app_state BranchTo 5 as S1
    name_call_arg BranchTo 3 as tgt
    have hBP1 : Crypto.BranchPinsPA S1 := by
      rw [← hS1]; exact ⟨hBP.base.hFeature_AA32EL0, hBP.base.hFeature_AA32EL1, hBP.base.hFeature_AA32EL2, hBP.base.hFeature_AA32EL3, hBP.base.hFeature_AA64EL0, hBP.base.hFeature_AA64EL1, hBP.base.hFeature_AA64EL2, hBP.base.hFeature_AA64EL3, hBP.base.hFeature_AES, hBP.base.hFeature_AFP, hBP.base.hFeature_AdvSIMD, hBP.base.hFeature_BF16, hBP.base.hFeature_BRBE, hBP.base.hFeature_BTI, hBP.base.hFeature_CRC32, hBP.base.hFeature_DGH, hBP.base.hFeature_DIT, hBP.base.hFeature_DPB, hBP.base.hFeature_DPB2, hBP.base.hFeature_Debugv8p9, hBP.base.hFeature_DotProd, hBP.base.hFeature_ECV, hBP.base.hFeature_FCMA, hBP.base.hFeature_FHM, hBP.base.hFeature_FP, hBP.base.hFeature_FP16, hBP.base.hFeature_FRINTTS, hBP.base.hFeature_FlagM, hBP.base.hFeature_FlagM2, hBP.base.hFeature_I8MM, hBP.base.hFeature_JSCVT, hBP.base.hFeature_LRCPC, hBP.base.hFeature_LRCPC2, hBP.base.hFeature_LSE, hBP.base.hFeature_LSE2, hBP.base.hFeature_MOPS, hBP.base.hFeature_MTE, hBP.base.hFeature_MTE2, hBP.base.hFeature_PACIMP, hBP.base.hFeature_PFAR, hBP.base.hFeature_PMULL, hBP.base.hFeature_RDM, hBP.base.hFeature_RME, hBP.base.hFeature_SB, hBP.base.hFeature_SHA1, hBP.base.hFeature_SHA256, hBP.base.hFeature_SHA3, hBP.base.hFeature_SHA512, hBP.base.hFeature_SM3, hBP.base.hFeature_SM4, hBP.base.hFeature_SME, hBP.base.hFeature_SME_F64F64, hBP.base.hFeature_SME_FA64, hBP.base.hFeature_SME_I16I64, hBP.base.hFeature_SVE, hBP.base.hFeature_SVE2, hBP.base.hFeature_SVE_AES, hBP.base.hFeature_SVE_BitPerm, hBP.base.hFeature_SVE_PMULL128, hBP.base.hFeature_SVE_SHA3, hBP.base.hFeature_SVE_SM4, hBP.base.hFeature_TME, hBP.base.hFeature_WFxT, hBP.base.hDebugBP, hBP.base.hDebugWP, hBP.base.hDebugCTX, hBP.base.hEDSCR_STATUS, hBP.base.hSPE, hBP.base.hEL, hBP.base.hnRW, hBP.base.hIL, hBP.base.hE2H, hBP.base.hTGE, hBP.base.hSCR_NS, hBP.base.hSCR_NSE, hBP.base.hMDSCR_SS, hBP.base.hPSTATE_SS, hBP.base.hOSUC, hBP.base.hPMB_E, hBP.base.hSCR_RW, hBP.base.hSCR_EEL2, hBP.base.hTBI0, hBP.base.hTBID0, hBP.base.hNSPB, hBP.base.hNSPBE⟩
    have hVHE1 : S1.regs.FeatureImpl[54] = true := by rw [← hS1]; exact hBP.vhe
    have hlow1 : tgt.toNat < 2 ^ 55 := by rw [← htgt]; exact hlow'
    rw [BR8_BranchTo.complete_pa tgt BranchType.BranchType_RET false S1 hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE (BR8Pins.vhe_bang _ hVHE1) (BR8Pins.bit55_of_lt _ hlow1)]
    obtain ⟨u, hN, hF, hbt, hpc, hbtt⟩ := Crypto.BrToCore.brto_obs_pa tgt BranchType.BranchType_RET false S1 hBP1 hVHE1 hlow1
    refine ⟨u, hN, ?_⟩
    have h1 : ActFrameBr t S1 := by
      rw [← hS1]; exact ⟨fun _ _ => rfl, rfl, rfl, btn.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hS1g : S1.regs.gpr = t.regs.gpr := by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
    have hS1m : S1.mem = t.mem := by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
    have hS1p : S1.regs.PSTATE = t.regs.PSTATE := by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
    have hS1sp : S1.regs.SP_EL0 = t.regs.SP_EL0 := by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
    have hS1z : S1.regs._Z = t.regs._Z := by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
    have htg : tgt = (spec Rn).fPC t := by first | (rw [← htgt]; done) | (rw [← htgt]; rfl)
    exact ⟨frame_comp t S1 u h1 hF, hF.mem.trans hS1m, hF.gpr.trans hS1g, hF.sp.trans hS1sp, hF.z.trans hS1z,
      hF.pstate.trans hS1p, hpc.trans htg, hbt, by rw [hbtt]; exact fun h => BranchType.noConfusion h,
      ArmCertCT.CT2.NonProjRegsEq.trans (by first | (rw [← hS1]; done) | (rw [← hS1]; unfold ArmCertCT.CT2.NonProjRegsEq ArmCertCT.CT2.mask; rfl)) hF.npe,
      hF.gic.trans (by first | (rw [← hS1]; done) | (rw [← hS1]; rfl))⟩
  obtain ⟨u, hu, hr⟩ := key
  have same : a = u := by
    have h := action.symm.trans hu
    injection h
  subst same
  exact ⟨hr.gpr, hr.sp, hr.z⟩

end Crypto.CruxRet

#print axioms Crypto.CruxCbz.cbz_regsZ
#print axioms Crypto.CruxBcond.bcond_regsZ
#print axioms Crypto.CruxRet.ret_regsZ
