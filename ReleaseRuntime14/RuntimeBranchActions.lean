import BR8.BranchToPins
-- Runtime branch actions over the real decoder, without the unused MTE2 pin.
import NativeR14B.Cbz
import RuntimeBranchLeaves
import TranslateSpan.BranchMTE2

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.BcondCore NativeR14B

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.RuntimeBranch
#check "CURRENT_DECL branch_actions"
/-- A BranchTo on an unchanged state t, as the full tuple. -/
theorem brto_tuple (tgt : BitVec 64) (bt : BranchType) (c : Bool) (t : NativeState)
    (hBP : TranslateSpan.BranchMTE2.Pins t) (hlow : tgt.toNat < 2 ^ 55) (hne : bt ≠ BranchType.BranchType_RESET) :
    ∃ u, (BranchTo tgt bt c : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs.BTypeNext = t.regs.BTypeNext ∧
      u.regs._PC = tgt ∧ u.regs.__BranchTaken = true ∧
      u.regs.PhysicalCount = t.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = t.regs.gpr ∧ u.regs.SP_EL0 = t.regs.SP_EL0 ∧ u.regs.PSTATE = t.regs.PSTATE := by
  have hBP1 := hBP.base
  rw [BR8_BranchTo.complete_pa_mte tgt bt c t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1
    hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1
    hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD
    hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH
    hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd
    hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16
    hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT
    hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS
    hBP1.hFeature_MTE hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM
    hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3
    hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64
    hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2
    hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3
    hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX
    hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS
    hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2
    hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE]
  obtain ⟨u, hN, hF, hbt, hpc, hbtt⟩ := TranslateSpan.BranchMTE2.brto_obs_pa tgt bt c t hBP1 hBP.vhe hlow
  obtain ⟨u', hN', hph, hmask, hgic⟩ := TranslateSpan.BranchMTE2.extra tgt bt c t hBP1 hBP.vhe hlow
  have hu : u' = u := by
    have := hN'.symm.trans hN
    cases this; rfl
  subst hu
  have h1 : ActFrameBr t t := actFrame_refl_of rfl
  exact ⟨u', hN', frame_comp t t u' h1 hF, hF.mem, hF.events, hF.btn, hpc, hbt, hph, hmask, hgic,
    by rw [hbtt]; exact hne, hF.gpr, hF.sp, hF.pstate⟩
  -- train-v3 BR8 split B2: BranchTo native pins (VHE, target bit55)
  all_goals first | exact BR8Pins.vhe_bang _ hBP.vhe | exact BR8Pins.bit55_of_lt _ hlow

/-- B: the full tuple (target = PC + sext(imm26 ++ 00)). -/
theorem b_run_full (imm26 : BitVec 26) (t : NativeState) (hBP : TranslateSpan.BranchMTE2.Pins t)
    (hlow : (NativeEntryCallerParts.blTarget imm26 t).toNat < 2 ^ 55) :
    ∃ u, (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs.BTypeNext = t.regs.BTypeNext ∧
      u.regs._PC = NativeEntryCallerParts.blTarget imm26 t ∧ u.regs.__BranchTaken = true ∧
      u.regs.PhysicalCount = t.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = t.regs.gpr ∧ u.regs.SP_EL0 = t.regs.SP_EL0 ∧ u.regs.PSTATE = t.regs.PSTATE := by
  have hb : (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 0#1 : SailM Unit) t =
      (BranchTo (NativeEntryCallerParts.blTarget imm26 t) BranchType.BranchType_DIR false : SailM Unit) t := by
    simpa only [BPrefix_native, NativeEntryCallerParts.blTarget] using BPrefix_complete imm26 t
  rw [hb]
  exact brto_tuple _ _ _ t hBP hlow (fun h => BranchType.noConfusion h)

/-- TBNZ32 taken: the full tuple. -/
theorem tbnz_run_taken (Rt : BitVec 5) (imm14 : BitVec 14) (t : NativeState)
    (hBP : TranslateSpan.BranchMTE2.Pins t)
    (hrt : Rt.toNat < 31) (hc : tbnzBit Rt t = 1#1) (hlow : (tbnzTarget imm14 t).toNat < 2 ^ 55) :
    ∃ u, (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 0#5 1#1 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs.BTypeNext = t.regs.BTypeNext ∧
      u.regs._PC = tbnzTarget imm14 t ∧ u.regs.__BranchTaken = true ∧
      u.regs.PhysicalCount = t.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = t.regs.gpr ∧ u.regs.SP_EL0 = t.regs.SP_EL0 ∧ u.regs.PSTATE = t.regs.PSTATE := by
  have hBP1 := hBP.base
  rw [ReleaseProfile.RuntimeBranchLeaves.tbnz_prefix Rt imm14 t hBP1.hFeature_AA32EL0
    hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0
    hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP
    hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32
    hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9
    hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP
    hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM
    hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2
    hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL
    hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256
    hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME
    hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE
    hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128
    hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP
    hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H
    hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E
    hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold TbnzPinsPrefix_native
  rw [dite_cond_eq_true (eq_true hc)]
  exact brto_tuple _ _ _ t hBP hlow (fun h => BranchType.noConfusion h)

/-- TBNZ32 not taken: registers unchanged (so every frame field is reflexive); Branchtypetaken carried from t. -/
theorem tbnz_run_not_taken (Rt : BitVec 5) (imm14 : BitVec 14) (t : NativeState)
    (hBP : TranslateSpan.BranchMTE2.Pins t)
    (hrt : Rt.toNat < 31) (hc : ¬ tbnzBit Rt t = 1#1) :
    ∃ u, (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 0#5 1#1 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs = t.regs ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs := by
  have hBP1 := hBP.base
  rw [ReleaseProfile.RuntimeBranchLeaves.tbnz_prefix Rt imm14 t hBP1.hFeature_AA32EL0
    hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0
    hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP
    hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32
    hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9
    hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP
    hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM
    hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2
    hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL
    hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256
    hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME
    hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE
    hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128
    hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP
    hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H
    hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E
    hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold TbnzPinsPrefix_native
  rw [dite_cond_eq_false (eq_false hc)]
  have hr : ∀ u : NativeState, u.regs = t.regs →
      ActFrameBr t u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs :=
    fun u h => ⟨actFrame_refl_of h, nonProj_of h⟩
  refine ⟨_, rfl, (hr _ ?_).1, ?_, ?_, ?_, (hr _ ?_).2⟩ <;> (repeat' split) <;> rfl

theorem cbz32_run_taken (Rt : BitVec 5) (imm19 : BitVec 19) (t : NativeState)
    (hBP : TranslateSpan.BranchMTE2.Pins t)
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
  rw [ReleaseProfile.RuntimeBranchLeaves.cbz_prefix Rt imm19 t hBP1.hFeature_AA32EL0
    hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0
    hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP
    hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32
    hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9
    hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP
    hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM
    hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2
    hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL
    hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256
    hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME
    hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE
    hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128
    hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP
    hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H
    hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E
    hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold CbzPinsPrefix_native
  rw [dite_cond_eq_true (eq_true hc)]
  exact brto_tuple _ _ _ t hBP hlow (fun h => BranchType.noConfusion h)

theorem cbz32_run_not_taken (Rt : BitVec 5) (imm19 : BitVec 19) (t : NativeState)
    (hBP : TranslateSpan.BranchMTE2.Pins t)
    (hrt : Rt.toNat < 31) (hc : ¬ cbz32Cond Rt t) :
    ∃ u, (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs = t.regs ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs := by
  have hBP1 := hBP.base
  rw [ReleaseProfile.RuntimeBranchLeaves.cbz_prefix Rt imm19 t hBP1.hFeature_AA32EL0
    hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0
    hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP
    hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32
    hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9
    hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP
    hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM
    hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2
    hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL
    hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256
    hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME
    hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE
    hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128
    hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP
    hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H
    hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E
    hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold CbzPinsPrefix_native
  rw [dite_cond_eq_false (eq_false hc)]
  have hr : ∀ u : NativeState, u.regs = t.regs → ActFrameBr t u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs :=
    fun u h => ⟨actFrame_refl_of h, nonProj_of h⟩
  refine ⟨_, rfl, (hr _ ?_).1, ?_, ?_, ?_, (hr _ ?_).2⟩ <;> (repeat' split) <;> rfl

#print axioms cbz32_run_taken
#print axioms cbz32_run_not_taken
#print axioms brto_tuple
#print axioms b_run_full
#print axioms tbnz_run_taken
#print axioms tbnz_run_not_taken
end ReleaseProfile.RuntimeBranch
