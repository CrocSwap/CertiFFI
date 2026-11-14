import BR8.BranchToPins
import NativeR14B.B
import NativeR14B.Tbnz
import NativeEntryBodyBranch.BrToExtra
import Bridge.CruxGenBrDefs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace NativeR14B
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.BcondCore
set_option autoImplicit false
set_option maxRecDepth 1024
/-! Full action tuples for the runtime14 B / TBNZ32 (and CBZ32, Cbz.lean) step tails, in the conjunct order of
NativeR14Br.Ret.run / NativeEntryBodyBranch.Cbz.run: success, ActFrameBr, mem, events, BTypeNext, PC, BranchTaken,
PhysicalCount, NonProjRegsEq bkHeap, GIC, Branchtypetaken <> RESET, gpr, SP_EL0, PSTATE. Taken: BR8 complete_pa +
Crypto.BrToCore.brto_obs_pa + NativeEntryBodyBranch.BrToExtra.extra on the UNCHANGED state (no prefix writes).
Not taken: registers literally unchanged. -/

/-- Local copy of Crypto.CruxBrObl.frame_comp (as NativeR14Br.Ret). -/
theorem frame_comp (t S u : NativeState) (h1 : ActFrameBr t S) (hF : Crypto.BcondCore.BrFrame S u) : ActFrameBr t u :=
  ⟨fun k hk => (hF.bbool k hk).trans (h1.bbool k hk), hF.feat.trans h1.feat, by rw [hF.pstate]; exact h1.pse,
    hF.btn.trans h1.btn, hF.b64.trans h1.b64, hF.b32.trans h1.b32, hF.bint.trans h1.bint, hF.ss.trans h1.ss,
    hF.it.trans h1.it, hF.enc.trans h1.enc, hF.emu.trans h1.emu, hF.b128.trans h1.b128⟩

theorem actFrame_refl_of {t u : NativeState} (h : u.regs = t.regs) : ActFrameBr t u := by
  constructor <;> (try intro _ _) <;> rw [h]

theorem nonProj_of {t u : NativeState} (h : u.regs = t.regs) :
    ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs := by
  unfold ArmCertCT.CT2.NonProjRegsEq; rw [h]

set_option maxHeartbeats 8000000 in
/-- A BranchTo on an unchanged state t, as the full tuple. -/
theorem brto_tuple (tgt : BitVec 64) (bt : BranchType) (c : Bool) (t : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t) (hlow : tgt.toNat < 2 ^ 55) (hne : bt ≠ BranchType.BranchType_RESET) :
    ∃ u, (BranchTo tgt bt c : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs.BTypeNext = t.regs.BTypeNext ∧
      u.regs._PC = tgt ∧ u.regs.__BranchTaken = true ∧
      u.regs.PhysicalCount = t.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = t.regs.gpr ∧ u.regs.SP_EL0 = t.regs.SP_EL0 ∧ u.regs.PSTATE = t.regs.PSTATE := by
  have hBP1 := hBP.base
  rw [BR8_BranchTo.complete_pa tgt bt c t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE]
  obtain ⟨u, hN, hF, hbt, hpc, hbtt⟩ := Crypto.BrToCore.brto_obs_pa tgt bt c t hBP1 hBP.vhe hlow
  obtain ⟨u', hN', hph, hmask, hgic⟩ := NativeEntryBodyBranch.BrToExtra.extra tgt bt c t hBP1 hBP.vhe hlow
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
theorem b_run_full (imm26 : BitVec 26) (t : NativeState) (hBP : Crypto.BranchV2.BranchPinsV2PA t)
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

set_option maxHeartbeats 8000000 in
/-- TBNZ32 taken: the full tuple. -/
theorem tbnz_run_taken (Rt : BitVec 5) (imm14 : BitVec 14) (t : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
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
  rw [TbnzPinsPrefix_complete Rt imm14 t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE hrt]
  unfold TbnzPinsPrefix_native
  rw [dite_cond_eq_true (eq_true hc)]
  exact brto_tuple _ _ _ t hBP hlow (fun h => BranchType.noConfusion h)

/-- TBNZ32 not taken: registers unchanged (so every frame field is reflexive); Branchtypetaken carried from t. -/
theorem tbnz_run_not_taken (Rt : BitVec 5) (imm14 : BitVec 14) (t : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t)
    (hrt : Rt.toNat < 31) (hc : ¬ tbnzBit Rt t = 1#1) :
    ∃ u, (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 0#5 1#1 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs = t.regs ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs := by
  obtain ⟨u, hN, hr, hm, he⟩ := tbnz_not_taken Rt imm14 t hBP hrt hc
  exact ⟨u, hN, actFrame_refl_of hr, hm, he, hr, nonProj_of hr⟩

#print axioms brto_tuple
#print axioms b_run_full
#print axioms tbnz_run_taken
#print axioms tbnz_run_not_taken
end NativeR14B
