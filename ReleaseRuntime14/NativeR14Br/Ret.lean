import BR8.BranchToPins
import BridgeDraft.StateProjection
import Bridge.CruxGenBrDefs
import Crypto.BcondCore
import NativeEntryBodyBranch.BrToExtra
import SDKPA.Roots
import SDKPA.BrToCore
import SDKPA.BranchV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace NativeR14Br.Ret
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.BcondCore

/-- Local copy of Crypto.CruxBrObl.frame_comp (pure field composition; avoids the old-bridge CruxBrObl module). -/
theorem frame_comp (t S u : NativeState) (h1 : ActFrameBr t S) (hF : Crypto.BcondCore.BrFrame S u) : ActFrameBr t u :=
  ⟨fun k hk => (hF.bbool k hk).trans (h1.bbool k hk), hF.feat.trans h1.feat, by rw [hF.pstate]; exact h1.pse,
    hF.btn.trans h1.btn, hF.b64.trans h1.b64, hF.b32.trans h1.b32, hF.bint.trans h1.bint, hF.ss.trans h1.ss,
    hF.it.trans h1.it, hF.enc.trans h1.enc, hF.emu.trans h1.emu, hF.b128.trans h1.b128⟩

/- d194: CruxRet-free copy of NativeEntryBodyBranch.Ret.run (PC stated as X[Rn] directly). RET body run on the ACTUAL successor: success, ActFrameBr, mem, events,
BTypeNext, PC = X[Rn] (Crypto.CruxRet.spec), BranchTaken, PhysicalCount, full bkHeap
NPE and GIC. Unfolding exactly as Crypto.CruxRet.obs up to BR8_BranchTo.complete_pa, then
the canonical Crypto.BrToCore.brto_obs_pa and NativeEntryBodyBranch.BrToExtra on the SAME
BranchTo native at the intermediate state S1 (only BTypeNext written). -/
set_option maxHeartbeats 8000000 in
theorem run (Rn : BitVec 5) (hRn : Rn.toNat < 31) (t : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t) (hbtn : t.regs.BTypeNext = 0#2)
    (hlow' : (t.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) :
    ∃ u, (decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs.BTypeNext = t.regs.BTypeNext ∧
      u.regs._PC = t.regs.gpr[(GPRSummary.key Rn.toNat).val] ∧ u.regs.__BranchTaken = true ∧
      u.regs.PhysicalCount = t.regs.PhysicalCount ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs ∧
      u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending ∧
      u.regs.Branchtypetaken ≠ BranchType.BranchType_RESET ∧
      u.regs.gpr = t.regs.gpr ∧ u.regs.SP_EL0 = t.regs.SP_EL0 ∧ u.regs.PSTATE = t.regs.PSTATE := by
  have hGCS0 : t.regs.FeatureImpl[245] = false := hBP.gcs
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
  rw [BR8_BranchTo.complete_pa tgt BranchType.BranchType_RET false S1 hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE]
  obtain ⟨u, hN, hF, hbt, hpc, hbtt⟩ := Crypto.BrToCore.brto_obs_pa tgt BranchType.BranchType_RET false S1 hBP1 hVHE1 hlow1
  obtain ⟨u', hN', hph, hmask, hgic⟩ := NativeEntryBodyBranch.BrToExtra.extra tgt BranchType.BranchType_RET false S1 hBP1 hVHE1 hlow1
  have hu : u' = u := by
    have := hN'.symm.trans hN
    cases this; rfl
  subst hu
  have h1 : ActFrameBr t S1 := by
    rw [← hS1]; exact ⟨fun _ _ => rfl, rfl, rfl, hbtn.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hS1m : S1.mem = t.mem := by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
  have hS1e : S1.events = t.events := by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
  have hS1c : S1.regs.PhysicalCount = t.regs.PhysicalCount := by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
  have hS1g : S1.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending := by
    first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
  have hS1k : ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap S1.regs = ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap t.regs := by
    first | (rw [← hS1]; done) | (rw [← hS1]; rfl)
  have htg : tgt = t.regs.gpr[(GPRSummary.key Rn.toNat).val] := by first | (rw [← htgt]; done) | (rw [← htgt]; rfl)
  have hfr := frame_comp t S1 u' h1 hF
  exact ⟨u', hN', hfr, hF.mem.trans hS1m, hF.events.trans hS1e, hfr.btn, hpc, hbt,
    hph.trans hS1c, hmask.trans hS1k, hgic.trans hS1g, by rw [hbtt]; exact fun h => BranchType.noConfusion h,
    hF.gpr.trans (by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)), hF.sp.trans (by first | (rw [← hS1]; done) | (rw [← hS1]; rfl)),
    hF.pstate.trans (by first | (rw [← hS1]; done) | (rw [← hS1]; rfl))⟩
  -- train-v3 BR8 split B2: BranchTo native pins (VHE, target bit55)
  case hVHE => exact BR8Pins.vhe_bang _ hVHE1
  case hBit55 => exact BR8Pins.bit55_of_lt _ hlow1

#print axioms run
end NativeR14Br.Ret
