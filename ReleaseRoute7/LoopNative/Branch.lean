import NativeEntryBodyBranch.BrToExtra
import Bridge.CruxGenBrDefs
import Crypto.BrToCore
import SDKPA.BranchV2
import SDKPA.BrToCore
import SDKPA.Roots
import BR8.BranchToPins
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace LoopNative.Branch
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.BcondCore
set_option autoImplicit false
set_option maxRecDepth 100000

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

set_option maxHeartbeats 200000 in
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
  rw [BR8_BranchTo.complete_pa tgt bt c t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE (hVHE := BR8Pins.vhe_bang _ hBP.vhe) (hBit55 := BR8Pins.bit55_of_lt _ hlow)]
  obtain ⟨u, hN, hF, hbt, hpc, hbtt⟩ := Crypto.BrToCore.brto_obs_pa tgt bt c t hBP1 hBP.vhe hlow
  obtain ⟨u', hN', hph, hmask, hgic⟩ := NativeEntryBodyBranch.BrToExtra.extra tgt bt c t hBP1 hBP.vhe hlow
  have hu : u' = u := by
    have := hN'.symm.trans hN
    cases this; rfl
  subst hu
  have h1 : ActFrameBr t t := actFrame_refl_of rfl
  exact ⟨u', hN', frame_comp t t u' h1 hF, hF.mem, hF.events, hF.btn, hpc, hbt, hph, hmask, hgic,
    by rw [hbtt]; exact hne, hF.gpr, hF.sp, hF.pstate⟩

set_option maxHeartbeats 200000 in

theorem brto_z (tgt : BitVec 64) (bt : BranchType) (c : Bool) (t u : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA t) (hlow : tgt.toNat < 2 ^ 55)
    (hrun : (BranchTo tgt bt c : SailM Unit) t = .ok () u) : u.regs._Z = t.regs._Z := by
  have hBP1 := hBP.base
  rw [BR8_BranchTo.complete_pa tgt bt c t hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_MTE2 hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE (hVHE := BR8Pins.vhe_bang _ hBP.vhe) (hBit55 := BR8Pins.bit55_of_lt _ hlow)] at hrun
  obtain ⟨u0, hN, hF, _⟩ := Crypto.BrToCore.brto_obs_pa tgt bt c t hBP1 hBP.vhe hlow
  have : u = u0 := by
    have := hrun.symm.trans hN
    cases this; rfl
  subst this
  exact hF.z

#print axioms brto_tuple
#print axioms brto_z
end LoopNative.Branch
