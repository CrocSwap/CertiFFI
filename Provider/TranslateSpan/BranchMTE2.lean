-- Additive exact BranchTo observations and RET action independent of MTE2.
-- The old modules remain immutable. Inputs are the pinned generated Sail proofs.
import TranslateSpan.BranchMTE2Base
import BR8.BranchToPins
import TranslateSpan.BranchMTE2Probe
import NativeEntryBodyBranch.Ret
import SDKPA.BranchPinsF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
open ArmBridge.Draft
set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace TranslateSpan.BranchMTE2


structure Pins (s : NativeState) : Prop where
  base : Base s
  vhe : s.regs.FeatureImpl[54] = true
  gcs : s.regs.FeatureImpl[245] = false


open Crypto.BcondCore ArmBridge.CruxGenBr Crypto.CruxBrObl
set_option maxHeartbeats 40000000 in
/-- Observation of driver's flat BranchTo root: ok, frame, BranchTaken, PC = target (low target). -/
theorem brto_obs_pa (target : BitVec 64) (bt : BranchType) (c : Bool) (S0 : SequentialState Regs oracleChoiceSource)
    (hBP : Base S0) (hVHE : S0.regs.FeatureImpl[54] = true) (hlow : target.toNat < 2 ^ 55) :
    ∃ t, BR8_BranchTo.native target bt c S0 = .ok () t ∧ BrFrame S0 t ∧
      t.regs.__BranchTaken = true ∧ t.regs._PC = target ∧ t.regs.Branchtypetaken = bt := by
  have hNS : Sail.BitVec.extractLsb (Mk_SCRType (S0.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3)) 0 0 = 1#1 := hBP.hSCR_NS
  have hb55 := Crypto.BrSimp.b55_false _ hlow
  have gi := Crypto.BrSimp.gi259
  have := hBP.f0
  have := hBP.f1
  have := hBP.f2
  have := hBP.f3
  have := hBP.f4
  have := hBP.f5
  have := hBP.f6
  have := hBP.f7
  have := hBP.f12
  have := hBP.f153
  have := hBP.f13
  have := hBP.f143
  have := hBP.f230
  have := hBP.f123
  have := hBP.f45
  have := hBP.f144
  have := hBP.f103
  have := hBP.f60
  have := hBP.f126
  have := hBP.f185
  have := hBP.f105
  have := hBP.f145
  have := hBP.f89
  have := hBP.f107
  have := hBP.f27
  have := hBP.f65
  have := hBP.f130
  have := hBP.f108
  have := hBP.f131
  have := hBP.f67
  have := hBP.f92
  have := hBP.f93
  have := hBP.f110
  have := hBP.f50
  have := hBP.f111
  have := hBP.f171
  have := hBP.f133
  have := hBP.f95
  have := hBP.f200
  have := hBP.f36
  have := hBP.f53
  have := hBP.f232
  have := hBP.f138
  have := hBP.f40
  have := hBP.f41
  have := hBP.f76
  have := hBP.f77
  have := hBP.f78
  have := hBP.f79
  have := hBP.f233
  have := hBP.f234
  have := hBP.f235
  have := hBP.f236
  have := hBP.f81
  have := hBP.f221
  have := hBP.f222
  have := hBP.f223
  have := hBP.f224
  have := hBP.f225
  have := hBP.f226
  have := hBP.f227
  have := hBP.f165
  observe_simp [BR8_BranchTo.native]
  simp only [Crypto.BrSimp.tt_ff, Crypto.BrSimp.tt_ff2, Crypto.BrSimp.idx_55_63, ite_true, ite_false,
    dite_true, dite_false]
  simp (config := {maxSteps := 2000000}) only [Crypto.BrSimp.ok_ite, Crypto.BrSimp.ok_dite, Crypto.BrSimp.ok_exists]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals try (intro k hk)
  all_goals observe_simp [Sail.ConcurrencyInterfaceV1.RegisterRef.set]
  all_goals try simp only [dite_eq_ite, ite_self]
  all_goals try (simp (disch := first | exact hk | exact Ne.symm hk) only [Sail.ConcurrencyInterfaceV1.RegMap.set_ne, dite_eq_ite, ite_self]; done)
  all_goals try exact Crypto.BrSimp.tbi_low _ hlow _
  all_goals try decide
  all_goals try (first
    | exact ArmCertCT.CT2.NonProjRegsEq.refl _ _
    | (unfold ArmCertCT.CT2.NonProjRegsEq ArmCertCT.CT2.mask
       congr 1 <;> (try repeat' split) <;> (try simp (disch := decide) only [ArmBridge.CruxNonProj.maskBank_set]) <;> rfl))
#print axioms brto_obs_pa

open Crypto.BcondCore
set_option maxHeartbeats 40000000 in
theorem extra (target : BitVec 64) (bt : BranchType) (c : Bool) (S0 : SequentialState Regs oracleChoiceSource)
    (hBP : Base S0) (hVHE : S0.regs.FeatureImpl[54] = true) (hlow : target.toNat < 2 ^ 55) :
    ∃ t, BR8_BranchTo.native target bt c S0 = .ok () t ∧
      t.regs.PhysicalCount = S0.regs.PhysicalCount ∧
      ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap t.regs = ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap S0.regs ∧
      t.regs.bank_Option_InterruptID .__GIC_Pending = S0.regs.bank_Option_InterruptID .__GIC_Pending := by
  have hNS : Sail.BitVec.extractLsb (Mk_SCRType (S0.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3)) 0 0 = 1#1 := hBP.hSCR_NS
  have hb55 := Crypto.BrSimp.b55_false _ hlow
  have gi := Crypto.BrSimp.gi259
  have := hBP.f0
  have := hBP.f1
  have := hBP.f2
  have := hBP.f3
  have := hBP.f4
  have := hBP.f5
  have := hBP.f6
  have := hBP.f7
  have := hBP.f12
  have := hBP.f153
  have := hBP.f13
  have := hBP.f143
  have := hBP.f230
  have := hBP.f123
  have := hBP.f45
  have := hBP.f144
  have := hBP.f103
  have := hBP.f60
  have := hBP.f126
  have := hBP.f185
  have := hBP.f105
  have := hBP.f145
  have := hBP.f89
  have := hBP.f107
  have := hBP.f27
  have := hBP.f65
  have := hBP.f130
  have := hBP.f108
  have := hBP.f131
  have := hBP.f67
  have := hBP.f92
  have := hBP.f93
  have := hBP.f110
  have := hBP.f50
  have := hBP.f111
  have := hBP.f171
  have := hBP.f133
  have := hBP.f95
  have := hBP.f200
  have := hBP.f36
  have := hBP.f53
  have := hBP.f232
  have := hBP.f138
  have := hBP.f40
  have := hBP.f41
  have := hBP.f76
  have := hBP.f77
  have := hBP.f78
  have := hBP.f79
  have := hBP.f233
  have := hBP.f234
  have := hBP.f235
  have := hBP.f236
  have := hBP.f81
  have := hBP.f221
  have := hBP.f222
  have := hBP.f223
  have := hBP.f224
  have := hBP.f225
  have := hBP.f226
  have := hBP.f227
  have := hBP.f165
  observe_simp [BR8_BranchTo.native]
  simp only [Crypto.BrSimp.tt_ff, Crypto.BrSimp.tt_ff2, Crypto.BrSimp.idx_55_63, ite_true, ite_false,
    dite_true, dite_false]
  simp (config := {maxSteps := 2000000}) only [Crypto.BrSimp.ok_ite, Crypto.BrSimp.ok_dite, Crypto.BrSimp.ok_exists]
  refine ⟨?_, ?_, ?_⟩
  all_goals try (intro k hk)
  all_goals observe_simp [Sail.ConcurrencyInterfaceV1.RegisterRef.set]
  all_goals try simp only [dite_eq_ite, ite_self]
  all_goals try simp only [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskPSTATE, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap]
  all_goals
    congr 1
    all_goals first
      | rfl
      | (split <;> rfl)
      | (split <;> split <;> rfl)
      | (funext k; split <;> rfl)
      | (funext k; cases k <;> rfl)
      | (funext k; simp only [ArmCertCT.CT2.maskBank]; split <;> (try split) <;> (try split) <;> (try split) <;> (try simp (config := {maxSteps := 200000}) [Sail.ConcurrencyInterfaceV1.RegMap.set, Sail.ConcurrencyInterfaceV1.RegisterRef.set, *]) <;> (try contradiction) <;> (try (subst_vars; contradiction)) <;> (try (subst_vars; simp_all)) <;> (try (intro _ hk; subst hk; contradiction)) <;> (try (intro _ hk; subst hk; simp_all)) <;> done)

#print axioms extra

set_option maxHeartbeats 8000000 in
theorem run (Rn : BitVec 5) (hRn : Rn.toNat < 31) (t : NativeState)
    (hBP : Pins t) (hbtn : t.regs.BTypeNext = 0#2)
    (hlow' : (t.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) :
    ∃ u, (decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1 : SailM Unit) t = .ok () u ∧
      ActFrameBr t u ∧ u.mem = t.mem ∧ u.events = t.events ∧ u.regs.BTypeNext = t.regs.BTypeNext ∧
      u.regs._PC = (Crypto.CruxRet.spec Rn).fPC t ∧ u.regs.__BranchTaken = (Crypto.CruxRet.spec Rn).fBT t ∧
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
  have hBP1 : Base S1 := by
    rw [← hS1]; exact ⟨hBP.base.hFeature_AA32EL0, hBP.base.hFeature_AA32EL1, hBP.base.hFeature_AA32EL2, hBP.base.hFeature_AA32EL3, hBP.base.hFeature_AA64EL0, hBP.base.hFeature_AA64EL1, hBP.base.hFeature_AA64EL2, hBP.base.hFeature_AA64EL3, hBP.base.hFeature_AES, hBP.base.hFeature_AFP, hBP.base.hFeature_AdvSIMD, hBP.base.hFeature_BF16, hBP.base.hFeature_BRBE, hBP.base.hFeature_BTI, hBP.base.hFeature_CRC32, hBP.base.hFeature_DGH, hBP.base.hFeature_DIT, hBP.base.hFeature_DPB, hBP.base.hFeature_DPB2, hBP.base.hFeature_Debugv8p9, hBP.base.hFeature_DotProd, hBP.base.hFeature_ECV, hBP.base.hFeature_FCMA, hBP.base.hFeature_FHM, hBP.base.hFeature_FP, hBP.base.hFeature_FP16, hBP.base.hFeature_FRINTTS, hBP.base.hFeature_FlagM, hBP.base.hFeature_FlagM2, hBP.base.hFeature_I8MM, hBP.base.hFeature_JSCVT, hBP.base.hFeature_LRCPC, hBP.base.hFeature_LRCPC2, hBP.base.hFeature_LSE, hBP.base.hFeature_LSE2, hBP.base.hFeature_MOPS, hBP.base.hFeature_MTE, hBP.base.hFeature_PACIMP, hBP.base.hFeature_PFAR, hBP.base.hFeature_PMULL, hBP.base.hFeature_RDM, hBP.base.hFeature_RME, hBP.base.hFeature_SB, hBP.base.hFeature_SHA1, hBP.base.hFeature_SHA256, hBP.base.hFeature_SHA3, hBP.base.hFeature_SHA512, hBP.base.hFeature_SM3, hBP.base.hFeature_SM4, hBP.base.hFeature_SME, hBP.base.hFeature_SME_F64F64, hBP.base.hFeature_SME_FA64, hBP.base.hFeature_SME_I16I64, hBP.base.hFeature_SVE, hBP.base.hFeature_SVE2, hBP.base.hFeature_SVE_AES, hBP.base.hFeature_SVE_BitPerm, hBP.base.hFeature_SVE_PMULL128, hBP.base.hFeature_SVE_SHA3, hBP.base.hFeature_SVE_SM4, hBP.base.hFeature_TME, hBP.base.hFeature_WFxT, hBP.base.hDebugBP, hBP.base.hDebugWP, hBP.base.hDebugCTX, hBP.base.hEDSCR_STATUS, hBP.base.hSPE, hBP.base.hEL, hBP.base.hnRW, hBP.base.hIL, hBP.base.hE2H, hBP.base.hTGE, hBP.base.hSCR_NS, hBP.base.hSCR_NSE, hBP.base.hMDSCR_SS, hBP.base.hPSTATE_SS, hBP.base.hOSUC, hBP.base.hPMB_E, hBP.base.hSCR_RW, hBP.base.hSCR_EEL2, hBP.base.hTBI0, hBP.base.hTBID0, hBP.base.hNSPB, hBP.base.hNSPBE⟩
  have hVHE1 : S1.regs.FeatureImpl[54] = true := by rw [← hS1]; exact hBP.vhe
  have hlow1 : tgt.toNat < 2 ^ 55 := by rw [← htgt]; exact hlow'
  rw [BR8_BranchTo.complete_pa_mte tgt BranchType.BranchType_RET false S1 hBP1.hFeature_AA32EL0 hBP1.hFeature_AA32EL1 hBP1.hFeature_AA32EL2 hBP1.hFeature_AA32EL3 hBP1.hFeature_AA64EL0 hBP1.hFeature_AA64EL1 hBP1.hFeature_AA64EL2 hBP1.hFeature_AA64EL3 hBP1.hFeature_AES hBP1.hFeature_AFP hBP1.hFeature_AdvSIMD hBP1.hFeature_BF16 hBP1.hFeature_BRBE hBP1.hFeature_BTI hBP1.hFeature_CRC32 hBP1.hFeature_DGH hBP1.hFeature_DIT hBP1.hFeature_DPB hBP1.hFeature_DPB2 hBP1.hFeature_Debugv8p9 hBP1.hFeature_DotProd hBP1.hFeature_ECV hBP1.hFeature_FCMA hBP1.hFeature_FHM hBP1.hFeature_FP hBP1.hFeature_FP16 hBP1.hFeature_FRINTTS hBP1.hFeature_FlagM hBP1.hFeature_FlagM2 hBP1.hFeature_I8MM hBP1.hFeature_JSCVT hBP1.hFeature_LRCPC hBP1.hFeature_LRCPC2 hBP1.hFeature_LSE hBP1.hFeature_LSE2 hBP1.hFeature_MOPS hBP1.hFeature_MTE hBP1.hFeature_PACIMP hBP1.hFeature_PFAR hBP1.hFeature_PMULL hBP1.hFeature_RDM hBP1.hFeature_RME hBP1.hFeature_SB hBP1.hFeature_SHA1 hBP1.hFeature_SHA256 hBP1.hFeature_SHA3 hBP1.hFeature_SHA512 hBP1.hFeature_SM3 hBP1.hFeature_SM4 hBP1.hFeature_SME hBP1.hFeature_SME_F64F64 hBP1.hFeature_SME_FA64 hBP1.hFeature_SME_I16I64 hBP1.hFeature_SVE hBP1.hFeature_SVE2 hBP1.hFeature_SVE_AES hBP1.hFeature_SVE_BitPerm hBP1.hFeature_SVE_PMULL128 hBP1.hFeature_SVE_SHA3 hBP1.hFeature_SVE_SM4 hBP1.hFeature_TME hBP1.hFeature_WFxT hBP1.hDebugBP hBP1.hDebugWP hBP1.hDebugCTX hBP1.hEDSCR_STATUS hBP1.hSPE hBP1.hEL hBP1.hnRW hBP1.hIL hBP1.hE2H hBP1.hTGE hBP1.hSCR_NS hBP1.hSCR_NSE hBP1.hMDSCR_SS hBP1.hPSTATE_SS hBP1.hOSUC hBP1.hPMB_E hBP1.hSCR_RW hBP1.hSCR_EEL2 hBP1.hTBI0 hBP1.hTBID0 hBP1.hNSPB hBP1.hNSPBE (BR8Pins.vhe_bang _ hVHE1) (BR8Pins.bit55_of_lt _ hlow1)]
  obtain ⟨u, hN, hF, hbt, hpc, hbtt⟩ := brto_obs_pa tgt BranchType.BranchType_RET false S1 hBP1 hVHE1 hlow1
  obtain ⟨u', hN', hph, hmask, hgic⟩ := extra tgt BranchType.BranchType_RET false S1 hBP1 hVHE1 hlow1
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
  have htg : tgt = (Crypto.CruxRet.spec Rn).fPC t := by first | (rw [← htgt]; done) | (rw [← htgt]; rfl)
  have hfr := frame_comp t S1 u' h1 hF
  exact ⟨u', hN', hfr, hF.mem.trans hS1m, hF.events.trans hS1e, hfr.btn, hpc.trans htg, hbt,
    hph.trans hS1c, hmask.trans hS1k, hgic.trans hS1g, by rw [hbtt]; exact fun h => BranchType.noConfusion h,
    hF.gpr.trans (by rw [← hS1]), hF.sp.trans (by rw [← hS1]),
    hF.pstate.trans (by rw [← hS1])⟩

#print axioms run

open ArmBridge.CruxCore ArmBridge.CruxGen
theorem base_step (s fin : SequentialState Regs oracleChoiceSource) (h : Base s)
    (hsys : SysEq2 s.regs fin.regs) (hp : StepPins fin) (hbr : BrSysEq s.regs fin.regs) : Base fin where
  hFeature_AA32EL0 := by rw [hsys.feat]; exact h.hFeature_AA32EL0
  hFeature_AA32EL1 := by rw [hsys.feat]; exact h.hFeature_AA32EL1
  hFeature_AA32EL2 := by rw [hsys.feat]; exact h.hFeature_AA32EL2
  hFeature_AA32EL3 := by rw [hsys.feat]; exact h.hFeature_AA32EL3
  hFeature_AA64EL0 := by rw [hsys.feat]; exact h.hFeature_AA64EL0
  hFeature_AA64EL1 := by rw [hsys.feat]; exact h.hFeature_AA64EL1
  hFeature_AA64EL2 := by rw [hsys.feat]; exact h.hFeature_AA64EL2
  hFeature_AA64EL3 := by rw [hsys.feat]; exact h.hFeature_AA64EL3
  hFeature_AES := by rw [hsys.feat]; exact h.hFeature_AES
  hFeature_AFP := by rw [hsys.feat]; exact h.hFeature_AFP
  hFeature_AdvSIMD := by rw [hsys.feat]; exact h.hFeature_AdvSIMD
  hFeature_BF16 := by rw [hsys.feat]; exact h.hFeature_BF16
  hFeature_BRBE := by rw [hsys.feat]; exact h.hFeature_BRBE
  hFeature_BTI := by rw [hsys.feat]; exact h.hFeature_BTI
  hFeature_CRC32 := by rw [hsys.feat]; exact h.hFeature_CRC32
  hFeature_DGH := by rw [hsys.feat]; exact h.hFeature_DGH
  hFeature_DIT := by rw [hsys.feat]; exact h.hFeature_DIT
  hFeature_DPB := by rw [hsys.feat]; exact h.hFeature_DPB
  hFeature_DPB2 := by rw [hsys.feat]; exact h.hFeature_DPB2
  hFeature_Debugv8p9 := by rw [hsys.feat]; exact h.hFeature_Debugv8p9
  hFeature_DotProd := by rw [hsys.feat]; exact h.hFeature_DotProd
  hFeature_ECV := by rw [hsys.feat]; exact h.hFeature_ECV
  hFeature_FCMA := by rw [hsys.feat]; exact h.hFeature_FCMA
  hFeature_FHM := by rw [hsys.feat]; exact h.hFeature_FHM
  hFeature_FP := by rw [hsys.feat]; exact h.hFeature_FP
  hFeature_FP16 := by rw [hsys.feat]; exact h.hFeature_FP16
  hFeature_FRINTTS := by rw [hsys.feat]; exact h.hFeature_FRINTTS
  hFeature_FlagM := by rw [hsys.feat]; exact h.hFeature_FlagM
  hFeature_FlagM2 := by rw [hsys.feat]; exact h.hFeature_FlagM2
  hFeature_I8MM := by rw [hsys.feat]; exact h.hFeature_I8MM
  hFeature_JSCVT := by rw [hsys.feat]; exact h.hFeature_JSCVT
  hFeature_LRCPC := by rw [hsys.feat]; exact h.hFeature_LRCPC
  hFeature_LRCPC2 := by rw [hsys.feat]; exact h.hFeature_LRCPC2
  hFeature_LSE := by rw [hsys.feat]; exact h.hFeature_LSE
  hFeature_LSE2 := by rw [hsys.feat]; exact h.hFeature_LSE2
  hFeature_MOPS := by rw [hsys.feat]; exact h.hFeature_MOPS
  hFeature_MTE := by rw [hsys.feat]; exact h.hFeature_MTE
  hFeature_PACIMP := by rw [hsys.feat]; exact h.hFeature_PACIMP
  hFeature_PFAR := by rw [hsys.feat]; exact h.hFeature_PFAR
  hFeature_PMULL := by rw [hsys.feat]; exact h.hFeature_PMULL
  hFeature_RDM := by rw [hsys.feat]; exact h.hFeature_RDM
  hFeature_RME := by rw [hsys.feat]; exact h.hFeature_RME
  hFeature_SB := by rw [hsys.feat]; exact h.hFeature_SB
  hFeature_SHA1 := by rw [hsys.feat]; exact h.hFeature_SHA1
  hFeature_SHA256 := by rw [hsys.feat]; exact h.hFeature_SHA256
  hFeature_SHA3 := by rw [hsys.feat]; exact h.hFeature_SHA3
  hFeature_SHA512 := by rw [hsys.feat]; exact h.hFeature_SHA512
  hFeature_SM3 := by rw [hsys.feat]; exact h.hFeature_SM3
  hFeature_SM4 := by rw [hsys.feat]; exact h.hFeature_SM4
  hFeature_SME := by rw [hsys.feat]; exact h.hFeature_SME
  hFeature_SME_F64F64 := by rw [hsys.feat]; exact h.hFeature_SME_F64F64
  hFeature_SME_FA64 := by rw [hsys.feat]; exact h.hFeature_SME_FA64
  hFeature_SME_I16I64 := by rw [hsys.feat]; exact h.hFeature_SME_I16I64
  hFeature_SVE := by rw [hsys.feat]; exact h.hFeature_SVE
  hFeature_SVE2 := by rw [hsys.feat]; exact h.hFeature_SVE2
  hFeature_SVE_AES := by rw [hsys.feat]; exact h.hFeature_SVE_AES
  hFeature_SVE_BitPerm := by rw [hsys.feat]; exact h.hFeature_SVE_BitPerm
  hFeature_SVE_PMULL128 := by rw [hsys.feat]; exact h.hFeature_SVE_PMULL128
  hFeature_SVE_SHA3 := by rw [hsys.feat]; exact h.hFeature_SVE_SHA3
  hFeature_SVE_SM4 := by rw [hsys.feat]; exact h.hFeature_SVE_SM4
  hFeature_TME := by rw [hsys.feat]; exact h.hFeature_TME
  hFeature_WFxT := by rw [hsys.feat]; exact h.hFeature_WFxT
  hDebugBP := by rw [hbr.nbp]; exact h.hDebugBP
  hDebugWP := by rw [hbr.nwp]; exact h.hDebugWP
  hDebugCTX := by rw [hbr.nctx]; exact h.hDebugCTX
  hEDSCR_STATUS := hp.st
  hSPE := hp.spe
  hEL := hp.el
  hnRW := hp.nrw
  hIL := hp.il
  hE2H := by rw [hsys.hcr]; exact h.hE2H
  hTGE := by rw [hsys.hcr]; exact h.hTGE
  hSCR_NS := by rw [hsys.scr]; exact h.hSCR_NS
  hSCR_NSE := by rw [hsys.scr]; exact h.hSCR_NSE
  hMDSCR_SS := by rw [hsys.mdscr]; exact h.hMDSCR_SS
  hPSTATE_SS := hp.pss
  hOSUC := by rw [hp.edesr]; rfl
  hPMB_E := hp.pmbe
  hSCR_RW := by rw [hsys.scr]; exact h.hSCR_RW
  hSCR_EEL2 := by rw [hsys.scr]; exact h.hSCR_EEL2
  hTBI0 := by rw [hsys.tcr]; exact h.hTBI0
  hTBID0 := by rw [hsys.tcr]; exact h.hTBID0
  hNSPB := by rw [hbr.mdcr3]; exact h.hNSPB
  hNSPBE := by rw [hbr.mdcr3]; exact h.hNSPBE

/-- BranchPinsV2PA (BranchPinsPA + FEAT_VHE + FEAT_GCS off) persists along a crux4.1 run (eval, heap-crux v2 Pins2). -/
theorem pins_step (s fin : SequentialState Regs oracleChoiceSource) (h : Pins s)
    (hsys : SysEq2 s.regs fin.regs) (hp : StepPins fin) (hbr : BrSysEq s.regs fin.regs) : Pins fin :=
  ⟨base_step s fin h.base hsys hp hbr, by rw [hsys.feat]; exact h.vhe, by rw [hsys.feat]; exact h.gcs⟩


#print axioms base_step
#print axioms pins_step
end TranslateSpan.BranchMTE2
