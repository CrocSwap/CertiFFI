-- Chain lever 1: THE B.cond observation over the weakest pin bundle (TranslateSpan.BranchMTE2.Base),
-- in a light module. Crypto/SDKPA/BcondAction consumers derive from it (no repeated observe_simp). Name unchanged.
import TranslateSpan.BrToRwMTE
import TranslateSpan.BranchMTE2Base
import Crypto.BranchDefs
import Crypto.BcondDecode
import Crypto.Tac
import Crypto.Tac2
import Crypto.BrSimp
import Pilot.ObservationSimp
import Bridge.StepM
import BR8.BCond
import Bridge.CruxGenBrDefs
-- Actual B.cond action with no MTE2 premise.
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace ReleaseProfile.BcondAction
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.BcondDec Crypto.BcondCore
attribute [local instance 10] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 512
set_option Elab.async false


#check "CURRENT_DECL bcond_obs_current"
set_option maxHeartbeats 4000000 in
theorem bcond_obs_current (real : Type) [Sail.SailReal real] (cond : BitVec 4) (imm19 : BitVec 19) (S0 : SequentialState Regs oracleChoiceSource)
    (hBP : TranslateSpan.BranchMTE2.Base S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_BCondH.native real cond imm19 (bcondWord imm19 cond) (-1) S0 = .ok () t ∧ BrFrame S0 t ∧
      ((bcondC cond S0.regs ∧ t.regs.__BranchTaken = true ∧ t.regs._PC = S0.regs._PC + sign_extend (imm19 ++ 0#2) 64 ∧ t.regs.Branchtypetaken ≠ BranchType.BranchType_RESET) ∨
       (¬ bcondC cond S0.regs ∧ t.regs.__BranchTaken = S0.regs.__BranchTaken ∧ t.regs._PC = S0.regs._PC ∧ t.regs.Branchtypetaken = S0.regs.Branchtypetaken)) := by
  have hNS : Sail.BitVec.extractLsb (Mk_SCRType (S0.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3)) 0 0 = 1#1 := hBP.hSCR_NS
  have hb55 := Crypto.BrSimp.b55_false _ hlow
  have gi := Crypto.BrSimp.gi259
  have f0 : S0.regs.FeatureImpl[0] = false := by simpa [getElem!_def] using hBP.hFeature_AA32EL0
  have f1 : S0.regs.FeatureImpl[1] = false := by simpa [getElem!_def] using hBP.hFeature_AA32EL1
  have f2 : S0.regs.FeatureImpl[2] = false := by simpa [getElem!_def] using hBP.hFeature_AA32EL2
  have f3 : S0.regs.FeatureImpl[3] = false := by simpa [getElem!_def] using hBP.hFeature_AA32EL3
  have f4 : S0.regs.FeatureImpl[4] = true := by simpa [getElem!_def] using hBP.hFeature_AA64EL0
  have f5 : S0.regs.FeatureImpl[5] = true := by simpa [getElem!_def] using hBP.hFeature_AA64EL1
  have f6 : S0.regs.FeatureImpl[6] = true := by simpa [getElem!_def] using hBP.hFeature_AA64EL2
  have f7 : S0.regs.FeatureImpl[7] = true := by simpa [getElem!_def] using hBP.hFeature_AA64EL3
  have f12 : S0.regs.FeatureImpl[12] = true := by simpa [getElem!_def] using hBP.hFeature_AES
  have f153 : S0.regs.FeatureImpl[153] = true := by simpa [getElem!_def] using hBP.hFeature_AFP
  have f13 : S0.regs.FeatureImpl[13] = true := by simpa [getElem!_def] using hBP.hFeature_AdvSIMD
  have f143 : S0.regs.FeatureImpl[143] = true := by simpa [getElem!_def] using hBP.hFeature_BF16
  have f230 : S0.regs.FeatureImpl[230] = false := by simpa [getElem!_def] using hBP.hFeature_BRBE
  have f123 : S0.regs.FeatureImpl[123] = true := by simpa [getElem!_def] using hBP.hFeature_BTI
  have f45 : S0.regs.FeatureImpl[45] = true := by simpa [getElem!_def] using hBP.hFeature_CRC32
  have f144 : S0.regs.FeatureImpl[144] = true := by simpa [getElem!_def] using hBP.hFeature_DGH
  have f103 : S0.regs.FeatureImpl[103] = true := by simpa [getElem!_def] using hBP.hFeature_DIT
  have f60 : S0.regs.FeatureImpl[60] = true := by simpa [getElem!_def] using hBP.hFeature_DPB
  have f126 : S0.regs.FeatureImpl[126] = true := by simpa [getElem!_def] using hBP.hFeature_DPB2
  have f185 : S0.regs.FeatureImpl[185] = false := by simpa [getElem!_def] using hBP.hFeature_Debugv8p9
  have f105 : S0.regs.FeatureImpl[105] = true := by simpa [getElem!_def] using hBP.hFeature_DotProd
  have f145 : S0.regs.FeatureImpl[145] = true := by simpa [getElem!_def] using hBP.hFeature_ECV
  have f89 : S0.regs.FeatureImpl[89] = true := by simpa [getElem!_def] using hBP.hFeature_FCMA
  have f107 : S0.regs.FeatureImpl[107] = true := by simpa [getElem!_def] using hBP.hFeature_FHM
  have f27 : S0.regs.FeatureImpl[27] = true := by simpa [getElem!_def] using hBP.hFeature_FP
  have f65 : S0.regs.FeatureImpl[65] = true := by simpa [getElem!_def] using hBP.hFeature_FP16
  have f130 : S0.regs.FeatureImpl[130] = true := by simpa [getElem!_def] using hBP.hFeature_FRINTTS
  have f108 : S0.regs.FeatureImpl[108] = true := by simpa [getElem!_def] using hBP.hFeature_FlagM
  have f131 : S0.regs.FeatureImpl[131] = true := by simpa [getElem!_def] using hBP.hFeature_FlagM2
  have f67 : S0.regs.FeatureImpl[67] = true := by simpa [getElem!_def] using hBP.hFeature_I8MM
  have f92 : S0.regs.FeatureImpl[92] = true := by simpa [getElem!_def] using hBP.hFeature_JSCVT
  have f93 : S0.regs.FeatureImpl[93] = true := by simpa [getElem!_def] using hBP.hFeature_LRCPC
  have f110 : S0.regs.FeatureImpl[110] = true := by simpa [getElem!_def] using hBP.hFeature_LRCPC2
  have f50 : S0.regs.FeatureImpl[50] = true := by simpa [getElem!_def] using hBP.hFeature_LSE
  have f111 : S0.regs.FeatureImpl[111] = true := by simpa [getElem!_def] using hBP.hFeature_LSE2
  have f171 : S0.regs.FeatureImpl[171] = false := by simpa [getElem!_def] using hBP.hFeature_MOPS
  have f133 : S0.regs.FeatureImpl[133] = true := by simpa [getElem!_def] using hBP.hFeature_MTE
  have f95 : S0.regs.FeatureImpl[95] = false := by simpa [getElem!_def] using hBP.hFeature_PACIMP
  have f200 : S0.regs.FeatureImpl[200] = false := by simpa [getElem!_def] using hBP.hFeature_PFAR
  have f36 : S0.regs.FeatureImpl[36] = true := by simpa [getElem!_def] using hBP.hFeature_PMULL
  have f53 : S0.regs.FeatureImpl[53] = true := by simpa [getElem!_def] using hBP.hFeature_RDM
  have f232 : S0.regs.FeatureImpl[232] = false := by simpa [getElem!_def] using hBP.hFeature_RME
  have f138 : S0.regs.FeatureImpl[138] = true := by simpa [getElem!_def] using hBP.hFeature_SB
  have f40 : S0.regs.FeatureImpl[40] = true := by simpa [getElem!_def] using hBP.hFeature_SHA1
  have f41 : S0.regs.FeatureImpl[41] = true := by simpa [getElem!_def] using hBP.hFeature_SHA256
  have f76 : S0.regs.FeatureImpl[76] = true := by simpa [getElem!_def] using hBP.hFeature_SHA3
  have f77 : S0.regs.FeatureImpl[77] = true := by simpa [getElem!_def] using hBP.hFeature_SHA512
  have f78 : S0.regs.FeatureImpl[78] = true := by simpa [getElem!_def] using hBP.hFeature_SM3
  have f79 : S0.regs.FeatureImpl[79] = true := by simpa [getElem!_def] using hBP.hFeature_SM4
  have f233 : S0.regs.FeatureImpl[233] = false := by simpa [getElem!_def] using hBP.hFeature_SME
  have f234 : S0.regs.FeatureImpl[234] = false := by simpa [getElem!_def] using hBP.hFeature_SME_F64F64
  have f235 : S0.regs.FeatureImpl[235] = false := by simpa [getElem!_def] using hBP.hFeature_SME_FA64
  have f236 : S0.regs.FeatureImpl[236] = false := by simpa [getElem!_def] using hBP.hFeature_SME_I16I64
  have f81 : S0.regs.FeatureImpl[81] = true := by simpa [getElem!_def] using hBP.hFeature_SVE
  have f221 : S0.regs.FeatureImpl[221] = true := by simpa [getElem!_def] using hBP.hFeature_SVE2
  have f222 : S0.regs.FeatureImpl[222] = true := by simpa [getElem!_def] using hBP.hFeature_SVE_AES
  have f223 : S0.regs.FeatureImpl[223] = true := by simpa [getElem!_def] using hBP.hFeature_SVE_BitPerm
  have f224 : S0.regs.FeatureImpl[224] = true := by simpa [getElem!_def] using hBP.hFeature_SVE_PMULL128
  have f225 : S0.regs.FeatureImpl[225] = true := by simpa [getElem!_def] using hBP.hFeature_SVE_SHA3
  have f226 : S0.regs.FeatureImpl[226] = true := by simpa [getElem!_def] using hBP.hFeature_SVE_SM4
  have f227 : S0.regs.FeatureImpl[227] = false := by simpa [getElem!_def] using hBP.hFeature_TME
  have f165 : S0.regs.FeatureImpl[165] = true := by simpa [getElem!_def] using hBP.hFeature_WFxT
  observe_simp [BR_BCondH.native]
  rw [TranslateSpan.BrToRwMTE.brto_rw_mte ?hb (hV := ?hv) (hlow := ?hl)]
  case hb => exact { hBP with }
  case hv => exact hVHE
  case hl => exact hlow
  observe_simp [BR8_BranchTo.native]
  simp only [Crypto.BrSimp.tt_ff, Crypto.BrSimp.tt_ff2, Crypto.BrSimp.idx_55_63, ite_true, ite_false,
    dite_true, dite_false]
  simp (config := {maxSteps := 2000000}) only [Crypto.BrSimp.ok_ite, Crypto.BrSimp.ok_dite, Crypto.BrSimp.ok_exists]
  by_cases hC : bcondC cond S0.regs
  · have hC2 := hC
    unfold bcondC at hC2
    rw [if_pos hC2]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inl ⟨hC, ?_, ?_, ?_⟩⟩
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
  · have hC2 := hC
    unfold bcondC at hC2
    rw [if_neg hC2]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr ⟨hC, ?_, ?_, ?_⟩⟩
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

#check "CURRENT_DECL extra"
end ReleaseProfile.BcondAction
