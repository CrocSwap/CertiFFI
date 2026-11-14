import MemM1.NoFault
import Walk.S1EL10PermsCallees
import GetEntry.PrefixCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
namespace MemM1.Callees
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault

/-- FEAT_RME is bit 232 of FeatureImpl (num_of_Feature FEAT_RME = 232). -/
theorem rme (s : State) (hR : s.regs.FeatureImpl[232] = false) :
    HaveRME () s = .ok false s := by
  have hR' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_RME)]! = false := hR
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_RME)]! s = _
  rw [hR']

drive_spec tsi_native, tsi_eq : fun (ss : SecurityState) (acc : AccessDescriptor) (va : BitVec 64) (size : Int)
  (s : State) => AArch64_GetTranslationStartInfo .Regime_EL20 ss acc va size s

theorem tsi (ss : SecurityState) (acc : AccessDescriptor) (va : BitVec 64) (size : Int) :
    Normal (AArch64_GetTranslationStartInfo .Regime_EL20 ss acc va size) := by
  intro s
  rw [tsi_eq]
  observe_simp [Frame, tsi_native]
  exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

drive_spec el3a32_native, el3a32_eq : fun (s : State) => ELUsingAArch32 EL3 s
drive_spec el2a32_native, el2a32_eq : fun (s : State) => ELUsingAArch32 EL2 s

theorem el3a32 (s : State) : ∃ t, ELUsingAArch32 EL3 s = .ok false t ∧ Frame s t := by
  rw [el3a32_eq]
  observe_simp [Frame, el3a32_native]

theorem el2a32 (s : State) : ∃ t, ELUsingAArch32 EL2 s = .ok false t ∧ Frame s t := by
  rw [el2a32_eq]
  observe_simp [Frame, el2a32_native]

theorem el2en (s : State) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    ∃ t, EL2Enabled () s = .ok true t ∧ Frame s t := by
  rw [S1EL2Enabled.complete]
  observe_simp [Frame, S1EL2Enabled.native, Mk_SCRType]

drive_spec host0_native, host0_eq : fun (s : State) => ELIsInHost 0#2 s

theorem host0 (s : State) (hVHE : s.regs.FeatureImpl[54] = true) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1) :
    ∃ t, ELIsInHost 0#2 s = .ok true t ∧ Frame s t := by
  rw [host0_eq]
  observe_simp [Frame, host0_native, Mk_SCRType]

theorem css (s : State) (hR : s.regs.FeatureImpl[232] = false) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    ∃ x t, CurrentSecurityState () s = .ok x t ∧ Frame s t := by
  have hR' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_RME)]! = false := hR
  rcases occ_normal 503 s with ⟨l, s1, h1, f1⟩
  rcases bits_normal 2 l s1 with ⟨b, s2, h2, f2⟩
  have f02 := frame_trans f1 f2
  rcases el3a32 s2 with ⟨s3, h3, f3⟩
  have f03 := frame_trans f02 f3
  unfold CurrentSecurityState SecurityStateAtEL
  simp only [SailME.run, h1, h2, PreSail.readReg_apply, f02.1, hR', Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, MonadLiftT.monadLift, ExceptT.lift, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
    EStateM.map, Functor.map, readReg, HaveRME, IsFeatureImplemented, HaveEL]
  by_cases hE3 : ((Register.PSTATE.get s.regs).EL == EL3) = true
  · simp only [hE3, ↓reduceIte]
    exact ⟨_, _, rfl, f02⟩
  · simp only [hE3, Bool.false_eq_true, ↓reduceIte]
    by_cases hE2 : ((Register.PSTATE.get s.regs).EL != EL2) = true
    · simp only [hE2, h3, PreSail.readReg_apply, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false,
        PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift,
        MonadLift.monadLift, MonadLiftT.monadLift, ExceptT.lift, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
        EStateM.map, Functor.map, readReg, PreSail.assert, ArmFull.assert]
      exact ⟨_, _, rfl, f03⟩
    · rcases el2en s2 (f02.1 ▸ hAA) (f02.1 ▸ hNS) with ⟨s4, h4, f4⟩
      rcases el3a32 s4 with ⟨s5, h5, f5⟩
      simp only [hE2, h4, h5, PreSail.readReg_apply, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false,
        PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift,
        MonadLift.monadLift, MonadLiftT.monadLift, ExceptT.lift, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
        EStateM.map, Functor.map, readReg, PreSail.assert, ArmFull.assert]
      exact ⟨_, _, rfl, frame_trans (frame_trans f02 f4) f5⟩

/-- EL0 translation regime is EL2&0 under register facts:
FEAT_RME off (bit 232), FEAT_VHE on (bit 54), FEAT_AA64EL0 on (bit 4, makes HaveAArch64 true so
SCR_GEN_read reads SCR_EL3), SCR_EL3.NS = 1, HCR_EL2.E2H (bit 34) = 1, HCR_EL2.TGE (bit 27) = 1.
The result state differs from `s` only in choice bookkeeping (draws inside the callees). -/
theorem regime_el0 (s : State) (hR : s.regs.FeatureImpl[232] = false)
    (hVHE : s.regs.FeatureImpl[54] = true) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1) :
    ∃ t, TranslationRegime 0#2 s = .ok .Regime_EL20 t ∧ Frame s t := by
  rcases css s hR hAA hNS with ⟨x, s1, h1, f1⟩
  have e3 : ((0#2 : BitVec 2) == EL3) = false := rfl
  have e2 : ((0#2 : BitVec 2) == EL2) = false := rfl
  have e1 : ((0#2 : BitVec 2) == EL1) = false := rfl
  have e0 : ((0#2 : BitVec 2) == EL0) = true := rfl
  unfold TranslationRegime
  simp only [e3, e2, e1, e0, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, h1]
  have hw : ∃ s2, (if (x == SecurityState.SS_Secure) = true then ELUsingAArch32 EL3 else EStateM.pure false) s1
      = .ok false s2 ∧ Frame s1 s2 := by
    split
    · exact el3a32 s1
    · exact ⟨s1, rfl, rfl, rfl, rfl⟩
  rcases hw with ⟨s2, h2, f2⟩
  have f02 := frame_trans f1 f2
  rcases host0 s2 (f02.1 ▸ hVHE) (f02.1 ▸ hAA) (f02.1 ▸ hNS) (f02.1 ▸ hE2H) (f02.1 ▸ hTGE)
    with ⟨s3, h3, f3⟩
  have h3' : ELIsInHost EL0 s2 = .ok true s3 := h3
  simp only [h2, h3', Bool.false_eq_true, ↓reduceIte, EStateM.bind, EStateM.pure]
  exact ⟨s3, rfl, frame_trans f02 f3⟩
#print axioms rme
#print axioms tsi
#print axioms regime_el0
end MemM1.Callees
