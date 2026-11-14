import Walk.S1EL10PermsCallees
import Walk.S1EL2Enabled
import GetEntry.PrefixCallees
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
namespace ArmCert.Eval.JointSAT.Regime
/- Source copy (own build, no peer objects) of armcert-memory MemM1.Callees
   el3a32/el2a32/el2en/host0/css/regime_el0 (memory m1/ws/MemM1/Callees.lean a8a2f0a7,
   NoFault.frame_trans), credited to armcert-memory; used to tie ProfileEL20 to the
   actual EL0 translation regime (defects 9239). -/
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

theorem frame_trans {s t u : State} (h1 : S1Normality.Frame s t) (h2 : S1Normality.Frame t u) :
    S1Normality.Frame s u :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

drive_spec el3a32_native, el3a32_eq : fun (s : State) => ELUsingAArch32 EL3 s

theorem el3a32 (s : State) : ∃ t, ELUsingAArch32 EL3 s = .ok false t ∧ Frame s t := by
  rw [el3a32_eq]
  observe_simp [Frame, el3a32_native]

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
#print axioms regime_el0
end ArmCert.Eval.JointSAT.Regime
