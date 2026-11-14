import NativeMteTagCheck.TagCheck
import NativeMte2.Prepare
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace NativeMteTagCheck.StatusTrace
abbrev State := NativeMteTagCheck.State
def TraceFrame (s t : State) : Prop :=
  t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events ∧ ChoiceDelta s t 0
theorem to_frame {s t : State} (h : TraceFrame s t) : S1Normality.Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1⟩
theorem frame_trans {s t u : State} (a : TraceFrame s t) (b : TraceFrame t u) :
    TraceFrame s u := by
  exact ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1,
    choice_delta_trans a.2.2.2 b.2.2.2⟩
theorem occ_trace (site : Nat) (s : State) (different : site ≠ 1354) :
    ∃ label t, (occLabel site : SailM ChoiceLabel) s = .ok label t ∧ TraceFrame s t := by
  refine ⟨_, _, occurrence site s, rfl, rfl, rfl, rfl, ?_⟩
  simp [advanceOcc, Std.ExtHashMap.getD_insert, different, Ne.symm different]
theorem bits_trace (width : Nat) (label : ChoiceLabel) (s : State) :
    ∃ bits t, undefined_bitvector_at label width s = .ok bits t ∧ TraceFrame s t := by
  obtain ⟨bits, run⟩ := S1Unknowns.bits_at_total width label s
  exact ⟨bits, s, run, rfl, rfl, rfl, choice_delta_refl s⟩
namespace Callees

theorem el3a32 (s : State) : ∃ t, ELUsingAArch32 EL3 s = .ok false t ∧ TraceFrame s t := by
  rw [MemM1.Callees.el3a32_eq]
  observe_simp [TraceFrame, S1Normality.Frame, ChoiceDelta, Std.ExtHashMap.getD_insert, MemM1.Callees.el3a32_native]
  all_goals simp [Std.ExtHashMap.getD_insert]

theorem el2a32 (s : State) : ∃ t, ELUsingAArch32 EL2 s = .ok false t ∧ TraceFrame s t := by
  rw [MemM1.Callees.el2a32_eq]
  observe_simp [TraceFrame, S1Normality.Frame, ChoiceDelta, Std.ExtHashMap.getD_insert, MemM1.Callees.el2a32_native]
  all_goals simp [Std.ExtHashMap.getD_insert]

theorem el2en (s : State) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    ∃ t, EL2Enabled () s = .ok true t ∧ TraceFrame s t := by
  rw [S1EL2Enabled.complete]
  observe_simp [TraceFrame, S1Normality.Frame, ChoiceDelta, Std.ExtHashMap.getD_insert, S1EL2Enabled.native, Mk_SCRType]
  all_goals simp [Std.ExtHashMap.getD_insert]


theorem host0 (s : State) (hVHE : s.regs.FeatureImpl[54] = true) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1) :
    ∃ t, ELIsInHost 0#2 s = .ok true t ∧ TraceFrame s t := by
  rw [MemM1.Callees.host0_eq]
  observe_simp [TraceFrame, S1Normality.Frame, ChoiceDelta, Std.ExtHashMap.getD_insert, MemM1.Callees.host0_native, Mk_SCRType]
  all_goals simp [Std.ExtHashMap.getD_insert]

theorem css (s : State) (hR : s.regs.FeatureImpl[232] = false) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    ∃ x t, CurrentSecurityState () s = .ok x t ∧ TraceFrame s t := by
  have hR' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_RME)]! = false := hR
  rcases occ_trace 503 s (by decide) with ⟨l, s1, h1, f1⟩
  rcases bits_trace 2 l s1 with ⟨b, s2, h2, f2⟩
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
    ∃ t, TranslationRegime 0#2 s = .ok .Regime_EL20 t ∧ TraceFrame s t := by
  rcases css s hR hAA hNS with ⟨x, s1, h1, f1⟩
  have e3 : ((0#2 : BitVec 2) == EL3) = false := rfl
  have e2 : ((0#2 : BitVec 2) == EL2) = false := rfl
  have e1 : ((0#2 : BitVec 2) == EL1) = false := rfl
  have e0 : ((0#2 : BitVec 2) == EL0) = true := rfl
  unfold TranslationRegime
  simp only [e3, e2, e1, e0, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, h1]
  have hw : ∃ s2, (if (x == SecurityState.SS_Secure) = true then ELUsingAArch32 EL3 else EStateM.pure false) s1
      = .ok false s2 ∧ TraceFrame s1 s2 := by
    split
    · exact el3a32 s1
    · exact ⟨s1, rfl, rfl, rfl, rfl, choice_delta_refl s1⟩
  rcases hw with ⟨s2, h2, f2⟩
  have f02 := frame_trans f1 f2
  rcases host0 s2 (f02.1 ▸ hVHE) (f02.1 ▸ hAA) (f02.1 ▸ hNS) (f02.1 ▸ hE2H) (f02.1 ▸ hTGE)
    with ⟨s3, h3, f3⟩
  have h3' : ELIsInHost EL0 s2 = .ok true s3 := h3
  simp only [h2, h3', Bool.false_eq_true, ↓reduceIte, EStateM.bind, EStateM.pure]
  exact ⟨s3, rfl, frame_trans f02 f3⟩

end Callees

open NativeMte2
theorem transport_host {s t : State} (h : HostPins s) (f : TraceFrame s t) : HostPins t :=
  h.transport (to_frame f)
theorem transport_default {s t : State} {catalogue : ControlCatalogue}
    (h : DefaultAt catalogue s) (f : TraceFrame s t) : DefaultAt catalogue t :=
  h.transport (to_frame f)
theorem bit1 (site : Nat) (s : State) (different : site ≠ 1354) :
    ∃ b t, ((do let label ← occLabel site; undefined_bitvector_at label 1) : SailM (BitVec 1)) s =
      .ok b t ∧ TraceFrame s t := by
  obtain ⟨label, u, hl, fl⟩ := occ_trace site s different
  obtain ⟨b, t, hb, fb⟩ := bits_trace 1 label u
  exact ⟨b, t, by simp only [Bind.bind, EStateM.bind, hl, hb], frame_trans fl fb⟩
theorem nofault (acc : AccessDescriptor) (s : State) :
    ∃ f t, NoFault__1 acc s = .ok f t ∧ f.statuscode = .Fault_None ∧ TraceFrame s t := by
  unfold NoFault__1 GPCNoFault
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    UndefSummaries.GPCFRecord_eq, UndefSummaries.FaultRecord_eq]
  delta UndefSummaries.GPCFRecord_native UndefSummaries.FaultRecord_native
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [Std.ExtHashMap.getD_insert]
private theorem ns_bit (s : State) (h : HostPins s) :
    Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .SCR_EL3) 0 0 = 1#1 := by
  simpa only [_get_SCR_EL3_Type_NS, Sail.BitVec.castWidth_eq] using h.ns

private theorem e2h_bit (s : State) (h : HostPins s) :
    Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .HCR_EL2) 34 34 = 1#1 := by
  simpa only [_get_HCR_EL2_Type_E2H,Sail.BitVec.castWidth_eq] using h.e2h

private theorem tge_bit (s : State) (h : HostPins s) :
    Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .HCR_EL2) 27 27 = 1#1 := by
  simpa only [_get_HCR_EL2_Type_TGE,Sail.BitVec.castWidth_eq] using h.tge

theorem host0 (s : State) (h : HostPins s) : ∃ t, ELIsInHost EL0 s = .ok true t ∧ TraceFrame s t :=
  Callees.host0 s (by simpa using h.vhe) (by simpa using h.aa64)
    (ns_bit s h) (e2h_bit s h) (tge_bit s h)

theorem regime20 (s : State) (h : HostPins s) :
    ∃ t, TranslationRegime EL0 s = .ok .Regime_EL20 t ∧ TraceFrame s t :=
  Callees.regime_el0 s (by simpa using h.rme) (by simpa using h.vhe)
    (by simpa using h.aa64) (ns_bit s h) (e2h_bit s h) (tge_bit s h)

theorem vhe_on (s : State) (h : HostPins s) : HaveVirtHostExt () s = .ok true s := by
  change EStateM.Result.ok s.regs.FeatureImpl[54]! s = _
  rw [h.vhe]

theorem s1_regime2 (s : State) (h : HostPins s) :
    ∃ t, S1TranslationRegime EL0 s = .ok EL2 t ∧ TraceFrame s t := by
  obtain ⟨u,hu,fu⟩ := Callees.el3a32 s
  obtain ⟨t,ht,ft⟩ := host0 u (transport_host h fu)
  refine ⟨t,?_,frame_trans fu ft⟩
  unfold S1TranslationRegime
  simp only [HaveEL,hu,vhe_on u (transport_host h fu),ht,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    bne_self_eq_false,Bool.false_eq_true,ite_true,ite_false]

private theorem el2_ne_el1 : (EL2 == EL1) = false := rfl

theorem tcma_frame (a : BitVec 64) (s : State) (h : HostPins s) :
    ∃ b t, EffectiveTCMA a EL0 s = .ok b t ∧ TraceFrame s t := by
  obtain ⟨_,u,hu,fu⟩ := bit1 740 s (by decide)
  obtain ⟨v,hv,fv⟩ := s1_regime2 u (transport_host h fu)
  obtain ⟨w,hw,fw⟩ := Callees.el2a32 v
  have fsw := frame_trans (frame_trans fu fv) fw
  obtain ⟨t,ht,ft⟩ := host0 w (transport_host h fsw)
  simp only [Bind.bind,EStateM.bind] at hu
  unfold EffectiveTCMA
  simp only [hu,hv,hw,ht,vhe_on w (transport_host h fsw),HaveEL,ArmFull.assert,PreSail.assert,
    Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,el2_ne_el1,beq_self_eq_true,
    Bool.not_false,Bool.false_eq_true,↓reduceIte,ite_true,ite_false]
  split <;> exact ⟨_,t,rfl,frame_trans fsw ft⟩

theorem mtx_frame (a : BitVec 64) (s : State) (h : HostPins s) :
    ∃ b t, EffectiveMTX a false EL0 s = .ok b t ∧ TraceFrame s t := by
  obtain ⟨_,u,hu,fu⟩ := bit1 741 s (by decide)
  obtain ⟨v,hv,fv⟩ := s1_regime2 u (transport_host h fu)
  obtain ⟨w,hw,fw⟩ := Callees.el2a32 v
  have fsw := frame_trans (frame_trans fu fv) fw
  obtain ⟨m,hm⟩ : ∃ m, HaveMTE4Ext () w = .ok m w := ⟨_,rfl⟩
  obtain ⟨t,ht,ft⟩ := host0 w (transport_host h fsw)
  simp only [Bind.bind,EStateM.bind] at hu
  unfold EffectiveMTX
  cases m
  · simp only [hu,hv,hw,hm,HaveEL,ArmFull.assert,PreSail.assert,Bind.bind,EStateM.bind,
      Pure.pure,EStateM.pure,Bool.not_false,Bool.true_or,↓reduceIte,ite_true]
    exact ⟨0#1,w,rfl,fsw⟩
  · simp only [hu,hv,hw,hm,ht,vhe_on w (transport_host h fsw),HaveEL,ArmFull.assert,PreSail.assert,
      Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,el2_ne_el1,beq_self_eq_true,
      Bool.not_false,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte,ite_true,ite_false]
    split <;> exact ⟨_,t,rfl,frame_trans fsw ft⟩

theorem tbi_frame (a : BitVec 64) (s : State) (h : HostPins s) :
    ∃ b t, EffectiveTBI a false EL0 s = .ok b t ∧ TraceFrame s t := by
  obtain ⟨_,u,hu,fu⟩ := bit1 567 s (by decide)
  obtain ⟨_,v,hv,fv⟩ := bit1 568 u (by decide)
  have fsv := frame_trans fu fv
  obtain ⟨w,hw,fw⟩ := s1_regime2 v (transport_host h fsv)
  obtain ⟨z,hz,fz⟩ := Callees.el2a32 w
  have fsz := frame_trans (frame_trans fsv fw) fz
  obtain ⟨t,ht,ft⟩ := host0 z (transport_host h fsz)
  obtain ⟨p,hp⟩ : ∃ p, HavePACExt () t = .ok p t := ⟨_,rfl⟩
  have fst := frame_trans fsz ft
  simp only [Bind.bind,EStateM.bind] at hu hv
  unfold EffectiveTBI
  by_cases ha : ((BitVec.setWidth 1 (BitVec.join1 [BitVec.access a 55])) == 1#1) = true
  all_goals cases p <;>
    simp only [hu,hv,hw,hz,ht,hp,ha,vhe_on z (transport_host h fsz),HaveEL,ArmFull.assert,PreSail.assert,
      Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,el2_ne_el1,beq_self_eq_true,
      readReg,PreSail.readReg_apply,Bool.not_false,Bool.not_true,Bool.true_or,Bool.false_or,
      Bool.or_true,Bool.false_eq_true,↓reduceIte,ite_true,ite_false]
  all_goals
    by_cases h0 : (_get_TCR_EL2_Type_TBI0 (Register.TCR_EL2.get t.regs) == 1#1) = true <;>
      by_cases h1 : (_get_TCR_EL2_Type_TBI1 (Register.TCR_EL2.get t.regs) == 1#1) = true <;>
      first
      | (refine ⟨1#1,t,?_,fst⟩; simp only [h0,h1,hp,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_true,ite_false]; done)
      | exact ⟨0#1,t,by simp only [h0,h1,hp,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_true,ite_false],fst⟩

theorem allocation_frame (s : State) (h : HostPins s) :
    ∃ b t, AArch64_AllocationTagAccessIsEnabled EL0 s = .ok b t ∧ TraceFrame s t := by
  obtain ⟨u,hu,fu⟩ := Callees.el2en s (by simpa using h.aa64) (by
    simpa only [_get_SCR_EL3_Type_NS,Sail.BitVec.castWidth_eq] using h.ns)
  obtain ⟨t,ht,ft⟩ := regime20 u (transport_host h fu)
  obtain ⟨v,hv,fv⟩ := regime20 s h
  have he : _get_HCR_EL2_Type_E2H (Register.HCR_EL2.get u.regs) = 1#1 := (transport_host h fu).e2h
  have hg : _get_HCR_EL2_Type_TGE (Register.HCR_EL2.get u.regs) = 1#1 := (transport_host h fu).tge
  have h11 : (1#1 +++ 1#1 != 3#2) = false := rfl
  unfold AArch64_AllocationTagAccessIsEnabled
  by_cases hs : (_get_SCR_EL3_Type_ATA (Register.SCR_EL3.get s.regs) == 0#1) = true
  · exact ⟨false,s,by
      simp only [readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
        beq_self_eq_true,Bool.true_or,Bool.and_true,hs,ite_true],⟨rfl,rfl,rfl,choice_delta_refl s⟩⟩
  · by_cases hh : (_get_HCR_EL2_Type_ATA (Register.HCR_EL2.get s.regs) == 0#1) = true
    · exact ⟨(_get_SCTLR_EL2_Type_ATA0 (Register.SCTLR_EL2.get t.regs) == 1#1),t,by
        simp only [readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
          beq_self_eq_true,Bool.true_or,Bool.and_true,hs,hh,hu,ht,he,hg,h11,Bool.false_eq_true,ite_true,ite_false,↓reduceIte],
        frame_trans fu ft⟩
    · exact ⟨(_get_SCTLR_EL2_Type_ATA0 (Register.SCTLR_EL2.get v.regs) == 1#1),v,by
        simp only [readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
          beq_self_eq_true,Bool.true_or,Bool.and_true,hs,hh,hv,Bool.false_eq_true,ite_true,ite_false,↓reduceIte],fv⟩

theorem tcf0_fault_no_report (a : BitVec 64) (acc : AccessDescriptor) (s : State) (h : HostPins s)
    (el : acc.el = EL0) (tcf0 : _get_SCTLR_EL2_Type_TCF0 (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#2) :
    ∃ t, AArch64_TagCheckFault a acc s = .ok () t ∧ TraceFrame s t := by
  obtain ⟨l,u,ho,fo⟩ := occ_trace 1358 s (by decide)
  obtain ⟨bits,v,hb,fb⟩ := bits_trace 2 l u
  have fov := frame_trans fo fb
  obtain ⟨w,hw,fw⟩ := regime20 v (transport_host h fov)
  have fow := frame_trans fov fw
  have tcf : _get_SCTLR_EL2_Type_TCF0 (Register.SCTLR_EL2.get w.regs) = 0#2 := by
    change _get_SCTLR_EL2_Type_TCF0 (w.regs.bank_BitVec_64 .SCTLR_EL2) = 0#2
    rw [fow.1]; exact tcf0
  have effective : AArch64_EffectiveTCF acc.el s = .ok 0#2 w := by
    unfold AArch64_EffectiveTCF
    simp only [el,ho,hb,hw,tcf,readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
      beq_self_eq_true,ite_true]
    rfl
  obtain ⟨fault,t,hf,_,ff⟩ := nofault acc w
  refine ⟨t,?_,frame_trans fow ff⟩
  unfold AArch64_TagCheckFault
  simp only [effective,hf,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure]

private def noTopIgnore (address : BitVec 64) : SailM Bool := do
  let state ← readReg Register.PSTATE
  let mtx ← EffectiveMTX address false state.EL
  if mtx == 0#1 then
    let state ← readReg Register.PSTATE
    let tbi ← EffectiveTBI address false state.EL
    pure (tbi == 0#1)
  else pure false

private theorem noTopIgnore_frame (address : BitVec 64) (s : State) (host : HostPins s) :
    ∃ value t, noTopIgnore address s = .ok value t ∧ TraceFrame s t := by
  obtain ⟨mtx, u, hm, fu⟩ := mtx_frame address s host
  obtain ⟨tbi, t, hb, ft⟩ := tbi_frame address u (transport_host host fu)
  have hs : (Register.PSTATE.get s.regs).EL = EL0 := host.el
  have hu : (Register.PSTATE.get u.regs).EL = EL0 := (transport_host host fu).el
  by_cases equal : (mtx == 0#1) = true
  · exact ⟨tbi == 0#1, t, by
      simp only [noTopIgnore, readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, hs, hu, hm, hb, equal, ite_true], frame_trans fu ft⟩
  · exact ⟨false, u, by
      simp only [noTopIgnore, readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, hs, hm, equal, Bool.false_eq_true, ite_false], fu⟩

private def tagMask (address : BitVec 64) : SailM Bool := do
  let state ← readReg Register.PSTATE
  let tcma ← EffectiveTCMA address state.EL
  let high := Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb address 59 55)
  pure ((tcma == 1#1) && ((high == 0#5) || (high == 31#5)))

private theorem tagMask_frame (address : BitVec 64) (s : State) (host : HostPins s) :
    ∃ value t, tagMask address s = .ok value t ∧ TraceFrame s t := by
  obtain ⟨tcma, t, run, frame⟩ := tcma_frame address s host
  have el : (Register.PSTATE.get s.regs).EL = EL0 := host.el
  unfold tagMask
  simp only [readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, el, run]
  exact ⟨_, t, rfl, frame⟩

theorem store_only_frame (s : State) (host : HostPins s)
    (feature : HaveMTEStoreOnlyExt () s = .ok true s) :
    ∃ value t, StoreOnlyTagCheckingEnabled EL0 s = .ok value t ∧ TraceFrame s t := by
  obtain ⟨unused, u, bits, firstFrame⟩ := bit1 1353 s (by decide)
  obtain ⟨t, runHost, hostFrame⟩ := host0 u (transport_host host firstFrame)
  simp only [Bind.bind, EStateM.bind] at bits
  refine ⟨_get_SCTLR_EL2_Type_TCSO0 (Register.SCTLR_EL2.get t.regs) == 1#1, t, ?_,
    frame_trans firstFrame hostFrame⟩
  simp only [StoreOnlyTagCheckingEnabled, feature, ArmFull.assert, PreSail.assert,
    bits, runHost, readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, beq_self_eq_true,
    Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  all_goals rfl

private def storeDecision (access : AccessDescriptor) : SailM Bool := do
  let feature ← HaveMTEStoreOnlyExt ()
  if feature && !access.write then StoreOnlyTagCheckingEnabled access.el else pure false

private theorem storeDecision_frame (access : AccessDescriptor) (s : State) (host : HostPins s)
    (el : access.el = EL0) :
    ∃ value t, storeDecision access s = .ok value t ∧ TraceFrame s t := by
  obtain ⟨feature, hf⟩ : ∃ feature, HaveMTEStoreOnlyExt () s = .ok feature s := ⟨_, rfl⟩
  cases feature with
  | false =>
    exact ⟨false, s, by
      simp only [storeDecision, hf, Bool.false_and, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      all_goals rfl, rfl, rfl, rfl, choice_delta_refl s⟩
  | true =>
    cases write : access.write with
    | true =>
      exact ⟨false, s, by
        simp only [storeDecision, hf, write, Bool.not_true, Bool.and_false,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        all_goals rfl, rfl, rfl, rfl, choice_delta_refl s⟩
    | false =>
      obtain ⟨value, t, run, frame⟩ := store_only_frame s host hf
      refine ⟨value, t, ?_, frame⟩
      simp only [storeDecision, hf, write, el, run, Bool.not_false, Bool.and_true,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ite_true]

theorem access_default (catalogue : ControlCatalogue) (address : BitVec 64)
    (access : AccessDescriptor) (s : State) (controls : DefaultAt catalogue s)
    (el : access.el = EL0) (requested : access.tagchecked = true) :
    ∃ checked t, AArch64_AccessIsTagChecked address access s = .ok checked t ∧ TraceFrame s t := by
  obtain ⟨ignored, u, hu, fu⟩ := noTopIgnore_frame address s controls.host
  obtain ⟨masked, v, hv, fv⟩ := tagMask_frame address u (transport_host controls.host fu)
  have frameSV := frame_trans fu fv
  obtain ⟨enabled, w, hw, fw⟩ := allocation_frame v (transport_host controls.host frameSV)
  have frameSW := frame_trans frameSV fw
  obtain ⟨storeOnly, t, ht, ft⟩ := storeDecision_frame access w (transport_host controls.host frameSW) el
  have tco : (Register.PSTATE.get w.regs).TCO = 0#1 := (transport_default controls frameSW).tco
  have zeroTco : (0#1 == 1#1) = false := rfl
  unfold noTopIgnore at hu
  unfold tagMask at hv
  unfold storeDecision at ht
  simp only [Bind.bind, EStateM.bind, readReg, PreSail.readReg_apply, Pure.pure, EStateM.pure, el] at hu hv ht
  unfold AArch64_AccessIsTagChecked
  cases ignored with
  | true =>
    exact ⟨false, u, by
      simp only [requested, using_a64 s controls.host, ArmFull.assert, PreSail.assert,
        readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        hu, Bool.false_eq_true, ite_true, ite_false], fu⟩
  | false =>
    cases masked with
    | true =>
      exact ⟨false, v, by
        simp only [requested, using_a64 s controls.host, ArmFull.assert, PreSail.assert,
          readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          hu, hv, Bool.false_eq_true, ite_true, ite_false], frameSV⟩
    | false =>
      cases enabled with
      | false =>
        exact ⟨false, w, by
          simp only [requested, el, using_a64 s controls.host, ArmFull.assert, PreSail.assert,
            readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            hu, hv, hw, Bool.not_false, Bool.false_eq_true, ite_true, ite_false], frameSW⟩
      | true =>
        refine ⟨!storeOnly, t, ?_, frame_trans frameSW ft⟩
        cases storeOnly <;>
          simp only [requested, el, using_a64 s controls.host, ArmFull.assert, PreSail.assert,
            readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            hu, hv, hw, tco, zeroTco, ht, Bool.not_false, Bool.not_true, Bool.false_eq_true,
            ite_true, ite_false]
        all_goals rfl

theorem _root_.NativeMteTagCheck.prepare_off (address : BitVec 64) (access : AccessDescriptor) (s : State)
    (h : s.regs.FeatureImpl[134]! = false) : NativeMte2.prepare address access s = .ok access s := by
  simp only [NativeMte2.prepare, NativeMte2.have_mte2, h, Bool.false_and, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, Bool.false_eq_true, ite_false]

theorem prepare_default (catalogue : ControlCatalogue) (address : BitVec 64)
    (access : AccessDescriptor) (s : State) (controls : DefaultAt catalogue s)
    (el : access.el = EL0) :
    ∃ prepared t, NativeMte2.prepare address access s = .ok prepared t ∧
      prepared = { access with tagchecked := prepared.tagchecked } ∧
      TraceFrame s t ∧ DefaultAt catalogue t := by
  cases hm : s.regs.FeatureImpl[134]! with
  | false =>
    refine ⟨access, s, prepare_off address access s hm, ?_, ⟨rfl, rfl, rfl, choice_delta_refl s⟩, controls⟩
    cases access; rfl
  | true =>
    cases requested : access.tagchecked with
    | false =>
      refine ⟨access, s, ?_, ?_, ⟨rfl, rfl, rfl, choice_delta_refl s⟩, controls⟩
      · simp only [NativeMte2.prepare, NativeMte2.have_mte2, hm, requested,
          Bool.and_false, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        all_goals rfl
      · cases access
        rfl
    | true =>
      obtain ⟨checked, t, run, frame⟩ := access_default catalogue address access s controls el requested
      refine ⟨{ access with tagchecked := checked }, t, ?_, rfl, frame, transport_default controls frame⟩
      simp only [NativeMte2.prepare, NativeMte2.have_mte2, hm, requested, run,
        Bool.and_true, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ite_true]

theorem prepared_kind (access : AccessDescriptor) (checked : Bool) :
    AccessDescriptor_to_Access_kind { access with tagchecked := checked } =
      AccessDescriptor_to_Access_kind access := rfl

theorem check_tag_transport (descriptor : AddressDescriptor) (access : AccessDescriptor)
    (physicalTag : BitVec 4) (s : State)
    (allowed : descriptor.memattrs.tags = .MemTag_AllocationTagged → TagStatusOK s) :
    ∃ matched t draws, AArch64_CheckTag descriptor access physicalTag s = .ok matched t ∧
      S1Normality.Frame s t ∧ ChoiceDelta s t draws ∧ draws ≤ 1 := by
  cases kind : descriptor.memattrs.tags with
  | MemTag_Untagged =>
    refine ⟨true, s, 0, ?_, ⟨rfl, rfl, rfl⟩, choice_delta_refl s, by decide⟩
    simp only [AArch64_CheckTag, kind]
    all_goals rfl
  | MemTag_CanonicallyTagged =>
    refine ⟨AArch64_CanonicalTagCheck descriptor physicalTag, s, 0, ?_,
      ⟨rfl, rfl, rfl⟩, choice_delta_refl s, by decide⟩
    simp only [AArch64_CheckTag, kind]
    all_goals rfl
  | MemTag_AllocationTagged =>
    obtain ⟨matched, t, run, frame, delta⟩ :=
      allocation_tag_transport descriptor access physicalTag s kind (allowed kind)
    have sameKind : (MemTagType.MemTag_AllocationTagged == MemTagType.MemTag_AllocationTagged) = true := rfl
    refine ⟨matched, t, 1, ?_, frame, delta, by decide⟩
    simpa only [AArch64_CheckTag, kind, sameKind, ite_true] using run

theorem tagcheck_transport (catalogue : ControlCatalogue) (address : BitVec 64)
    (descriptor : AddressDescriptor) (access : AccessDescriptor) (s : State)
    (controls : DefaultAt catalogue s) (el : access.el = EL0)
    (allowed : access.tagchecked = true →
      descriptor.memattrs.tags = .MemTag_AllocationTagged → TagStatusOK s) :
    ∃ t draws, checkedAccess address descriptor access s = .ok () t ∧
      S1Normality.Frame s t ∧ DefaultAt catalogue t ∧
      ChoiceDelta s t draws ∧ draws ≤ 1 := by
  cases hm : s.regs.FeatureImpl[134]! with
  | false =>
    exact ⟨s, 0, checked_off address descriptor access s hm, ⟨rfl, rfl, rfl⟩, controls, choice_delta_refl s, by decide⟩
  | true =>
    cases tagchecked : access.tagchecked with
    | false =>
      refine ⟨s, 0, ?_, ⟨rfl, rfl, rfl⟩, controls, choice_delta_refl s, by decide⟩
      simp only [checkedAccess, NativeMte2.have_mte2, hm, tagchecked,
        Bool.and_false, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      all_goals rfl
    | true =>
      obtain ⟨matched, afterCheck, draws, checked, checkFrame, delta, bound⟩ :=
        check_tag_transport descriptor access (AArch64_PhysicalTag address) s (allowed tagchecked)
      cases matched with
      | true =>
        refine ⟨afterCheck, draws, ?_, checkFrame, controls.transport checkFrame, delta, bound⟩
        simp only [checkedAccess, NativeMte2.have_mte2, hm, tagchecked, checked,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_true, ite_false]
        all_goals rfl
      | false =>
        have afterControls := controls.transport checkFrame
        obtain ⟨t, fault, faultTrace⟩ :=
          tcf0_fault_no_report address access afterCheck afterControls.host el afterControls.tcf0
        have frame := MemM1.NoFault.frame_trans checkFrame (to_frame faultTrace)
        have combined : ChoiceDelta s t draws := by
          simpa only [Nat.add_zero] using choice_delta_trans delta faultTrace.2.2.2
        refine ⟨t, draws, ?_, frame, controls.transport frame, combined, bound⟩
        simp only [checkedAccess, NativeMte2.have_mte2, hm, tagchecked, checked, fault,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_true, ite_false]
        all_goals rfl

#print axioms check_tag_transport
#print axioms tagcheck_transport

#print axioms Callees.regime_el0
#print axioms tcf0_fault_no_report
#print axioms prepare_default
end NativeMteTagCheck.StatusTrace
