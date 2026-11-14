import NativeMte2.Control
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace NativeMte2
open S1Normality MemM1.NoFault

/-- One actual width-one undefined draw, including its occurrence update. -/
theorem bit1 (site : Nat) (s : State) :
    ∃ b t, ((do let label ← occLabel site; undefined_bitvector_at label 1) : SailM (BitVec 1)) s = .ok b t ∧
      Frame s t := by
  obtain ⟨label,u,hl,fl⟩ := occ_normal site s
  obtain ⟨b,t,hb,fb⟩ := bits_normal 1 label u
  exact ⟨b,t,by simp only [Bind.bind,EStateM.bind,hl,hb],frame_trans fl fb⟩

private theorem el2_ne_el1 : (EL2 == EL1) = false := rfl

theorem tcma_frame (a : BitVec 64) (s : State) (h : HostPins s) :
    ∃ b t, EffectiveTCMA a EL0 s = .ok b t ∧ Frame s t := by
  obtain ⟨_,u,hu,fu⟩ := bit1 740 s
  obtain ⟨v,hv,fv⟩ := s1_regime2 u (h.transport fu)
  obtain ⟨w,hw,fw⟩ := MemM1.Callees.el2a32 v
  have fsw := frame_trans (frame_trans fu fv) fw
  obtain ⟨t,ht,ft⟩ := host0 w (h.transport fsw)
  simp only [Bind.bind,EStateM.bind] at hu
  unfold EffectiveTCMA
  simp only [hu,hv,hw,ht,vhe_on w (h.transport fsw),HaveEL,ArmFull.assert,PreSail.assert,
    Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,el2_ne_el1,beq_self_eq_true,
    Bool.not_false,Bool.false_eq_true,↓reduceIte,ite_true,ite_false]
  split <;> exact ⟨_,t,rfl,frame_trans fsw ft⟩

theorem mtx_frame (a : BitVec 64) (s : State) (h : HostPins s) :
    ∃ b t, EffectiveMTX a false EL0 s = .ok b t ∧ Frame s t := by
  obtain ⟨_,u,hu,fu⟩ := bit1 741 s
  obtain ⟨v,hv,fv⟩ := s1_regime2 u (h.transport fu)
  obtain ⟨w,hw,fw⟩ := MemM1.Callees.el2a32 v
  have fsw := frame_trans (frame_trans fu fv) fw
  obtain ⟨m,hm⟩ : ∃ m, HaveMTE4Ext () w = .ok m w := ⟨_,rfl⟩
  obtain ⟨t,ht,ft⟩ := host0 w (h.transport fsw)
  simp only [Bind.bind,EStateM.bind] at hu
  unfold EffectiveMTX
  cases m
  · simp only [hu,hv,hw,hm,HaveEL,ArmFull.assert,PreSail.assert,Bind.bind,EStateM.bind,
      Pure.pure,EStateM.pure,Bool.not_false,Bool.true_or,↓reduceIte,ite_true]
    exact ⟨0#1,w,rfl,fsw⟩
  · simp only [hu,hv,hw,hm,ht,vhe_on w (h.transport fsw),HaveEL,ArmFull.assert,PreSail.assert,
      Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,el2_ne_el1,beq_self_eq_true,
      Bool.not_false,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte,ite_true,ite_false]
    split <;> exact ⟨_,t,rfl,frame_trans fsw ft⟩

theorem tbi_frame (a : BitVec 64) (s : State) (h : HostPins s) :
    ∃ b t, EffectiveTBI a false EL0 s = .ok b t ∧ Frame s t := by
  obtain ⟨_,u,hu,fu⟩ := bit1 567 s
  obtain ⟨_,v,hv,fv⟩ := bit1 568 u
  have fsv := frame_trans fu fv
  obtain ⟨w,hw,fw⟩ := s1_regime2 v (h.transport fsv)
  obtain ⟨z,hz,fz⟩ := MemM1.Callees.el2a32 w
  have fsz := frame_trans (frame_trans fsv fw) fz
  obtain ⟨t,ht,ft⟩ := host0 z (h.transport fsz)
  obtain ⟨p,hp⟩ : ∃ p, HavePACExt () t = .ok p t := ⟨_,rfl⟩
  have fst := frame_trans fsz ft
  simp only [Bind.bind,EStateM.bind] at hu hv
  unfold EffectiveTBI
  by_cases ha : ((BitVec.setWidth 1 (BitVec.join1 [BitVec.access a 55])) == 1#1) = true
  all_goals cases p <;>
    simp only [hu,hv,hw,hz,ht,hp,ha,vhe_on z (h.transport fsz),HaveEL,ArmFull.assert,PreSail.assert,
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
    ∃ b t, AArch64_AllocationTagAccessIsEnabled EL0 s = .ok b t ∧ Frame s t := by
  obtain ⟨u,hu,fu⟩ := MemM1.Callees.el2en s (by simpa using h.aa64) (by
    simpa only [_get_SCR_EL3_Type_NS,Sail.BitVec.castWidth_eq] using h.ns)
  obtain ⟨t,ht,ft⟩ := regime20 u (h.transport fu)
  obtain ⟨v,hv,fv⟩ := regime20 s h
  have he : _get_HCR_EL2_Type_E2H (Register.HCR_EL2.get u.regs) = 1#1 := (h.transport fu).e2h
  have hg : _get_HCR_EL2_Type_TGE (Register.HCR_EL2.get u.regs) = 1#1 := (h.transport fu).tge
  have h11 : (1#1 +++ 1#1 != 3#2) = false := rfl
  unfold AArch64_AllocationTagAccessIsEnabled
  by_cases hs : (_get_SCR_EL3_Type_ATA (Register.SCR_EL3.get s.regs) == 0#1) = true
  · exact ⟨false,s,by
      simp only [readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
        beq_self_eq_true,Bool.true_or,Bool.and_true,hs,ite_true],⟨rfl,rfl,rfl⟩⟩
  · by_cases hh : (_get_HCR_EL2_Type_ATA (Register.HCR_EL2.get s.regs) == 0#1) = true
    · exact ⟨(_get_SCTLR_EL2_Type_ATA0 (Register.SCTLR_EL2.get t.regs) == 1#1),t,by
        simp only [readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
          beq_self_eq_true,Bool.true_or,Bool.and_true,hs,hh,hu,ht,he,hg,h11,Bool.false_eq_true,ite_true,ite_false,↓reduceIte],
        frame_trans fu ft⟩
    · exact ⟨(_get_SCTLR_EL2_Type_ATA0 (Register.SCTLR_EL2.get v.regs) == 1#1),v,by
        simp only [readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
          beq_self_eq_true,Bool.true_or,Bool.and_true,hs,hh,hv,Bool.false_eq_true,ite_true,ite_false,↓reduceIte],fv⟩

#print axioms tcma_frame
#print axioms mtx_frame
#print axioms tbi_frame
#print axioms allocation_frame
end NativeMte2
