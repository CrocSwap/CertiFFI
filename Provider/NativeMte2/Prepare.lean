import NativeMte2.Getters
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace NativeMte2
open S1Normality MemM1.NoFault

private def noTopIgnore (a : BitVec 64) : SailM Bool := do
  let p ← readReg Register.PSTATE
  let m ← EffectiveMTX a false p.EL
  if m == 0#1 then
    let p ← readReg Register.PSTATE
    let b ← EffectiveTBI a false p.EL
    pure (b == 0#1)
  else pure false

private theorem noTopIgnore_frame (a : BitVec 64) (s : State) (h : HostPins s) :
    ∃ b t, noTopIgnore a s = .ok b t ∧ Frame s t := by
  obtain ⟨m,u,hm,fu⟩ := mtx_frame a s h
  obtain ⟨b,t,hb,ft⟩ := tbi_frame a u (h.transport fu)
  have hs : (Register.PSTATE.get s.regs).EL = EL0 := h.el
  have hu : (Register.PSTATE.get u.regs).EL = EL0 := (h.transport fu).el
  by_cases e : (m == 0#1) = true
  · exact ⟨(b == 0#1),t,by
      simp only [noTopIgnore,readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,
        Pure.pure,EStateM.pure,hs,hu,hm,hb,e,ite_true],frame_trans fu ft⟩
  · exact ⟨false,u,by
      simp only [noTopIgnore,readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,
        Pure.pure,EStateM.pure,hs,hm,e,Bool.false_eq_true,ite_false],fu⟩

private def tagMask (a : BitVec 64) : SailM Bool := do
  let p ← readReg Register.PSTATE
  let m ← EffectiveTCMA a p.EL
  let hi := Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb a 59 55)
  pure ((m == 1#1) && ((hi == 0#5) || (hi == 31#5)))

private theorem tagMask_frame (a : BitVec 64) (s : State) (h : HostPins s) :
    ∃ b t, tagMask a s = .ok b t ∧ Frame s t := by
  obtain ⟨m,t,hm,ft⟩ := tcma_frame a s h
  have hs : (Register.PSTATE.get s.regs).EL = EL0 := h.el
  unfold tagMask
  simp only [readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,hs,hm]
  exact ⟨_,t,rfl,ft⟩

/-- The actual tag check decision returns false; all draws keep their real successor. -/
theorem access_not_tagchecked_tco (a : BitVec 64) (acc : AccessDescriptor) (s : State)
    (h : TcoAt s) (el : acc.el = EL0) (tag : acc.tagchecked = true) :
    ∃ t, AArch64_AccessIsTagChecked a acc s = .ok false t ∧ Frame s t := by
  obtain ⟨b,u,hu,fu⟩ := noTopIgnore_frame a s h.host
  obtain ⟨c,v,hv,fv⟩ := tagMask_frame a u (h.host.transport fu)
  have fsv := frame_trans fu fv
  obtain ⟨d,w,hw,fw⟩ := allocation_frame v (h.host.transport fsv)
  have fsw := frame_trans fsv fw
  have ht : (Register.PSTATE.get w.regs).TCO = 1#1 := (h.transport fsw).tco
  unfold noTopIgnore at hu
  unfold tagMask at hv
  simp only [Bind.bind,EStateM.bind,readReg,PreSail.readReg_apply,Pure.pure,EStateM.pure] at hu hv
  unfold AArch64_AccessIsTagChecked
  cases b
  · cases c
    · refine ⟨w,?_,fsw⟩
      cases d <;> simp only [tag,el,using_a64 s h.host,ArmFull.assert,PreSail.assert,
        readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
        hu,hv,hw,ht,Bool.not_false,Bool.not_true,Bool.false_eq_true,beq_self_eq_true,ite_true,ite_false,↓reduceIte]
    · exact ⟨v,by simp only [tag,using_a64 s h.host,ArmFull.assert,PreSail.assert,
        readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
        hu,hv,Bool.false_eq_true,ite_true,ite_false,↓reduceIte],fsv⟩
  · exact ⟨u,by simp only [tag,using_a64 s h.host,ArmFull.assert,PreSail.assert,
      readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
      hu,Bool.false_eq_true,ite_true,ite_false,↓reduceIte],fu⟩

/-- This is the descriptor preparation in both Sail MemSingle read and set. -/
def prepare (a : BitVec 64) (acc : AccessDescriptor) : SailM AccessDescriptor := do
  let m ← HaveMTE2Ext ()
  if m && acc.tagchecked then
    let b ← AArch64_AccessIsTagChecked a acc
    pure {acc with tagchecked := b}
  else pure acc

theorem prepare_tco (a : BitVec 64) (acc : AccessDescriptor) (s : State)
    (h : TcoAt s) (el : acc.el = EL0) :
    ∃ t, prepare a acc s = .ok (clearTagCheck acc) t ∧ Frame s t := by
  cases tag : acc.tagchecked
  · have same : clearTagCheck acc = acc := by
      cases acc <;> simp_all only [clearTagCheck]
    exact ⟨s,by simp only [prepare,have_mte2,h.mte2,tag,same,Bool.and_false,
      Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false],⟨rfl,rfl,rfl⟩⟩
  · obtain ⟨t,ht,ft⟩ := access_not_tagchecked_tco a acc s h el tag
    exact ⟨t,by simp only [prepare,have_mte2,h.mte2,tag,ht,Bool.and_true,
      Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,ite_true,clearTagCheck],ft⟩

@[simp] theorem clearTagCheck_tag (acc : AccessDescriptor) : (clearTagCheck acc).tagchecked = false := rfl

theorem clearTagCheck_kind (acc : AccessDescriptor) :
    AccessDescriptor_to_Access_kind (clearTagCheck acc) = AccessDescriptor_to_Access_kind acc := rfl

/-- The exact descriptor branch after reading HaveMTE2Ext in MemSingle. -/
theorem prepare_if_tco (a : BitVec 64) (acc : AccessDescriptor) (s : State)
    (h : TcoAt s) (el : acc.el = EL0) :
    ∃ t, ((if acc.tagchecked then
      (do let b ← AArch64_AccessIsTagChecked a acc; pure {acc with tagchecked := b})
      else pure acc) : SailM AccessDescriptor) s = .ok (clearTagCheck acc) t ∧ Frame s t := by
  simpa only [prepare,have_mte2,h.mte2,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    Bool.true_and] using prepare_tco a acc s h el

#print axioms access_not_tagchecked_tco
#print axioms prepare_tco
end NativeMte2
