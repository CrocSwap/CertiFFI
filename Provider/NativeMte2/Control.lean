import MemM1.Callees
import ArmFull.Fn.M1042
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
namespace NativeMte2
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

structure HostPins (s : State) : Prop where
  el : s.regs.PSTATE.EL = 0#2
  nrw : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  rme : s.regs.FeatureImpl[232]! = false
  vhe : s.regs.FeatureImpl[54]! = true
  ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1

/-- Current host-EL0 controls for the actual tag-check override path. -/
structure TcoAt (s : State) : Prop where
  host : HostPins s
  mte2 : s.regs.FeatureImpl[134]! = true
  tco : s.regs.PSTATE.TCO = 1#1

def clearTagCheck (acc : AccessDescriptor) : AccessDescriptor := {acc with tagchecked := false}

theorem have_mte2 (s : State) : (HaveMTE2Ext () : SailM Bool) s = .ok s.regs.FeatureImpl[134]! s := rfl

open MemM1.NoFault

protected theorem HostPins.transport {s t : State} (h : HostPins s) (f : Frame s t) : HostPins t := by
  rcases h with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
  constructor <;> rw [f.1] <;> assumption

protected theorem TcoAt.transport {s t : State} (h : TcoAt s) (f : Frame s t) : TcoAt t :=
  ⟨h.host.transport f, f.1 ▸ h.mte2, f.1 ▸ h.tco⟩

private theorem ns_bit (s : State) (h : HostPins s) :
    Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .SCR_EL3) 0 0 = 1#1 := by
  simpa only [_get_SCR_EL3_Type_NS, Sail.BitVec.castWidth_eq] using h.ns

private theorem e2h_bit (s : State) (h : HostPins s) :
    Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .HCR_EL2) 34 34 = 1#1 := by
  simpa only [_get_HCR_EL2_Type_E2H,Sail.BitVec.castWidth_eq] using h.e2h

private theorem tge_bit (s : State) (h : HostPins s) :
    Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .HCR_EL2) 27 27 = 1#1 := by
  simpa only [_get_HCR_EL2_Type_TGE,Sail.BitVec.castWidth_eq] using h.tge

theorem host0 (s : State) (h : HostPins s) : ∃ t, ELIsInHost EL0 s = .ok true t ∧ Frame s t :=
  MemM1.Callees.host0 s (by simpa using h.vhe) (by simpa using h.aa64)
    (ns_bit s h) (e2h_bit s h) (tge_bit s h)

theorem regime20 (s : State) (h : HostPins s) :
    ∃ t, TranslationRegime EL0 s = .ok .Regime_EL20 t ∧ Frame s t :=
  MemM1.Callees.regime_el0 s (by simpa using h.rme) (by simpa using h.vhe)
    (by simpa using h.aa64) (ns_bit s h) (e2h_bit s h) (tge_bit s h)

theorem vhe_on (s : State) (h : HostPins s) : HaveVirtHostExt () s = .ok true s := by
  change EStateM.Result.ok s.regs.FeatureImpl[54]! s = _
  rw [h.vhe]

theorem s1_regime2 (s : State) (h : HostPins s) :
    ∃ t, S1TranslationRegime EL0 s = .ok EL2 t ∧ Frame s t := by
  obtain ⟨u,hu,fu⟩ := MemM1.Callees.el3a32 s
  obtain ⟨t,ht,ft⟩ := host0 u (h.transport fu)
  refine ⟨t,?_,frame_trans fu ft⟩
  unfold S1TranslationRegime
  simp only [HaveEL,hu,vhe_on u (h.transport fu),ht,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    bne_self_eq_false,Bool.false_eq_true,ite_true,ite_false]

theorem using_a64 (s : State) (h : HostPins s) : UsingAArch32 () s = .ok false s := by
  have f4 : IsFeatureImplemented .FEAT_AA64EL0 s = .ok true s := by
    change EStateM.Result.ok s.regs.FeatureImpl[4]! s = _
    rw [h.aa64]
  have aa64 : HaveAArch64 () s = .ok true s := by
    unfold HaveAArch64
    simp only [f4,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,ite_true]
  have nrw : (Register.PSTATE.get s.regs).nRW = 0#1 := h.nrw
  unfold UsingAArch32
  simp only [HaveAArch32,aa64,nrw,readReg,PreSail.readReg_apply,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    Bool.not_true,Bool.false_eq_true,ite_false]
  rfl

/-- Host-EL0 TCF0 chooses the zero mismatch disposition after the tag check.
    This theorem says nothing about earlier tag-memory reads. -/
theorem tcf0_fault_no_report (a : BitVec 64) (acc : AccessDescriptor) (s : State) (h : HostPins s)
    (el : acc.el = EL0) (tcf0 : _get_SCTLR_EL2_Type_TCF0 (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#2) :
    ∃ t, AArch64_TagCheckFault a acc s = .ok () t ∧ Frame s t := by
  obtain ⟨l,u,ho,fo⟩ := occ_normal 1358 s
  obtain ⟨bits,v,hb,fb⟩ := bits_normal 2 l u
  have fov := frame_trans fo fb
  obtain ⟨w,hw,fw⟩ := regime20 v (h.transport fov)
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

#print axioms s1_regime2
#print axioms using_a64
#print axioms tcf0_fault_no_report
end NativeMte2
