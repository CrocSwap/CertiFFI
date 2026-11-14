import NativeEntry.MrsDitRoot
import Bridge.RootFrame
import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntry.MrsDit
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
def expected (s : NativeState) (Rt : BitVec 5) :=
  ({ s.regs with gpr := s.regs.gpr.set (GPRSummary.key Rt.toNat).val ((0#39 +++ s.regs.PSTATE.DIT) +++ 0#24) (GPRSummary.key Rt.toNat).isLt }, s.mem, s.events)
def projection (s : NativeState) := (s.regs, s.mem, s.events)

structure Guard (s : NativeState) (Rt : BitVec 5) : Prop where
  rt : Rt.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2
  dit : s.regs.FeatureImpl[103]! = true
  bti : s.regs.FeatureImpl[123]! = true
  tme : s.regs.FeatureImpl[227]! = false


theorem effect (s : NativeState) (Rt : BitVec 5) (g : Guard s Rt) :
    ∃ t, (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1 : SailM Unit) s = .ok () t ∧
      projection t = expected s Rt := by
  have hRt : ¬ (Rt.toNat : Int) = 31 := by have := g.rt; omega
  obtain ⟨u, hu⟩ : ∃ u, effect_native s Rt = .ok (expected s Rt) u := by
    unfold effect_native expected
    simp only [btn_set_zero _ g.btn, hRt, ite_true, ite_false, dite_eq_ite, ite_self]

    first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)
  have root := (effect_complete s Rt g.rt g.el g.a64 g.aa64 g.btype g.btn g.dit g.bti g.tme).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s Rt) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s Rt) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntry.MrsDit
