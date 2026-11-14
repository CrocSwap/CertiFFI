import NativeEntry.IsbSyRoot
import Bridge.RootFrame
import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntry.IsbSy
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
def expected (s : NativeState)  :=
  (s.regs, s.mem, s.events.push (.barrier (.Barrier_ISB ())))
def projection (s : NativeState) := (s.regs, s.mem, s.events)

structure Guard (s : NativeState)  : Prop where
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  aa32el2 : s.regs.FeatureImpl[2]! = false
  aa32el3 : s.regs.FeatureImpl[3]! = false
  aa64el2 : s.regs.FeatureImpl[6]! = true
  aa64el3 : s.regs.FeatureImpl[7]! = true
  rme : s.regs.FeatureImpl[232]! = false
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  brbe : s.regs.FeatureImpl[230]! = false
  spe : s.regs.bank_Bool .SPESampleInFlight = false


theorem effect (s : NativeState)  (g : Guard s) :
    ∃ t, (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit) s = .ok () t ∧
      projection t = expected s := by

  obtain ⟨u, hu⟩ : ∃ u, effect_native s = .ok (expected s) u := by
    unfold effect_native expected

    first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)
  have root := (effect_complete s g.el g.a64 g.aa64 g.aa32el2 g.aa32el3 g.aa64el2 g.aa64el3 g.rme g.e2h g.tge g.ns g.brbe g.spe).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntry.IsbSy
