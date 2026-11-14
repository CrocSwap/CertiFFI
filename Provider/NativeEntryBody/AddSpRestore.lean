import NativeEntryBody.AddSpRestoreRoot
import Bridge.RootFrame
import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBody.AddSpRestore
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
/- AUTO: the expected output IS the actual drive_spec evaluation of the selected
decoder (effect_native), so no hand-written post state can disagree with the model. -/
noncomputable def expected (s : NativeState) (imm12 : BitVec 12) : Regs × Std.ExtHashMap Nat (BitVec 8) × Array Event :=
  match effect_native s imm12 with
  | .ok v _ => v
  | .error _ _ => (s.regs, s.mem, s.events)
def projection (s : NativeState) := (s.regs, s.mem, s.events)

structure Guard (s : NativeState) (imm12 : BitVec 12) : Prop where
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2


theorem effect (s : NativeState) (imm12 : BitVec 12) (g : Guard s imm12) :
    ∃ t, (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 31#5 imm12 0#1 0#1 0#1 1#1 : SailM Unit) s = .ok () t ∧
      projection t = expected s imm12 := by

  obtain ⟨u, hu⟩ : ∃ u, effect_native s imm12 = .ok (expected s imm12) u := by
    unfold effect_native expected
    simp only [ite_true, ite_false, dite_eq_ite, ite_self]

    exact ⟨_, rfl⟩
  have root := (effect_complete s imm12 g.el g.a64 g.aa64 g.btype g.btn).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s imm12) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s imm12) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntryBody.AddSpRestore
