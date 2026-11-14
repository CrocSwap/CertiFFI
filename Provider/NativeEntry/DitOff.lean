import NativeEntry.DitOffRoot
import Bridge.RootFrame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntry.DitOff
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
def expected (s : NativeState)  :=
  ({ s.regs with PSTATE := { s.regs.PSTATE with DIT := 0#1 }, BTypeNext := 0#2 }, s.mem, s.events)
def projection (s : NativeState) := (s.regs, s.mem, s.events)

structure Guard (s : NativeState)  : Prop where
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  word : s.regs.bank_BitVec_32 .__ThisInstr = 0xd503405f#32
  dit : s.regs.FeatureImpl[103]! = true
  bti : s.regs.FeatureImpl[123]! = true
  tme : s.regs.FeatureImpl[227]! = false


theorem effect (s : NativeState)  (g : Guard s) :
    ∃ t, (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 0#4 3#3 : SailM Unit) s = .ok () t ∧
      projection t = expected s := by

  obtain ⟨u, hu⟩ : ∃ u, effect_native s = .ok (expected s) u := by
    unfold effect_native expected

    first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)
  have root := (effect_complete s g.el g.a64 g.aa64 g.btype g.word g.dit g.bti g.tme).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntry.DitOff
