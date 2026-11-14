import NativeEntry.BtiCRoot
import Bridge.RootFrame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntry.BtiC
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
def expected (s : NativeState)  :=
  ({ s.regs with BTypeCompatible := s.regs.PSTATE.BTYPE != 3#2, BTypeNext := 0#2 }, s.mem, s.events)
def projection (s : NativeState) := (s.regs, s.mem, s.events)



theorem effect (s : NativeState)   :
    ∃ t, (decode_bti_aarch64_instrs_system_hints 2#3 4#4 : SailM Unit) s = .ok () t ∧
      projection t = expected s := by

  obtain ⟨u, hu⟩ : ∃ u, effect_native s = .ok (expected s) u := by
    unfold effect_native expected

    first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)
  have root := (effect_complete s ).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntry.BtiC
