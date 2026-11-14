import NativeEntryBody.SecpLsr31Root
import Bridge.RootFrame
import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBody.SecpLsr31
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
/- AUTO: the expected output IS the actual drive_spec evaluation of the selected
decoder (effect_native), so no hand-written post state can disagree with the model. -/
noncomputable def expected (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) : Regs × Std.ExtHashMap Nat (BitVec 8) × Array Event :=
  match effect_native s Rd Rn with
  | .ok v _ => v
  | .error _ _ => (s.regs, s.mem, s.events)
def projection (s : NativeState) := (s.regs, s.mem, s.events)

structure Guard (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) : Prop where
  rd : Rd.toNat < 31
  rn : Rn.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2


theorem effect (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (g : Guard s Rd Rn) :
    ∃ t, (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 31#6 1#1 2#2 1#1 : SailM Unit) s = .ok () t ∧
      projection t = expected s Rd Rn := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by have := g.rd; omega
  have hRn : ¬ (Rn.toNat : Int) = 31 := by have := g.rn; omega
  obtain ⟨u, hu⟩ : ∃ u, effect_native s Rd Rn = .ok (expected s Rd Rn) u := by
    unfold expected effect_native
    simp only [hRd, hRn, ite_true, ite_false, dite_eq_ite, ite_self]

    exact ⟨_, rfl⟩
  have root := (effect_complete s Rd Rn g.rd g.rn g.el g.a64 g.aa64 g.btype g.btn).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s Rd Rn) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s Rd Rn) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntryBody.SecpLsr31
