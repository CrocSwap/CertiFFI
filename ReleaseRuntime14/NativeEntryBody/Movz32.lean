import NativeEntryBody.Movz32Root
import Bridge.RootFrame
import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBody.Movz32
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
/- AUTO: the expected output IS the actual drive_spec evaluation of the selected
decoder (effect_native), so no hand-written post state can disagree with the model. -/
noncomputable def expected (s : NativeState) (Rd : BitVec 5) (imm16 : BitVec 16) : Regs × Std.ExtHashMap Nat (BitVec 8) × Array Event :=
  match effect_native s Rd imm16 with
  | .ok v _ => v
  | .error _ _ => (s.regs, s.mem, s.events)
def projection (s : NativeState) := (s.regs, s.mem, s.events)

structure Guard (s : NativeState) (Rd : BitVec 5) (imm16 : BitVec 16) : Prop where
  rd : Rd.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2


theorem effect (s : NativeState) (Rd : BitVec 5) (imm16 : BitVec 16) (g : Guard s Rd imm16) :
    ∃ t, (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 0#2 2#2 0#1 : SailM Unit) s = .ok () t ∧
      projection t = expected s Rd imm16 := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by have := g.rd; omega
  obtain ⟨u, hu⟩ : ∃ u, effect_native s Rd imm16 = .ok (expected s Rd imm16) u := by
    unfold effect_native expected
    simp only [hRd, ite_true, ite_false, dite_eq_ite, ite_self]

    exact ⟨_, rfl⟩
  have root := (effect_complete s Rd imm16 g.rd g.el g.a64 g.aa64 g.btype g.btn).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s Rd imm16) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s Rd imm16) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntryBody.Movz32
