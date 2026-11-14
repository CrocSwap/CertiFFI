import NativeEntryBody.SecpCsinv2ZZRoot
import Bridge.RootFrame
import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBody.SecpCsinv2ZZ
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- These are the exact output fields of the actual selected Sail decoder.
Expected projection only, not a replacement action/evaluator. -/
/- AUTO-FIELDS: only the listed fields take the ACTUAL drive_spec value (effect_native);
every other field is literally the input. effect proves the whole actual output has
exactly this shape, so an unlisted write would fail to compile. -/
noncomputable def expected (s : NativeState) (Rd : BitVec 5) : Regs × Std.ExtHashMap Nat (BitVec 8) × Array Event :=
  ({ s.regs with gpr := ((match effect_native s Rd with | .ok v _ => v | .error _ _ => (s.regs, s.mem, s.events)).1).gpr }, s.mem, s.events)
def projection (s : NativeState) := (s.regs, s.mem, s.events)

structure Guard (s : NativeState) (Rd : BitVec 5) : Prop where
  rd : Rd.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2
  spe : s.regs.bank_Bool .SPESampleInFlight = false


set_option maxHeartbeats 1000000 in
theorem effect (s : NativeState) (Rd : BitVec 5) (g : Guard s Rd) :
    ∃ t, (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 2#4 31#5 1#1 1#1 : SailM Unit) s = .ok () t ∧
      projection t = expected s Rd := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by have := g.rd; omega
  obtain ⟨u, hu⟩ : ∃ u, effect_native s Rd = .ok (expected s Rd) u := by
    unfold expected effect_native
    simp only [g.spe, hRd, ite_true, ite_false, dite_eq_ite, ite_self]

    by_cases hz : s.regs.PSTATE.C = 1#1 <;> simp only [hz, ↓reduceIte] <;> exact ⟨_, rfl⟩
  have root := (effect_complete s Rd g.rd g.el g.a64 g.aa64 g.btype g.btn g.spe).trans hu
  have success := ArmBridge.RootFrame.ok_of_root _ projection s u (expected s Rd) root
  have fields := ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s Rd) u) root
  exact ⟨_, success, fields⟩

#print axioms effect
end NativeEntryBody.SecpCsinv2ZZ
