import N1D226.CsetEq32.Root
import Bridge.RootFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace N1D226.CsetEq32
open ArmBridge.Draft
noncomputable def expected (s : NativeState) (Rd : BitVec 5) : Regs × Std.ExtHashMap Nat (BitVec 8) × Array Event :=
  match effect_native s Rd with
  | .ok v _ => v
  | .error _ _ => (s.regs,s.mem,s.events)
def projection (s : NativeState) := (s.regs,s.mem,s.events)
structure Guard (s : NativeState) (Rd : BitVec 5) : Prop where
  rd : Rd.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2

theorem effect (s : NativeState) (Rd : BitVec 5) (g : Guard s Rd) :
    ∃ t, (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1 : SailM Unit) s = .ok () t ∧ projection t = expected s Rd := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by have := g.rd; omega
  obtain ⟨u,hu⟩ : ∃ u, effect_native s Rd = .ok (expected s Rd) u := by
    unfold effect_native expected
    simp only [hRd, ite_true, ite_false, dite_eq_ite, ite_self]
    first | exact ⟨_,rfl⟩ | (split <;> exact ⟨_,rfl⟩)
  have hr := (effect_complete s Rd g.rd g.el g.a64 g.aa64 g.btype g.btn).trans hu
  exact ⟨_,ArmBridge.RootFrame.ok_of_root _ projection s u (expected s Rd) hr,
    ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s Rd) u) hr⟩
#print axioms effect
end N1D226.CsetEq32
