import N1D226.CmnImm64Generic.Root
import Bridge.RootFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace N1D226.CmnImm64Generic
open ArmBridge.Draft
noncomputable def expected (s : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) : Regs × Std.ExtHashMap Nat (BitVec 8) × Array Event :=
  match effect_native s Rn imm12 with
  | .ok v _ => v
  | .error _ _ => (s.regs,s.mem,s.events)
def projection (s : NativeState) := (s.regs,s.mem,s.events)
structure Guard (s : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) : Prop where
  rn : Rn.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2

theorem effect (s : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (g : Guard s Rn imm12) :
    ∃ t, (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 0#1 1#1 : SailM Unit) s = .ok () t ∧ projection t = expected s Rn imm12 := by
  have hRn : ¬ (Rn.toNat : Int) = 31 := by have := g.rn; omega
  obtain ⟨u,hu⟩ : ∃ u, effect_native s Rn imm12 = .ok (expected s Rn imm12) u := by
    unfold effect_native expected
    simp only [hRn, ite_true, ite_false, dite_eq_ite, ite_self]
    first | exact ⟨_,rfl⟩ | (split <;> exact ⟨_,rfl⟩)
  have hr := (effect_complete s Rn imm12 g.rn g.el g.a64 g.aa64 g.btype g.btn).trans hu
  exact ⟨_,ArmBridge.RootFrame.ok_of_root _ projection s u (expected s Rn imm12) hr,
    ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s Rn imm12) u) hr⟩
#print axioms effect
end N1D226.CmnImm64Generic
