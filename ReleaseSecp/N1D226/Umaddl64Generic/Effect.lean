import N1D226.Umaddl64Generic.Root
import Bridge.RootFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
namespace N1D226.Umaddl64Generic
open ArmBridge.Draft
noncomputable def expected (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Regs × Std.ExtHashMap Nat (BitVec 8) × Array Event :=
  match effect_native s Rd Rn Rm with
  | .ok v _ => v
  | .error _ _ => (s.regs,s.mem,s.events)
def projection (s : NativeState) := (s.regs,s.mem,s.events)
structure Guard (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) : Prop where
  rd : Rd.toNat < 31
  rn : Rn.toNat < 31
  rm : Rm.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2

theorem effect (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (g : Guard s Rd Rn Rm) :
    ∃ t, (decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn 31#5 0#1 Rm 1#1 : SailM Unit) s = .ok () t ∧ projection t = expected s Rd Rn Rm := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by have := g.rd; omega
  have hRn : ¬ (Rn.toNat : Int) = 31 := by have := g.rn; omega
  have hRm : ¬ (Rm.toNat : Int) = 31 := by have := g.rm; omega
  obtain ⟨u,hu⟩ : ∃ u, effect_native s Rd Rn Rm = .ok (expected s Rd Rn Rm) u := by
    unfold effect_native expected
    simp only [hRd, hRn, hRm, ite_true, ite_false, dite_eq_ite, ite_self]
    first | exact ⟨_,rfl⟩ | (split <;> exact ⟨_,rfl⟩)
  have hr := (effect_complete s Rd Rn Rm g.rd g.rn g.rm g.el g.a64 g.aa64 g.btype g.btn).trans hu
  exact ⟨_,ArmBridge.RootFrame.ok_of_root _ projection s u (expected s Rd Rn Rm) hr,
    ArmBridge.RootFrame.val_of_root _ projection s (.ok (expected s Rd Rn Rm) u) hr⟩
#print axioms effect
end N1D226.Umaddl64Generic
