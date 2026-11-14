import NativeEntryCallerParts.Frames
import NativeEntryCallerParts.AddrTopRoot
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryCallerParts
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem top_55_or_63 (p : Prop) [Decidable p] :
    (if p then (55 : Int) else 63) = 55 ∨ (if p then (55 : Int) else 63) = 63 := by
  split <;> simp_all

theorem top_run (target : BitVec 64) (s : NativeState) (hp : CallerControls s)
    (bit55 : BitVec.access target 55 = 0#1) :
    ∃ n t, (AddrTop target true 0#2 : SailM Int) s = .ok n t ∧ (n = 55 ∨ n = 63) := by
  rw [top_complete target s hp.f4 hp.f2 hp.f3 hp.f6 hp.f7 hp.rme hp.vhe hp.brbe hp.el hp.nrw hp.e2h hp.tge hp.ns hp.pmb hp.spe hp.pmbs hp.nspb hp.nspbe bit55]
  unfold top_native
  simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false]
  first
  | exact ⟨_, _, rfl, top_55_or_63 _⟩
  | (split <;> exact ⟨_, _, rfl, top_55_or_63 _⟩)

theorem low_address_run (target : BitVec 64) (s : NativeState) (hp : CallerControls s)
    (low : target.toNat < 2^55) :
    ∃ t, (AArch64_BranchAddr target 0#2 : SailM (BitVec 64)) s = .ok target t := by
  have bit := low_bit55 target low
  have joined : BitVec.join1 [BitVec.access target 55] = 0#1 := by rw [bit]; rfl
  have n55 : Sail.Int.toNatChecked (55 : Int) = 55 := rfl
  have z55 : BitVec.setWidth 1 (BitVec.join1 [BitVec.access target (Sail.Int.toNatChecked 55)]) = 0#1 := by
    rw [n55, joined]
    rfl
  have diff : ((0#1 : BitVec 1) == 1#1) = false := rfl
  obtain ⟨n, t, top, range⟩ := top_run target s hp bit
  unfold AArch64_BranchAddr
  simp only [↓bind_app, using32_run s hp, Bool.not_false, ArmFull.assert,
    pure_run, assert_run]
  rw [top]
  rcases range with rfl | rfl
  · simp only [↓bind_app, Int.reduceBEq, Int.reduceLE, Int.reduceLT,
      Bool.false_eq_true, Bool.true_and, Bool.false_and, Bool.true_or,
      Bool.cond_true, Bool.cond_false, Bool.not_true, Bool.not_false, ite_true, ite_false,
      pure_run, assert_run, PreSail.readReg_apply, z55, diff, n55, joined, BitVec.setWidth_eq]
    exact ⟨_, congrArg (fun v => EStateM.Result.ok v t) (low_untag target low)⟩
  · simp only [↓bind_app, Int.reduceBEq, ite_true, pure_run]
    exact ⟨_, rfl⟩

theorem address_low (target : BitVec 64) (s : NativeState) (hp : CallerControls s)
    (low : target.toNat < 2^55) : addressValue target s = target := by
  obtain ⟨t, run⟩ := low_address_run target s hp low
  have actual := address_run target s hp (low_bit55 target low)
  have same := actual.symm.trans run
  exact congrArg (fun r => match r with | .ok value _ => value | .error _ _ => 0#64) same

#print axioms top_55_or_63
#print axioms top_run
#print axioms low_address_run
#print axioms address_low
end NativeEntryCallerParts
