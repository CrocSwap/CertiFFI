import HookQuietCounters.PMUOff
import HookQuietCounters.Range
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUBody.featureValue"
  (← IO.getStderr).flush

def featureValue (s : NativeState) (f : Feature) : Bool :=
  s.regs.FeatureImpl[Sail.Int.toNatChecked (num_of_Feature f)]!

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUBody.feature_apply"
  (← IO.getStderr).flush

theorem feature_apply (f : Feature) (s : NativeState) :
    (IsFeatureImplemented f : SailM Bool) s = .ok (featureValue s f) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUBody.have_a64"
  (← IO.getStderr).flush

theorem have_a64 (s : NativeState) (h : featureValue s .FEAT_AA64EL0 = true) :
    (HaveAArch64 () : SailM Bool) s = .ok true s := by
  simp [HaveAArch64, bind_app, pure_apply, feature_apply, h]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUBody.using_a64"
  (← IO.getStderr).flush

theorem using_a64 (s : NativeState) (h : featureValue s .FEAT_AA64EL0 = true)
    (hn : s.regs.PSTATE.nRW = 0#1) :
    (UsingAArch32 () : SailM Bool) s = .ok false s := by
  have hr : (readReg PSTATE : SailM ProcState) s = .ok s.regs.PSTATE s := rfl
  simp [UsingAArch32, bind_app, pure_apply, hr, HaveAArch32, have_a64 s h, hn]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUBody.assert_true"
  (← IO.getStderr).flush

theorem assert_true (msg : String) (s : NativeState) :
    (ArmFull.assert true msg : SailM Unit) s = .ok () s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUBody.pmu_event2_acc"
  (← IO.getStderr).flush

theorem pmu_event2_acc (e : BitVec 16) (inc idx : Int) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hn : s.regs.PSTATE.nRW = 0#1)
    (hl : 0 ≤ idx) (hu : idx < 31) :
    ∃ acc, (PMUEvent__2 e inc idx : SailM Unit) s =
      .ok () {s with regs := {s.regs with PMUEventAccumulator := acc}} := by
  have hp : (HavePMUv3 () : SailM Bool) s = .ok (featureValue s .FEAT_PMUv3) s := rfl
  have ht : (readReg PMEVTYPER_EL0 : SailM (Vector (BitVec 64) 32)) s =
    .ok (s.regs.bank_Vector_BitVec_64_32 .PMEVTYPER_EL0) s := rfl
  have hr : (readReg PMUEventAccumulator : SailM (Vector Int 31)) s =
    .ok s.regs.PMUEventAccumulator s := rfl
  have hb32 : ((0 ≤b idx) && (idx <b 32)) = true := by simp; omega
  have hb31 : ((0 ≤b idx) && (idx <b 31)) = true := by simp; omega
  cases hpv : featureValue s .FEAT_PMUv3 with
  | false =>
    simp only [PMUEvent__2, bind_app, hp, hpv, Bool.not_false,
      ↓reduceIte, pure_apply]
    exact ⟨s.regs.PMUEventAccumulator, rfl⟩
  | true =>
    simp only [PMUEvent__2, bind_app, hp, hpv, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, using_a64 s ha hn, hb32, hb31,
      assert_true, pure_apply, ht]
    split
    · simp only [bind_app, hr]
      exact ⟨_, rfl⟩
    · exact ⟨s.regs.PMUEventAccumulator, rfl⟩

#print axioms have_a64
#print axioms using_a64
#print axioms pmu_event2_acc

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUBody.eventLoop"
  (← IO.getStderr).flush

def eventLoop (e : BitVec 16) (inc counters : Int) : SailM Unit := do
  let mut loop_vars := ()
  for idx in [0:counters-1:1]i do
    let () := loop_vars
    loop_vars ← do PMUEvent__2 e inc idx
  pure loop_vars

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUBody.event_loop_acc"
  (← IO.getStderr).flush

theorem event_loop_acc (e : BitVec 16) (inc counters : Int) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hn : s.regs.PSTATE.nRW = 0#1)
    (hu : counters ≤ 31) :
    ∃ acc, eventLoop e inc counters s =
      .ok () {s with regs := {s.regs with PMUEventAccumulator := acc}} := by
  let range : IntRange := [0:counters-1:1]i
  let I : Unit → NativeState → Prop := fun _ t =>
    ∃ acc, t = {s with regs := {s.regs with PMUEventAccumulator := acc}}
  let body : Int → Unit → SailM (ForInStep Unit) := fun i _ => do
    PMUEvent__2 e inc i
    pure (.yield ())
  have hs : I () s := ⟨s.regs.PMUEventAccumulator, rfl⟩
  have hstep : ∀ i, i ∈ range → ∀ b t, I b t →
      ∃ v u, body i b t = .ok v u ∧ I (stepValue v) u := by
    intro i hi b t ht
    obtain ⟨acc, rfl⟩ := ht
    have bounds : 0 ≤ i ∧ i ≤ counters - 1 := by
      simpa [range, Membership.mem] using hi
    obtain ⟨next, hnext⟩ := pmu_event2_acc e inc i
      {s with regs := {s.regs with PMUEventAccumulator := acc}} ha hn bounds.1 (by omega)
    refine ⟨.yield (), {s with regs := {s.regs with PMUEventAccumulator := next}}, ?_, ?_⟩
    · simp only [body, bind_app, hnext, pure_apply]
    · exact ⟨next, rfl⟩
  obtain ⟨b, t, ht, hI⟩ := range_forIn_preserves range body I hstep () s hs
  obtain ⟨acc, rfl⟩ := hI
  cases b
  refine ⟨acc, ?_⟩
  change ((forIn range () body) >>= fun b => pure b) s = _
  simp only [bind_app, ht, pure_apply]

#print axioms event_loop_acc

end HookQuietCounters
