import HookQuietCounters.PMUCycleParts
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.PMUWriteFrame
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUCycleLoop.PMUPost.counter_count"
  (← IO.getStderr).flush

theorem PMUPost.counter_count {budget : Nat} {s t : NativeState} (f : PMUPost budget s t) :
    t.regs.bank_Int .NUM_PMU_COUNTERS = s.regs.bank_Int .NUM_PMU_COUNTERS := by
  exact frame_pres_E20 (fun r => r.bank_Int .NUM_PMU_COUNTERS)
    (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) f.frame

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUCycleLoop.reset_acc_total"
  (← IO.getStderr).flush

theorem reset_acc_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) :
    ∃ t, (do let a ← readReg PMUEventAccumulator
             writeReg PMUEventAccumulator (vectorUpdate a idx 0) : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  let v := vectorUpdate (PMUEventAccumulator.get s.regs) idx 0
  let t : NativeState := {s with regs := PMUEventAccumulator.set v s.regs}
  exact ⟨t, by simp only [bind_app, read_apply, write_apply]; rfl,
    (write_PMUEventAccumulator budget s q v).2.1⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUCycleLoop.pmu_cycle_body_total"
  (← IO.getStderr).flush

theorem pmu_cycle_body_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Int)
    (h0 : 0 ≤ idx) (hN : idx < s.regs.bank_Int .NUM_PMU_COUNTERS) (h31 : idx < 31) :
    ∃ t, PMUCycleParts.body idx s = .ok () t ∧ PMUPost budget s t := by
  let n := Sail.Int.toNatChecked idx
  have hn : (n : Int) = idx := by
    dsimp only [n]
    rw [BookkeepingGuard.LoopIndexArithmetic.toNatChecked_eq_toNat idx h0]
    omega
  have hn31 : n < 31 := by omega
  have hB32 : ((0 ≤b idx) && (idx ≤b 32)) = true := by simp; omega
  have hB31 : ((0 ≤b idx) && (idx <b 31)) = true := by simp [h0, h31]
  have hi : CountIndexValid n s := Or.inr (Or.inl (by omega))
  obtain ⟨enabled, a, ha, hf⟩ := count_pmu_events_query budget s q n hi
  have fa := PMUPost.of_eraseOcc_eq q hf
  let inc := GetElem?.getElem! (PMUEventAccumulator.get a.regs) n
  obtain ⟨w, hw, fw⟩ := increment_event_counter_total budget a fa.quiet n inc hn31
  cases enabled with
  | false =>
    obtain ⟨t, ht, ft⟩ := reset_acc_total budget a fa.quiet n
    refine ⟨t, ?_, fa.trans ft⟩
    simpa only [PMUCycleParts.body, bind_assoc, bind_if, pure_bind, bind_app, hB32, hB31,
      assert_true, ha, Bool.false_eq_true, reduceIte, n] using ht
  | true =>
    obtain ⟨t, ht, ft⟩ := reset_acc_total budget w fw.quiet n
    refine ⟨t, ?_, (fa.trans fw).trans ft⟩
    simp only [n, inc] at ha hw ht
    simp only [PMUCycleParts.body, bind_assoc, bind_if, pure_bind, bind_app, hB32, hB31,
      assert_true, ha, reduceIte, read_apply, hw]
    exact ht

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUCycleLoop.pmu_cycle_regular_total"
  (← IO.getStderr).flush

theorem pmu_cycle_regular_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (counters : Int)
    (hC : s.regs.bank_Int .NUM_PMU_COUNTERS = counters) :
    ∃ t, PMUCycleParts.regular counters s = .ok () t ∧ PMUPost budget s t := by
  let range : IntRange := [0:counters-1:1]i
  let step : Int → Unit → SailM (ForInStep Unit) := fun i _ => do
    PMUCycleParts.body i
    pure (.yield ())
  let I : Unit → NativeState → Prop := fun _ t => PMUPost budget s t
  have hs : I () s := PMUPost.refl budget s q
  have hstep : ∀ i, i ∈ range → ∀ b t, I b t →
      ∃ v u, step i b t = .ok v u ∧ I (stepValue v) u := by
    intro i hi b t ft
    have bounds : 0 ≤ i ∧ i ≤ counters - 1 := by simpa [range, Membership.mem] using hi
    have hNUM : t.regs.bank_Int .NUM_PMU_COUNTERS = counters := ft.counter_count.trans hC
    have hu : counters ≤ 31 := by rw [← hC]; exact q.pmuCountUpper
    obtain ⟨_, hn, hcount, _, _⟩ := BookkeepingGuard.LoopIndexArithmetic.checked_index_facts i counters bounds.1 bounds.2 hu
    obtain ⟨u, hb, fb⟩ := pmu_cycle_body_total budget t ft.quiet i bounds.1 (by omega) (by omega)
    exact ⟨.yield (), u, by simp only [step, bind_app, hb, pure_apply], ft.trans fb⟩
  obtain ⟨b, t, ht, ft⟩ := range_forIn_preserves range step I hstep () s hs
  cases b
  by_cases hz : counters = 0
  · exact ⟨s, by simp [PMUCycleParts.regular, hz, pure_apply], PMUPost.refl budget s q⟩
  · refine ⟨t, ?_, ft⟩
    simpa [PMUCycleParts.regular, range, step, hz, bind_app, pure_apply, unit_bind] using ht
#print axioms PMUPost.counter_count
#print axioms reset_acc_total
#print axioms pmu_cycle_body_total
#print axioms pmu_cycle_regular_total
end HookQuietCounters
