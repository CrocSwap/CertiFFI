import HookQuietCounters.CountStart
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountRun.quiet_of_eraseOcc_eq"
  (← IO.getStderr).flush

theorem quiet_of_eraseOcc_eq {budget : Nat} {s t : NativeState}
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (h : eraseOcc t = eraseOcc s) :
    ArmCert.HookQuiet.V0.HookQuiet budget t :=
  ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := t) (eraseOcc_regs h).symm q

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountRun.erase_el3_query"
  (← IO.getStderr).flush

theorem erase_el3_query (s : NativeState) : eraseOcc (el3QueryState s) = eraseOcc s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountRun.erase_prohibit_state"
  (← IO.getStderr).flush

theorem erase_prohibit_state (ss : SecurityState) (s : NativeState) :
    eraseOcc (prohibitState ss s) = eraseOcc s := by
  unfold prohibitState
  split
  · split <;> simp only [erase_el3_query]
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountRun.count_index_bounds"
  (← IO.getStderr).flush

theorem count_index_bounds (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (h : CountIndexValid idx s) :
    idx = INSTRUCTION_COUNTER_ID ∨ idx = CYCLE_COUNTER_ID ∨ idx < 32 := by
  rcases h with h | h | ⟨h, _⟩
  · exact Or.inr (Or.inl h)
  · have hu := q.pmuCountUpper
    exact Or.inr (Or.inr (by omega))
  · exact Or.inl h

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountRun.count_pmu_events_query"
  (← IO.getStderr).flush

theorem count_pmu_events_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (h : CountIndexValid idx s) :
    QueryResult (CountPMUEvents idx) s := by
  obtain ⟨v0, s1, h0, f0⟩ := count_start_query budget s q idx h
  rcases v0 with ⟨debug, resvd, ss, filtered⟩
  have q1 := quiet_of_eraseOcc_eq q f0
  obtain ⟨enabled, he⟩ := count_enable_total budget s1 q1 idx resvd
  obtain ⟨prohibited, hp⟩ := count_prohibit_total budget s1 q1 ss resvd
  let s2 := prohibitState ss s1
  have f1 : eraseOcc s2 = eraseOcc s1 := erase_prohibit_state ss s1
  have q2 := quiet_of_eraseOcc_eq q1 f1
  obtain ⟨frozen, s3, hf, f2⟩ := count_freeze_query budget s2 q2 resvd
  have q3 := quiet_of_eraseOcc_eq q2 f2
  obtain ⟨v3, ha⟩ := count_adjust_total budget s3 q3 idx ss resvd enabled frozen prohibited
  rcases v3 with ⟨enabled3, frozen3, prohibited3⟩
  obtain ⟨filter, hg⟩ := count_filter_total s3 q3.a64 idx (count_index_bounds budget s q idx h)
  let s4 := afterOcc 538 s3
  have f3 : eraseOcc s4 = eraseOcc s3 := rfl
  have q4 := quiet_of_eraseOcc_eq q3 f3
  obtain ⟨result, hz⟩ := count_finish_total budget s4 q4 debug enabled3 frozen3 prohibited3 filtered filter
  refine ⟨result, securityQueryState s4, ?_, ?_⟩
  · rw [CountParts.equation]
    simp only [s2] at hf
    simp only [s4] at hz
    simp only [bind_app, h0, he, hp, hf, ha, hg, hz]
    all_goals rfl
  · exact (erase_security_query s4).trans (f3.trans (f2.trans (f1.trans f0)))
#print axioms count_pmu_events_query
end HookQuietCounters
