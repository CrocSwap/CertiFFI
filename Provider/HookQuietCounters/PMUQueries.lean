import HookQuietCounters.PMUEventNonRetired
import HookQuietCounters.TimerCompose
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUQueries.QueryResult"
  (← IO.getStderr).flush

def QueryResult {α : Type} (x : SailM α) (s : NativeState) : Prop :=
  ∃ v t, x s = .ok v t ∧ eraseOcc t = eraseOcc s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUQueries.query_bind"
  (← IO.getStderr).flush

theorem query_bind {α β : Type} (x : SailM α) (f : α → SailM β) (s : NativeState)
    (hx : QueryResult x s)
    (hf : ∀ v t, eraseOcc t = eraseOcc s → QueryResult (f v) t) :
    QueryResult (x >>= f) s := by
  obtain ⟨v, t, hx, ht⟩ := hx
  obtain ⟨w, u, hf, hu⟩ := hf v t ht
  exact ⟨w, u, by simp only [bind_app, hx, hf], hu.trans ht⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUQueries.query_pure"
  (← IO.getStderr).flush

theorem query_pure {α : Type} (v : α) (s : NativeState) : QueryResult (pure v) s :=
  ⟨v, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUQueries.query_read"
  (← IO.getStderr).flush

theorem query_read {α : Type} (r : RegisterRef Regs α) (s : NativeState) :
    QueryResult (readReg r) s := ⟨r.get s.regs, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUQueries.halted_total"
  (← IO.getStderr).flush

theorem halted_total (s : NativeState) : ∃ b, (Halted () : SailM Bool) s = .ok b s := by
  have hED : (EDSCR_read () : SailM (BitVec 32)) s =
      .ok (Sail.BitVec.updateSubrange (s.regs.bank_BitVec_32 ._EDSCR) 30 29
        (BitVec.slice (s.regs.bank_BitVec_64 .MDCCSR_EL0) 29 2)) s := rfl
  simp only [Halted, bind_assoc, bind_if, pure_bind]
  simp only [bind_app, hED, pure_apply, map_apply, if_apply]
  repeat' first | split | exact ⟨_, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUQueries.external_debug_total"
  (← IO.getStderr).flush

theorem external_debug_total (s : NativeState) :
    ∃ b, (ExternalSecureNoninvasiveDebugEnabled () : SailM Bool) s = .ok b s := by
  cases hF : featureValue s .FEAT_Debugv8p4 <;>
    simp only [ExternalSecureNoninvasiveDebugEnabled, ExternalSecureInvasiveDebugEnabled,
      ExternalNoninvasiveDebugEnabled, ExternalInvasiveDebugEnabled,
      HaveNoninvasiveDebugAuth, HaveEL, bind_assoc, bind_if, pure_bind]
  all_goals simp only [bind_app, pure_apply, map_apply, if_apply,
      Bool.not_true, Bool.false_eq_true, reduceIte, feature_apply, hF, read_apply,
      Bool.not_false]
  all_goals repeat'
    try simp only [bind_app, pure_apply, map_apply, if_apply, read_apply]
    first | split | exact ⟨_, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUQueries.pmu_hyp_query"
  (← IO.getStderr).flush

theorem pmu_hyp_query (n : Int) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) : QueryResult (PMUCounterIsHyp n) s := by
  have hA := have_a64 (afterOcc 515 s) ha
  by_cases hI : n = (INSTRUCTION_COUNTER_ID : Int) <;>
    by_cases hC : n = (CYCLE_COUNTER_ID : Int) <;>
    cases hF : featureValue s .FEAT_HPMN0 <;>
    simp only [PMUCounterIsHyp, bind_assoc, bind_if, pure_bind] <;>
    simp only [QueryResult, bind_app, pure_apply, map_apply, if_apply,
      hI, hC, occ_apply, ubool, HaveEL, hA, read_apply, get_num_counters,
      HaveFeatHPMN0, feature_apply, afterOcc_feature, hF, ConstrainUnpredictableBool,
      beq_iff_eq, Bool.false_eq_true, reduceIte]
  all_goals repeat'
    try simp only [bind_app, pure_apply, map_apply, if_apply, read_apply, occ_apply, ubool,
      feature_apply, afterOcc_feature, hF, Bool.false_eq_true, reduceIte]
    first | split | exact ⟨_, _, rfl, rfl⟩
#print axioms query_bind
#print axioms halted_total
#print axioms external_debug_total
#print axioms pmu_hyp_query
end HookQuietCounters
