import HookQuietCounters.CountStartParts
import HookQuietCounters.CountProhibit
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
set_option linter.unusedSimpArgs false
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountStart.CountIndexValid"
  (← IO.getStderr).flush

def CountIndexValid (idx : Nat) (s : NativeState) : Prop :=
  idx = CYCLE_COUNTER_ID ∨ (idx : Int) < s.regs.bank_Int .NUM_PMU_COUNTERS ∨
    (idx = INSTRUCTION_COUNTER_ID ∧ featureValue s .FEAT_PMUv3_ICNTR = true)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountStart.countCheckState"
  (← IO.getStderr).flush

def countCheckState (s : NativeState) : NativeState :=
  afterOcc 533 (afterOcc 532 (afterOcc 531 (afterOcc 530 s)))

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountStart.countTailState"
  (← IO.getStderr).flush

def countTailState (s : NativeState) : NativeState :=
  afterOcc 536 (afterOcc 535 (afterOcc 534 s))

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountStart.count_check_total"
  (← IO.getStderr).flush

theorem count_check_total (s : NativeState) (idx : Nat) (hi : CountIndexValid idx s) :
    CountStartParts.check idx s = .ok () (countCheckState s) := by
  rcases hi with hc | hl | ⟨hI, hIC⟩
  · subst idx
    simp [CountStartParts.check, countCheckState, bind_assoc, bind_if, pure_bind,
      bind_app, occ_apply, ubv, get_num_counters, CYCLE_COUNTER_ID,
      assert_true, pure_apply]
  · simp [CountStartParts.check, countCheckState, bind_assoc, bind_if, pure_bind,
      bind_app, occ_apply, ubv, get_num_counters, hl, assert_true, pure_apply]
  · subst idx
    simp [CountStartParts.check, countCheckState, bind_assoc, bind_if, pure_bind,
      bind_app, occ_apply, ubv, get_num_counters, INSTRUCTION_COUNTER_ID, CYCLE_COUNTER_ID,
      HavePMUv3ICNTR, feature_apply, afterOcc_feature, hIC, assert_true, pure_apply]
    split <;> simp [bind_app, feature_apply, afterOcc_feature, hIC, assert_true, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountStart.count_start_tail_query"
  (← IO.getStderr).flush

theorem count_start_tail_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) :
    QueryResult (CountStartParts.tail idx) s := by
  obtain ⟨debug, hd⟩ := halted_total (countTailState s)
  obtain ⟨resvd, t, hh, hf⟩ := pmu_hyp_query (idx : Int) (countTailState s) q.a64
  have hr : t.regs = s.regs := eraseOcc_regs hf
  have qt := ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := t) hr.symm q
  have hS := current_security_quiet budget t qt
  have hv : ∃ v, CountStartParts.tail idx s = .ok v (securityQueryState t) := by
    simp only [countTailState] at hd hh
    simp [CountStartParts.tail, bind_assoc, pure_bind, bind_app, occ_apply,
      ubool, ubv, hd, hh, hS, pure_apply, map_apply]
  obtain ⟨v, hv⟩ := hv
  exact ⟨v, securityQueryState t, hv, (erase_security_query t).trans (hf.trans rfl)⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountStart.count_start_query"
  (← IO.getStderr).flush

theorem count_start_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (hi : CountIndexValid idx s) :
    QueryResult (CountParts.start idx) s := by
  have hc := count_check_total s idx hi
  have qa : ArmCert.HookQuiet.V0.HookQuiet budget (countCheckState s) :=
    ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := countCheckState s) rfl q
  obtain ⟨v, t, ht, hf⟩ := count_start_tail_query budget (countCheckState s) qa idx
  refine ⟨v, t, ?_, hf.trans rfl⟩
  rw [CountStartParts.equation]
  simp only [bind_app, hc, ht]
#print axioms count_check_total
#print axioms count_start_tail_query
#print axioms count_start_query
end HookQuietCounters
