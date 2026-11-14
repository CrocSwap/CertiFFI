import HookQuietCounters.OverflowParts
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowFacts.eraseOcc_regs"
  (← IO.getStderr).flush

theorem eraseOcc_regs {s t : NativeState} (h : eraseOcc t = eraseOcc s) : t.regs = s.regs := by
  simpa only [eraseOcc] using congrArg (fun x : NativeState => x.regs) h

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowFacts.overflow_preamble"
  (← IO.getStderr).flush

theorem overflow_preamble (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ ovsf, OverflowParts.preamble s =
      .ok (s.regs.bank_Int .NUM_PMU_COUNTERS, ovsf) (afterOcc 516 s) := by
  have hA := have_a64 (afterOcc 516 s) q.a64
  by_cases hc : s.regs.bank_Int .NUM_PMU_COUNTERS < 31
  · have hb : ((0 ≤b s.regs.bank_Int .NUM_PMU_COUNTERS) &&
        (s.regs.bank_Int .NUM_PMU_COUNTERS ≤b 30)) = true := by
      have hl := q.pmuCountLower
      simp; omega
    cases hI : featureValue s .FEAT_PMUv3_ICNTR <;>
      simp [OverflowParts.preamble, bind_assoc, bind_if, pure_bind, bind_app,
        get_num_counters, occ_apply, ubv, hA, HavePMUv3ICNTR, feature_apply,
        afterOcc_feature, hI, read_apply, hc, hb, assert_true, pure_apply, map_apply]
  · cases hI : featureValue s .FEAT_PMUv3_ICNTR <;>
      simp [OverflowParts.preamble, bind_assoc, bind_if, pure_bind, bind_app,
        get_num_counters, occ_apply, ubv, hA, HavePMUv3ICNTR, feature_apply,
        afterOcc_feature, hI, read_apply, hc, pure_apply, map_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowFacts.overflow_callback"
  (← IO.getStderr).flush

theorem overflow_callback (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool)
    (idx : Int) (ovsf : BitVec 64) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hl : 0 ≤ idx) (hu : idx < 64) :
    ∃ (v : BitVec 64) (t : NativeState),
      OverflowParts.callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync idx ovsf s = .ok (.yield v) t ∧ eraseOcc t = eraseOcc s := by
  obtain ⟨hyp, t, ht, hframe⟩ := pmu_hyp_query idx (afterOcc 517 s) ha
  have hr : t.regs = s.regs := eraseOcc_regs hframe
  have hat : featureValue t .FEAT_AA64EL0 = true := by
    unfold featureValue
    rw [hr]
    exact ha
  have hA := have_a64 t hat
  have hb : ((0 ≤b idx) && (idx <b 64)) = true := by simp; omega
  have hresult : ∃ v,
      OverflowParts.callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync idx ovsf s = .ok (.yield v) t := by
    cases hyp <;> cases check_e <;> cases include_hi_name <;> cases include_lo_name <;>
      simp only [OverflowParts.callback, bind_assoc, bind_if, pure_bind] <;>
      simp [bind_app, occ_apply, ubv, ht, hA, hb, assert_true, pure_apply, map_apply, read_apply]
  obtain ⟨v, hv⟩ := hresult
  exact ⟨v, t, hv, hframe.trans rfl⟩

#print axioms overflow_preamble
#print axioms overflow_callback
end HookQuietCounters
