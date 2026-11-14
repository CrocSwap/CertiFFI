import HookQuietCounters.OverflowTail
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowRun.overflow_loop"
  (← IO.getStderr).flush

theorem overflow_loop (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool)
    (counters : Int) (ovsf : BitVec 64) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hu : counters ≤ 31) :
    QueryResult (OverflowParts.loop check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync counters ovsf) s := by
  let range : IntRange := [0:counters-1:1]i
  let body := OverflowParts.callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync
  let I : BitVec 64 → NativeState → Prop := fun _ t => eraseOcc t = eraseOcc s
  have hs : I ovsf s := rfl
  have hstep : ∀ i, i ∈ range → ∀ b t, I b t →
      ∃ v u, body i b t = .ok v u ∧ I (stepValue v) u := by
    intro i hi b t ht
    have bounds : 0 ≤ i ∧ i ≤ counters-1 := by simpa [range, Membership.mem] using hi
    have hr : t.regs = s.regs := eraseOcc_regs ht
    have hat : featureValue t .FEAT_AA64EL0 = true := by
      unfold featureValue
      rw [hr]
      exact ha
    obtain ⟨v, u, hv, hf⟩ := overflow_callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync
      i b t hat bounds.1 (by omega)
    exact ⟨.yield v, u, hv, hf.trans ht⟩
  exact range_forIn_preserves range body I hstep ovsf s hs

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowRun.overflow_condition_query"
  (← IO.getStderr).flush

theorem overflow_condition_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)
    (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) :
    QueryResult (PMUOverflowCondition check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync) s := by
  obtain ⟨ovsf, hp⟩ := overflow_preamble budget s q
  obtain ⟨v, t, hl, hf⟩ := overflow_loop check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync
    (s.regs.bank_Int .NUM_PMU_COUNTERS) ovsf (afterOcc 516 s) q.a64 q.pmuCountUpper
  have hr : t.regs = s.regs := eraseOcc_regs hf
  have hat : featureValue t .FEAT_AA64EL0 = true := by
    unfold featureValue
    rw [hr]
    exact q.a64
  obtain ⟨b, ht⟩ := overflow_tail check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync v t hat
  refine ⟨b, t, ?_, hf.trans rfl⟩
  rw [OverflowParts.equation]
  simp only [bind_app, hp, hl, ht]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowRun.overflow_condition_masked"
  (← IO.getStderr).flush

theorem overflow_condition_masked (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)
    (check_e check_cnten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) :
    ∃ t, (PMUOverflowCondition check_e check_cnten true include_hi_name include_lo_name exclude_cyc exclude_sync : SailM Bool) s =
      .ok false t ∧ eraseOcc t = eraseOcc s := by
  obtain ⟨ovsf, hp⟩ := overflow_preamble budget s q
  obtain ⟨v, t, hl, hf⟩ := overflow_loop check_e check_cnten true include_hi_name include_lo_name exclude_cyc exclude_sync
    (s.regs.bank_Int .NUM_PMU_COUNTERS) ovsf (afterOcc 516 s) q.a64 q.pmuCountUpper
  have hr : t.regs = s.regs := eraseOcc_regs hf
  have hat : featureValue t .FEAT_AA64EL0 = true := by
    unfold featureValue
    rw [hr]
    exact q.a64
  have hm : t.regs.bank_BitVec_64 .PMINTENCLR_EL1 = 0#64 := by rw [hr]; exact q.pmuIrqMask
  have ht := overflow_tail_masked check_e check_cnten include_hi_name include_lo_name exclude_cyc exclude_sync v t hat hm
  refine ⟨t, ?_, hf.trans rfl⟩
  rw [OverflowParts.equation]
  simp only [bind_app, hp, hl, ht]

#print axioms overflow_loop
#print axioms overflow_condition_query
#print axioms overflow_condition_masked
end HookQuietCounters
