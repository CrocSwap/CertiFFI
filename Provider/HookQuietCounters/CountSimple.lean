import HookQuietCounters.CountParts
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountSimple.count_enable_total"
  (← IO.getStderr).flush

theorem count_enable_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (resvd : Bool) :
    ∃ b, CountParts.enable idx resvd s = .ok b s := by
  cases resvd <;>
    by_cases hI : idx = INSTRUCTION_COUNTER_ID <;>
    by_cases hC : idx = CYCLE_COUNTER_ID <;>
    rcases bit_cases (_get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0)) with hE | hE <;>
    rcases bit_cases (_get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2)) with hH | hH <;>
    simp_all [CountParts.enable, bind_assoc, bind_if, pure_bind, bind_app,
      hI, hC, hE, hH, INSTRUCTION_COUNTER_ID, CYCLE_COUNTER_ID, have_a64 s q.a64, assert_true, read_apply, pure_apply, map_apply, if_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountSimple.count_filter_total"
  (← IO.getStderr).flush

theorem count_filter_total (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true)
    (idx : Nat) (hi : idx = INSTRUCTION_COUNTER_ID ∨ idx = CYCLE_COUNTER_ID ∨ idx < 32) :
    ∃ filter, CountParts.getFilter idx s = .ok filter (afterOcc 538 s) := by
  have hA := have_a64 (afterOcc 538 s) ha
  have hb : idx = INSTRUCTION_COUNTER_ID ∨ idx = CYCLE_COUNTER_ID ∨ ((0 ≤b idx) && (idx <b 32)) = true := by
    rcases hi with hi | hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (by simp; omega))
  by_cases hI : idx = INSTRUCTION_COUNTER_ID <;>
    by_cases hC : idx = CYCLE_COUNTER_ID <;>
    simp_all [CountParts.getFilter, bind_assoc, bind_if, pure_bind, bind_app,
      INSTRUCTION_COUNTER_ID, CYCLE_COUNTER_ID,
      occ_apply, ubv, hA, read_apply, assert_true, pure_apply, map_apply, if_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountSimple.count_finish_total"
  (← IO.getStderr).flush

theorem count_finish_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)
    (debug enabled frozen prohibited filtered : Bool) (filter : BitVec 32) :
    ∃ b, CountParts.finish debug enabled frozen prohibited filtered filter s =
      .ok b (securityQueryState s) := by
  have hA := have_a64 s q.a64
  cases hS : featureValue s .FEAT_SEL2 <;>
    cases hR : featureValue s .FEAT_RME <;>
    cases hSS : securityValue s <;>
    simp [CountParts.finish, bind_assoc, bind_if, pure_bind, bind_app,
      HaveEL, hA, HaveSecureEL2Ext, HaveRME, feature_apply, hS, hR,
      current_security_quiet budget s q, hSS, read_apply, security_query_regs,
      q.el0, EL0, pure_apply, map_apply, if_apply]
#print axioms count_enable_total
#print axioms count_filter_total
#print axioms count_finish_total
end HookQuietCounters
