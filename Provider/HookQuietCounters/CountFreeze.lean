import HookQuietCounters.CountSimple
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountFreeze.freezeBit"
  (← IO.getStderr).flush

def freezeBit (resvd : Bool) (s : NativeState) : BitVec 1 :=
  if resvd then _get_MDCR_EL2_Type_HPMFZO (s.regs.bank_BitVec_64 .MDCR_EL2)
  else _get_PMCR_EL0_Type_FZO (s.regs.bank_BitVec_64 .PMCR_EL0)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountFreeze.count_freeze_shape"
  (← IO.getStderr).flush

theorem count_freeze_shape (resvd : Bool) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) :
    CountParts.freeze resvd s =
      (if featureValue s .FEAT_PMUv3p7 then
        if freezeBit resvd s == 1#1 then HiLoPMUOverflow resvd (afterOcc 537 s)
        else .ok false (afterOcc 537 s)
      else .ok false s) := by
  have hA := have_a64 (afterOcc 537 s) ha
  cases resvd <;> cases hF : featureValue s .FEAT_PMUv3p7 <;>
    rcases bit_cases (_get_MDCR_EL2_Type_HPMFZO (s.regs.bank_BitVec_64 .MDCR_EL2)) with hH | hH <;>
    rcases bit_cases (_get_PMCR_EL0_Type_FZO (s.regs.bank_BitVec_64 .PMCR_EL0)) with hP | hP <;>
    simp [CountParts.freeze, freezeBit, bind_assoc, bind_if, pure_bind, bind_app,
      occ_apply, ubv, HavePMUv3p7, feature_apply, hF, hA, hH, hP, read_apply, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountFreeze.count_freeze_query"
  (← IO.getStderr).flush

theorem count_freeze_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (resvd : Bool) :
    QueryResult (CountParts.freeze resvd) s := by
  have qa : ArmCert.HookQuiet.V0.HookQuiet budget (afterOcc 537 s) :=
    ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := afterOcc 537 s) rfl q
  obtain ⟨b, t, ht, hf⟩ := overflow_condition_query budget (afterOcc 537 s) qa
    false false false resvd (!resvd) false false
  have hh : (HiLoPMUOverflow resvd : SailM Bool) (afterOcc 537 s) = .ok b t := by
    simpa only [HiLoPMUOverflow] using ht
  unfold QueryResult
  rw [count_freeze_shape resvd s q.a64]
  split
  · split
    · exact ⟨b, t, hh, hf.trans rfl⟩
    · exact ⟨false, afterOcc 537 s, rfl, rfl⟩
  · exact ⟨false, s, rfl, rfl⟩
#print axioms count_freeze_shape
#print axioms count_freeze_query
end HookQuietCounters
