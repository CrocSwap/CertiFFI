import HookQuietCounters.CountAdjust
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
namespace HookQuietCounters

@[simp] theorem el3_query_regs (s : NativeState) : (el3QueryState s).regs = s.regs := rfl
@[simp] theorem el3_query_feature (s : NativeState) (f : Feature) :
    featureValue (el3QueryState s) f = featureValue s f := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountProhibit.el_query_nonzero"
  (← IO.getStderr).flush

theorem el_query_nonzero (el : BitVec 2) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (he : el ≠ 0#2) :
    (ELUsingAArch32 el : SailM Bool) s = .ok false (el3QueryState s) :=
  el_using_nonzero el s ha he

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountProhibit.prohibitBit"
  (← IO.getStderr).flush

def prohibitBit (s : NativeState) : Bool :=
  (_get_MDCR_EL3_Type_SPME (s.regs.bank_BitVec_64 .MDCR_EL3) == 0#1) &&
    featureValue s .FEAT_PMUv3p7 &&
    (_get_MDCR_EL3_Type_MPMX (s.regs.bank_BitVec_64 .MDCR_EL3) == 0#1)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountProhibit.prohibitState"
  (← IO.getStderr).flush

def prohibitState (ss : SecurityState) (s : NativeState) : NativeState :=
  if ss == SS_Secure then
    if prohibitBit s then el3QueryState (el3QueryState (el3QueryState s))
    else el3QueryState s
  else s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.CountProhibit.count_prohibit_total"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
theorem count_prohibit_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (ss : SecurityState) (resvd : Bool) :
    ∃ b, CountParts.prohibit ss resvd s = .ok b (prohibitState ss s) := by
  obtain ⟨db, hd⟩ := external_debug_total (el3QueryState (el3QueryState (el3QueryState s)))
  have ha : featureValue s .FEAT_AA64EL0 = true := q.a64
  cases ss
  case SS_Secure =>
    cases h7 : featureValue s .FEAT_PMUv3p7 <;>
    cases hD : featureValue s .FEAT_Debugv8p2 <;>
    rcases bit_cases (_get_MDCR_EL3_Type_SPME (s.regs.bank_BitVec_64 .MDCR_EL3)) with hS | hS <;>
    rcases bit_cases (_get_MDCR_EL3_Type_MPMX (s.regs.bank_BitVec_64 .MDCR_EL3)) with hM | hM <;>
    simp [CountParts.prohibit, prohibitState, prohibitBit,
      bind_assoc, bind_if, pure_bind, bind_app, pure_apply, map_apply, if_apply,
      HaveEL, HavePMUv3p7, HaveNoSecurePMUDisableOverride, feature_apply,
      el_query_nonzero, ha, el3_query_feature, read_apply, el3_query_regs,
      h7, hD, hS, hM, hd, q.el0, EL0, EL1, EL2, EL3,
      security_eq_secure]
  all_goals
    cases h7 : featureValue s .FEAT_PMUv3p7 <;>
      simp [CountParts.prohibit, prohibitState, prohibitBit,
      bind_assoc, bind_if, pure_bind, bind_app, pure_apply, map_apply, if_apply,
      HaveEL, HavePMUv3p7, HaveNoSecurePMUDisableOverride, feature_apply,
      el_query_nonzero, ha, el3_query_feature, read_apply, el3_query_regs,
      h7, hd, q.el0, EL0, EL1, EL2, EL3,
      security_eq_secure]
#print axioms count_prohibit_total
end HookQuietCounters
