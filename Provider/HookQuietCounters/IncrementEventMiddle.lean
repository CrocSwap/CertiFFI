import HookQuietCounters.IncrementEventParts
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.IncrementEventMiddle.increment_event_prefix"
  (← IO.getStderr).flush

theorem increment_event_prefix (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (inc : Int) (hn : idx < 31) :
    ∃ values t, IncrementEventParts.prefixStage idx inc s = .ok values t ∧ PMUPost budget s t := by
  obtain ⟨v, t, hv, fv⟩ := pmu_count_value_total budget s q idx inc hn
  let old : Int := BitVec.toNat (GetElem?.getElem! (s.regs.bank_Vector_BitVec_64_32 .PMEVCNTR_EL0) idx)
  refine ⟨(old, old + v), t, ?_, fv⟩
  simp only [IncrementEventParts.prefixStage, bind_app, read_apply, hv, pure_apply]
  rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.IncrementEventMiddle.increment_event_middle"
  (← IO.getStderr).flush

theorem increment_event_middle (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (newValue : Int) :
    ∃ (lp : BitVec 1) (width : Int) (t : NativeState),
      IncrementEventParts.middle idx newValue s = .ok (lp, width) t ∧
      PMUPost budget s t ∧ (width = 32 ∨ width = 64) := by
  let a := afterOcc 2422 s
  have fa : PMUPost budget s a := PMUPost.of_eraseOcc_eq (s := s) (t := a) q rfl
  cases h5 : featureValue s .FEAT_PMUv3p5 with
  | false =>
    let value := vectorUpdate (PMEVCNTR_EL0.get a.regs) idx
      (Sail.BitVec.zeroExtend (integer_subrange newValue 31 0) 64)
    let t : NativeState := {a with regs := PMEVCNTR_EL0.set value a.regs}
    have fw := (write_PMEVCNTR_EL0 budget a fa.quiet value).2.1
    refine ⟨oracleChoiceSource.chooseAt (.bitvector 1) (.occ 2422 (s.choiceOcc.getD 2422 0)) s.choiceState, 32, t, ?_, fa.trans fw, Or.inl rfl⟩
    simp only [IncrementEventParts.middle, bind_app, occ_apply, ubv, HavePMUv3p5,
      feature_apply, afterOcc_feature, h5, Bool.false_eq_true, reduceIte, read_apply,
      write_apply, pure_apply]
    rfl
  | true =>
    let value := vectorUpdate (PMEVCNTR_EL0.get a.regs) idx
      (integer_subrange newValue 63 0)
    let w : NativeState := {a with regs := PMEVCNTR_EL0.set value a.regs}
    have fw := (write_PMEVCNTR_EL0 budget a fa.quiet value).2.1
    obtain ⟨hyp, t, hh, hf⟩ := pmu_hyp_query (idx : Int) w fw.quiet.a64
    have fh := PMUPost.of_eraseOcc_eq fw.quiet hf
    simp only [w, value, a] at hh
    cases hyp with
    | false =>
      let lp := _get_PMCR_EL0_Type_LP (t.regs.bank_BitVec_64 .PMCR_EL0)
      refine ⟨lp, (if lp == 1#1 then 64 else 32), t, ?_, (fa.trans fw).trans fh, ?_⟩
      · simp only [IncrementEventParts.middle, bind_app, occ_apply, ubv, HavePMUv3p5,
          feature_apply, afterOcc_feature, h5, reduceIte, read_apply, write_apply,
          hh, Bool.false_eq_true, pure_apply]
        rfl
      · split <;> simp
    | true =>
      let lp := _get_MDCR_EL2_Type_HLP (t.regs.bank_BitVec_64 .MDCR_EL2)
      refine ⟨lp, (if lp == 1#1 then 64 else 32), t, ?_, (fa.trans fw).trans fh, ?_⟩
      · simp only [IncrementEventParts.middle, bind_app, occ_apply, ubv, HavePMUv3p5,
          feature_apply, afterOcc_feature, h5, reduceIte, read_apply, write_apply, hh, pure_apply]
        rfl
      · split <;> simp
#print axioms increment_event_prefix
#print axioms increment_event_middle
end HookQuietCounters
