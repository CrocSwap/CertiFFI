import ArmCertWalk.WalkTrafficRecords
import ArmCertCTOrdered.OrderedEventV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.EntryTraffic
open ArmCertWalk ArmCertCT.Native
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! coverage of an ACTUAL TranslateAddress raw delta (Memory 4b87dc78):
after the translation's initial history, the appended raw events are one
explicit delta, and every event in it has an ordered V2 record. No event is
dropped, merged or defaulted. -/

theorem record_some_of_traffic (e : Event) (h : (V2.trafficRec e).isSome = true) :
    (ArmCertCTOrdered.OrderedEventV2.record e).isSome = true := by
  unfold ArmCertCTOrdered.OrderedEventV2.record
  split
  · rfl
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    rw [hv]; rfl

theorem all_some_mem {l : List (Option V2.TrafficRec)} (h : ∀ x ∈ l, x.isSome = true)
    (delta : Array Event) (hmap : delta.toList.map V2.trafficRec = l) :
    ArmCertCTOrdered.OrderedEventV2.Covered delta := by
  intro e he
  apply record_some_of_traffic
  exact h _ (hmap ▸ List.mem_map_of_mem he)

theorem step_records_some (pa : Nat) (updated : Bool) :
    ∀ x ∈ stepRecords pa updated, x.isSome = true := by
  unfold stepRecords; split <;> simp

theorem leaf_records_some (pa : Nat) (updated : Bool) :
    ∀ x ∈ leafRecords pa updated, x.isSome = true := by
  unfold leafRecords; split <;> simp

theorem covered_append {a b : Array Event} (ha : ArmCertCTOrdered.OrderedEventV2.Covered a)
    (hb : ArmCertCTOrdered.OrderedEventV2.Covered b) : ArmCertCTOrdered.OrderedEventV2.Covered (a ++ b) := by
  intro e he
  rw [Array.toList_append, List.mem_append] at he
  rcases he with h | h
  · exact ha e h
  · exact hb e h

theorem fold_delta (steps : List (Nat × Bool × Array Event)) (base : Array Event)
    (hsteps : ∀ step ∈ steps, WalkStepTraffic step.1 step.2.1 step.2.2) :
    ∃ d, steps.foldl (fun events step => events ++ step.2.2) base = base ++ d ∧
      ArmCertCTOrdered.OrderedEventV2.Covered d := by
  induction steps generalizing base with
  | nil => exact ⟨#[], by simp, fun _ h => by simp at h⟩
  | cons step rest ih =>
    obtain ⟨d, hd, cov⟩ := ih (base ++ step.2.2) (fun s hs => hsteps s (List.mem_cons_of_mem _ hs))
    refine ⟨step.2.2 ++ d, ?_, covered_append ?_ cov⟩
    · simp only [List.foldl_cons, hd, Array.append_assoc]
    · exact all_some_mem (step_records_some step.1 step.2.1) step.2.2
        (step_records step.1 step.2.1 step.2.2 (hsteps step List.mem_cons_self))

run_cmd do
  IO.eprintln "CURRENT_DECL EntryTraffic.translate_delta_covered"
  (← IO.getStderr).flush

/-- The actual translation appends one covered delta to the initial history. -/
theorem translate_delta_covered (initial : Array Event) (info : TranslationStartInfo)
    (walk : List (Nat × Bool × Array Event)) (leaf : Nat × Bool × Array Event)
    (middle : Array Event) (address : AddressDescriptor)
    (traffic : TranslateTrafficFrom (initial.push (.translationStart info)) walk leaf middle) :
    ∃ delta, middle.push (.translationEnd address) = initial ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta := by
  obtain ⟨mid, ⟨hmid, hsteps⟩, leafTraffic, hafter⟩ := traffic
  obtain ⟨d, hd, cov⟩ := fold_delta walk _ hsteps
  have leafCov : ArmCertCTOrdered.OrderedEventV2.Covered leaf.2.2 :=
    all_some_mem (leaf_records_some leaf.1 leaf.2.1) leaf.2.2
      (leaf_records leaf.1 leaf.2.1 leaf.2.2 leafTraffic)
  have startCov : ArmCertCTOrdered.OrderedEventV2.Covered #[Event.translationStart info] := by
    intro e he
    simp only [List.mem_singleton] at he
    subst he; apply record_some_of_traffic; rw [start_record]; rfl
  have endCov : ArmCertCTOrdered.OrderedEventV2.Covered #[Event.translationEnd address] := by
    intro e he
    simp only [List.mem_singleton] at he
    subst he; apply record_some_of_traffic; rw [end_record]; rfl
  refine ⟨#[.translationStart info] ++ d ++ leaf.2.2 ++ #[.translationEnd address], ?_,
    covered_append (covered_append (covered_append startCov cov) leafCov) endCov⟩
  rw [hafter, hmid, hd, Array.push_eq_append_singleton, Array.push_eq_append_singleton]
  simp only [Array.append_assoc]

#print axioms translate_delta_covered
end ArmBridge.CruxGenGuarded.EntryTraffic
