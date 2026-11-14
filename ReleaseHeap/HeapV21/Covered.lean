/-
Heap v1.2 → v2.1: every step of each Heap run appends an OrderedEventV2.Covered delta.

The step lemma `covered_of_evshape` is the same proof as SecpCt.covered_of_evshape / loops'
Route7Trace.covered_of_evshape, over the heap-side StepEvents (base-v3 renamed sources). `covered_run` lifts it to a
run from the per-step EvShape facts that heap traces already expose (DefaultHeapTrap.initial_k,
DefaultHeapShimFactory.trace). The `*_some` lemmas discharge "every data record is present" for the heap record tables.
-/
import Bridge.CruxGenGuarded.StepEvents
import HeapV2StepCerts.DataRecs
import DefaultHeapRunRecords
import DefaultHeapTrapInitial
import DefaultHeapShimTrace
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmBridge.Draft ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace CertiFFI.HeapV21

theorem dataRecs_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) (w : Bool) (size : Nat) :
    ∀ r ∈ HeapV2StepCerts.DataRecs.dataRecs spec va w size, r.isSome = true := by
  intro r hr
  simp only [HeapV2StepCerts.DataRecs.dataRecs, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨v, hv, rfl⟩ | rfl
  · have := StepEvents.trafficRecsOf_some spec va v hv
    cases v with
    | none => simp at this
    | some _ => rfl
  · rfl

theorem covered_of_evshape {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (x fin : NativeState)
    (e : StepEvents.EvShape spec mapping data x fin) (some_ : ∀ r ∈ data, r.isSome = true) :
    ∃ delta : Array Event, fin.events = x.events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta := by
  obtain ⟨n, T, D, ev, tr, _, dr⟩ := e
  refine ⟨T ++ #[StepEvents.ifetchEv n x.regs._PC] ++ D, by rw [ev]; simp only [Array.append_assoc], ?_⟩
  intro event mem
  simp only [Array.toList_append, List.mem_append] at mem
  rcases mem with (inT | inF) | inD
  · have h := StepEvents.records_of_traffic T.toList _ tr (StepEvents.trafficRecsOf_some spec _)
    have hm := List.mem_map_of_mem (f := ArmCertCTOrdered.OrderedEventV2.record) inT
    rw [h] at hm
    obtain ⟨v, hv, eq⟩ := List.mem_map.1 hm
    rw [← eq]
    have := StepEvents.trafficRecsOf_some spec x.regs._PC v hv
    cases v with
    | none => simp at this
    | some _ => rfl
  · simp only [List.mem_singleton] at inF; subst inF; rfl
  · have hm := List.mem_map_of_mem (f := ArmCertCTOrdered.OrderedEventV2.record) inD
    rw [dr] at hm
    exact some_ _ hm

/-- Every step j < N of a run whose steps have EvShape over present records appends a Covered delta. -/
theorem covered_run (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (recs : Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (N : Nat) (e : NativeState)
    (ev : ∀ j, j < N → StepEvents.EvShape spec mapping (recs j)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e j) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (j + 1)))
    (some_ : ∀ j, ∀ r ∈ recs j, r.isSome = true) :
    ∀ j, j < N → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta :=
  fun j hj => covered_of_evshape spec mapping (recs j) _ _ (ev j hj) (some_ j)

theorem shimData_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins) :
    ∀ j, ∀ r ∈ Release.shimData spec pins j, r.isSome = true := by
  intro j r hr
  unfold Release.shimData at hr
  split at hr
  · exact dataRecs_some _ _ _ _ _ hr
  split at hr
  · simp only [List.mem_singleton] at hr; subst hr; rfl
  split at hr
  · exact dataRecs_some _ _ _ _ _ hr
  · simp at hr

theorem trapRecords_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins) :
    ∀ j, ∀ r ∈ ReleaseProfile.DefaultHeapTrap.records spec pins j, r.isSome = true := by
  intro j r hr
  unfold ReleaseProfile.DefaultHeapTrap.records at hr
  split at hr
  · exact shimData_some spec pins j r hr
  · simp at hr

theorem runRecords_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins) :
    ∀ j, ∀ r ∈ ReleaseProfile.DefaultHeapRun.records spec pins j, r.isSome = true := by
  intro j r hr
  unfold ReleaseProfile.DefaultHeapRun.records at hr
  split at hr <;> first | exact dataRecs_some _ _ _ _ _ hr | simp at hr

theorem factoryRecords_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins) :
    ∀ j, ∀ r ∈ ReleaseProfile.DefaultHeapShimFactory.records spec pins j, r.isSome = true := by
  intro j r hr
  unfold ReleaseProfile.DefaultHeapShimFactory.records at hr
  split at hr
  · exact shimData_some spec pins j r hr
  split at hr
  · exact runRecords_some spec pins _ r hr
  split at hr
  · simp at hr
  · exact shimData_some spec pins _ r hr

#print axioms covered_run
#print axioms trapRecords_some
#print axioms factoryRecords_some
end CertiFFI.HeapV21
