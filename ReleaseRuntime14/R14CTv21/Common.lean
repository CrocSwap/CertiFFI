-- Runtime14 CT0 → grades v2.1: step-level Covered from a EvShape (same proof as
-- SecpCt.covered_of_evshape / loops Route7Trace.dataRecs_some), stated over StepEvents only.
import Bridge.CruxGenGuarded.PhasedCT
import HeapV2StepCerts.DataRecs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
open ArmCert.Translate.Model ArmBridge.Draft ArmBridge.CruxGenGuarded
set_option autoImplicit false
namespace R14CTv21

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

end R14CTv21
#print axioms R14CTv21.covered_of_evshape
