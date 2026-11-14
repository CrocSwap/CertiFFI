-- Route 7 CT0: every step of a traced run appends a delta whose events all have
-- records (OrderedEventV2.Covered), so TimingRec's record comparison never compares an unrecorded event. The
-- step-level lemma is SecpCt.covered_of_evshape (same proof).
import Route7Trace.Copy
import Route7Trace.Set
import Route7Trace.Move
import HeapV2StepCerts.DataRecs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace Route7Trace
open ArmCertLoop

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

/-- Every step j < N of a traced run from e appends an OrderedEventV2.Covered delta. -/
theorem traced_covered (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (recs : Recs) (pcAt : Nat → BitVec 64) (N : Nat) (e : NativeState)
    (t : Traced real spec mapping recs pcAt N 0 e) (some_ : ∀ k, ∀ r ∈ recs k, r.isSome = true) :
    ∀ j, j < N → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta := by
  intro j hj
  obtain ⟨z, z', r, s, _, ev, -⟩ := t j hj
  rw [CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real j e z r,
    CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (j + 1) e z'
      (Aux.modelRun_append real j 1 e z z' r (run_one real z z' s))]
  exact covered_of_evshape spec mapping _ z z' ev (some_ _)

end Route7Trace

namespace Route7Copy
open ArmCertLoop ArmCertLoop.CopyNative
theorem recs_some (c : Context) : ∀ k, ∀ r ∈ (recsOf c) k, r.isSome = true := by
  intro k r hr
  simp only [recsOf, copyRecs] at hr
  split at hr
  · exact Route7Trace.dataRecs_some _ _ _ _ r hr
  · split at hr
    · exact Route7Trace.dataRecs_some _ _ _ _ r hr
    · simp at hr
end Route7Copy

namespace Route7Set
open ArmCertLoop ArmCertLoop.SetNative
theorem recs_some_s (c : Context) : ∀ k, ∀ r ∈ (recsOfS c) k, r.isSome = true := by
  intro k r hr
  simp only [recsOfS, setRecs] at hr
  split at hr
  · exact Route7Trace.dataRecs_some _ _ _ _ r hr
  · simp at hr
end Route7Set

namespace Route7Move
theorem recs_some_m (c : Context) : ∀ k, ∀ r ∈ (recsOfM c) k, r.isSome = true := by
  intro k r hr
  simp only [recsOfM] at hr
  cases hp : c.path <;> simp only [hp, moveRecs] at hr
  · simp at hr
  · simp at hr
  · split at hr
    · exact Route7Trace.dataRecs_some _ _ _ _ r hr
    · split at hr
      · exact Route7Trace.dataRecs_some _ _ _ _ r hr
      · simp at hr
  · split at hr
    · exact Route7Trace.dataRecs_some _ _ _ _ r hr
    · split at hr
      · exact Route7Trace.dataRecs_some _ _ _ _ r hr
      · simp at hr
end Route7Move
#print axioms Route7Trace.traced_covered
#print axioms Route7Copy.recs_some
#print axioms Route7Set.recs_some_s
#print axioms Route7Move.recs_some_m
