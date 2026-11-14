-- secp CT0: generic composition. Two runs whose every step has a single-run EvShape with the SAME
-- data records and equal PCs are TimingRec-equal (PhasedCT.phased_records over StepEvents.pair); and each step's appended
-- delta is OrderedEventV2.Covered (no unrecorded event) whenever its data records are all `some`.
import SecpCt.Spec
import Bridge.CruxGenGuarded.PhasedCT
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.CruxGenGuarded CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
namespace SecpCt

theorem ct_of_traces (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (n : Nat) (data : Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (e1 e2 : NativeState)
    (h1 : ∀ j, j < n → StepEvents.EvShape spec mapping (data j) (stateAt real e1 j) (stateAt real e1 (j + 1)))
    (h2 : ∀ j, j < n → StepEvents.EvShape spec mapping (data j) (stateAt real e2 j) (stateAt real e2 (j + 1)))
    (pc : ∀ j, j ≤ n → (stateAt real e1 j).regs._PC = (stateAt real e2 j).regs._PC) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record (stateAt real e1 0) (stateAt real e2 0)
      (stateAt real e1 n) (stateAt real e2 n) :=
  PhasedCT.phased_records (stateAt real e1) (stateAt real e2) (fun _ _ _ => True) n trivial (pc 0 (Nat.zero_le _))
    (fun k hk _ => ⟨StepEvents.pair spec mapping (data k) _ _ _ _ (h1 k hk) (h2 k hk) (pc k (Nat.le_of_lt hk))
      (pc (k + 1) hk), trivial⟩)

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

end SecpCt
#print axioms SecpCt.ct_of_traces
#print axioms SecpCt.covered_of_evshape
