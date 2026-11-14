-- secp CT0: generic facts for the per-card CT0 composition: the formal claim premise (SameExceptOperands,
-- S1) and `some`-ness of every data record the shim steps emit.
import SecpCt.Compose
import SecpCt.PairStoreStepE
import SecpCt.DitEpilogueEvents
open ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft ArmBridge.CruxGenGuarded
set_option autoImplicit false
namespace SecpCt

/-- Claim v2 premise: the second entry equals the first in every general-purpose register, except cmul's x1
(the scalar c: data). Memory (operand buffers, output prior contents) and every other register/state component are left
unconstrained: the composition never needs them, so the theorem is stronger than "e2 = e1 except operands". -/
structure SameExceptOperands (cmulX1 : Bool) (e1 e2 : NativeState) : Prop where
  gpr : ∀ i : Fin 31, (cmulX1 = true → i.val ≠ 1) → e1.regs.gpr[i.val] = e2.regs.gpr[i.val]

theorem traffic_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) :
    ∀ r ∈ (ArmCertWalk.trafficRecsOf spec va).map (Option.map ArmCertCTOrdered.OrderedEventV2.Record.traffic),
      r.isSome = true := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  have := StepEvents.trafficRecsOf_some spec va v hv
  cases v with
  | none => simp at this
  | some _ => rfl

theorem vaRecs_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (w : Bool) (vs : List (BitVec 64 × Nat)) :
    ∀ r ∈ PairRecs.vaRecs spec w vs, r.isSome = true := by
  intro r hr
  simp only [PairRecs.vaRecs, List.mem_flatMap, List.mem_append, List.mem_singleton] at hr
  obtain ⟨p, _, h | h⟩ := hr
  · exact traffic_some spec p.1 r h
  · subst h; rfl

theorem dataRecs_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) (w : Bool) (n : Nat) :
    ∀ r ∈ HeapV2StepCerts.DataRecs.dataRecs spec va w n, r.isSome = true := by
  intro r hr
  simp only [HeapV2StepCerts.DataRecs.dataRecs, List.mem_append, List.mem_singleton] at hr
  rcases hr with h | h
  · exact traffic_some spec va r h
  · subst h; rfl

theorem shimData_some {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins) (j : Nat) :
    ∀ r ∈ Release.shimData spec pins j, r.isSome = true := by
  intro r hr
  unfold Release.shimData at hr
  split at hr
  · exact dataRecs_some spec _ _ _ r hr
  · split at hr
    · simp only [List.mem_singleton] at hr; subst hr; rfl
    · split at hr
      · exact dataRecs_some spec _ _ _ r hr
      · simp at hr

/-! Spec transport for data records, proved once over abstract address lists (so per-card proofs never make the kernel
compare two concrete checked specs, whose address lists grow with the body length). -/
theorem vaRecs_spec (raw : TranslateSpan.CheckedTopology.Raw) (A B : List (BitVec 64))
    (hA : TranslateSpan.CheckedTopology.check raw A 4 = true) (hB : TranslateSpan.CheckedTopology.check raw B 4 = true)
    (w : Bool) (vs : List (BitVec 64 × Nat)) :
    PairRecs.vaRecs (TranslateSpan.CheckedTopology.spec raw A 4 hA) w vs = PairRecs.vaRecs (TranslateSpan.CheckedTopology.spec raw B 4 hB) w vs :=
  rfl

theorem shimData_spec (raw : TranslateSpan.CheckedTopology.Raw) (A B : List (BitVec 64))
    (hA : TranslateSpan.CheckedTopology.check raw A 4 = true) (hB : TranslateSpan.CheckedTopology.check raw B 4 = true)
    (pins : HeapV2E17.Pins) (j : Nat) :
    Release.shimData (TranslateSpan.CheckedTopology.spec raw A 4 hA) pins j = Release.shimData (TranslateSpan.CheckedTopology.spec raw B 4 hB) pins j :=
  rfl

theorem evshape_vaRecs (raw : TranslateSpan.CheckedTopology.Raw) (A B : List (BitVec 64))
    (hA : TranslateSpan.CheckedTopology.check raw A 4 = true) (hB : TranslateSpan.CheckedTopology.check raw B 4 = true)
    (mapping : BitVec 64 → Option Nat) (w : Bool) (vs : List (BitVec 64 × Nat)) (x fin : NativeState)
    (e : StepEvents.EvShape (TranslateSpan.CheckedTopology.spec raw A 4 hA) mapping (PairRecs.vaRecs (TranslateSpan.CheckedTopology.spec raw A 4 hA) w vs) x fin) :
    StepEvents.EvShape (TranslateSpan.CheckedTopology.spec raw B 4 hB) mapping (PairRecs.vaRecs (TranslateSpan.CheckedTopology.spec raw B 4 hB) w vs) x fin := by
  rw [← vaRecs_spec raw A B hA hB w vs]
  exact evshape_spec raw A B hA hB mapping _ x fin e

/-! Two runs from two callers of one source completion check different raws (params / controls / physical config depend
on the caller and its data part), but the traffic records read a raw only through `logicalRows` and `layout`
(the shared tables). Transport across raws with equal rows and layout. -/
theorem traffic_raw (raw1 raw2 : TranslateSpan.CheckedTopology.Raw) (A B : List (BitVec 64))
    (h1 : TranslateSpan.CheckedTopology.check raw1 A 4 = true) (h2 : TranslateSpan.CheckedTopology.check raw2 B 4 = true)
    (hl : raw1.logicalRows = raw2.logicalRows) (hy : raw1.layout = raw2.layout) :
    ArmCertWalk.trafficRecsOf (TranslateSpan.CheckedTopology.spec raw1 A 4 h1) =
      ArmCertWalk.trafficRecsOf (TranslateSpan.CheckedTopology.spec raw2 B 4 h2) := by
  funext va
  unfold ArmCertWalk.trafficRecsOf
  simp only [TranslateSpan.CheckedTopology.spec, hl, hy]

theorem evshape_raw (raw1 raw2 : TranslateSpan.CheckedTopology.Raw) (A B : List (BitVec 64))
    (h1 : TranslateSpan.CheckedTopology.check raw1 A 4 = true) (h2 : TranslateSpan.CheckedTopology.check raw2 B 4 = true)
    (hl : raw1.logicalRows = raw2.logicalRows) (hy : raw1.layout = raw2.layout)
    (mapping : BitVec 64 → Option Nat) (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (x fin : NativeState)
    (e : StepEvents.EvShape (TranslateSpan.CheckedTopology.spec raw1 A 4 h1) mapping data x fin) :
    StepEvents.EvShape (TranslateSpan.CheckedTopology.spec raw2 B 4 h2) mapping data x fin := by
  obtain ⟨n, T, D, ev, tr, mp, dr⟩ := e
  exact ⟨n, T, D, ev, by rw [← traffic_raw raw1 raw2 A B h1 h2 hl hy]; exact tr, mp, dr⟩

theorem vaRecs_raw (raw1 raw2 : TranslateSpan.CheckedTopology.Raw) (A B : List (BitVec 64))
    (h1 : TranslateSpan.CheckedTopology.check raw1 A 4 = true) (h2 : TranslateSpan.CheckedTopology.check raw2 B 4 = true)
    (hl : raw1.logicalRows = raw2.logicalRows) (hy : raw1.layout = raw2.layout) (w : Bool) (vs : List (BitVec 64 × Nat)) :
    PairRecs.vaRecs (TranslateSpan.CheckedTopology.spec raw1 A 4 h1) w vs = PairRecs.vaRecs (TranslateSpan.CheckedTopology.spec raw2 B 4 h2) w vs := by
  unfold PairRecs.vaRecs
  rw [traffic_raw raw1 raw2 A B h1 h2 hl hy]

theorem shimData_raw (raw1 raw2 : TranslateSpan.CheckedTopology.Raw) (A B : List (BitVec 64))
    (h1 : TranslateSpan.CheckedTopology.check raw1 A 4 = true) (h2 : TranslateSpan.CheckedTopology.check raw2 B 4 = true)
    (hl : raw1.logicalRows = raw2.logicalRows) (hy : raw1.layout = raw2.layout) (pins : HeapV2E17.Pins) (j : Nat) :
    Release.shimData (TranslateSpan.CheckedTopology.spec raw1 A 4 h1) pins j = Release.shimData (TranslateSpan.CheckedTopology.spec raw2 B 4 h2) pins j := by
  unfold Release.shimData HeapV2StepCerts.DataRecs.dataRecs
  rw [traffic_raw raw1 raw2 A B h1 h2 hl hy]

end SecpCt
#print axioms SecpCt.vaRecs_some
#print axioms SecpCt.shimData_some
#print axioms SecpCt.evshape_raw
#print axioms SecpCt.vaRecs_raw
#print axioms SecpCt.shimData_raw
