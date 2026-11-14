-- Memory (/, H-P3): records of a memory step's data events. A no-update data access
-- appends its translation traffic (records = trafficRecsOf spec va) then one access event whose record keeps only
-- (kind, VA, size): public data. dataRecs is that list; the mem tails export delta's records = dataRecs.
import HeapV2StepCerts.FetchTiming
import Bridge.CruxGenGuarded.StepEvents
import ArmCertWalk.MemClassLdrb
import ArmCertWalk.MemClassStrb
import ArmCertWalk.MemPair
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.DataRecs
open ArmCertWalk ArmCertCT.Native

/-- The records of one data access at `va` (translation traffic, then the access). -/
def dataRecs {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) (write : Bool) (size : Nat) :
    List (Option ArmCertCTOrdered.OrderedEventV2.Record) :=
  (trafficRecsOf spec va).map (Option.map .traffic) ++
    [some (.access ⟨if write then .write else .read, BitVec.ofNat 64 va.toNat, size⟩)]

theorem single_records {domain : QueryDomain} {spec : TopologyImageSpec domain} {va : BitVec 64}
    {before after delta : Array Event} {e : Event}
    (h : ∃ ad mid, NoUpdateTraffic spec va before ad mid ∧ after = mid.push e) (hd : after = before ++ delta)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    delta.toList.map ArmCertCTOrdered.OrderedEventV2.record =
      (trafficRecsOf spec va).map (Option.map .traffic) ++ [ArmCertCTOrdered.OrderedEventV2.record e] := by
  obtain ⟨ad, mid, traffic, ha⟩ := h
  obtain ⟨T, hT, rT⟩ := noupdate_traffic_delta traffic nodup
  have e1 : before ++ delta = before ++ (T ++ #[e]) := by
    rw [← hd, ha, hT, Array.push_eq_append, Array.append_assoc]
  have hdT : delta = T ++ #[e] := by
    have := congrArg Array.toList e1
    simp only [Array.toList_append] at this
    exact Array.ext' (List.append_cancel_left this |>.trans (by simp))
  rw [hdT, Array.toList_append, List.map_append,
    ArmBridge.CruxGenGuarded.StepEvents.records_of_traffic T.toList _ rT
      (ArmBridge.CruxGenGuarded.StepEvents.trafficRecsOf_some spec va)]
  rfl

theorem load_single {domain : QueryDomain} {spec : TopologyImageSpec domain} {va : BitVec 64} {pa : BitVec 56}
    {before after : Array Event} {kind : Access_kind arm_acc_type} (h : MemClass.Ldrb.LoadEvents spec va pa before kind after) :
    ∃ ad mid, NoUpdateTraffic spec va before ad mid ∧ after = mid.push (.memRead pa.toNat 1 (some va.toNat) kind false) := by
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, afterEq⟩ := h
  exact ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, afterEq⟩

theorem store_single {domain : QueryDomain} {spec : TopologyImageSpec domain} {va : BitVec 64} {pa : BitVec 56}
    {before after : Array Event} {kind : Access_kind arm_acc_type} {value : BitVec (8 * 1)}
    (h : MemClass.Strb.StoreEvents spec va pa before kind value after) :
    ∃ ad mid, NoUpdateTraffic spec va before ad mid ∧
      after = mid.push (.memWrite pa.toNat 1 (some va.toNat) kind (some value) none) := by
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, afterEq⟩ := h
  exact ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, afterEq⟩

theorem pair_single {domain : QueryDomain} {spec : TopologyImageSpec domain} {A : BitVec 64} {pa1 pa2 : BitVec 56}
    {one half1 half2 : Event} {before after : Array Event} (h : PairEvents spec A pa1 pa2 one half1 half2 before after)
    (al : A.toNat % 16 = 0) : ∃ ad mid, NoUpdateTraffic spec A before ad mid ∧ after = mid.push one := by
  rcases h with ⟨_, single⟩ | ⟨n16, _⟩
  · exact single
  · exact absurd al n16

#print axioms single_records
end HeapV2StepCerts.DataRecs
