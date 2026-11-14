-- the translation traffic of a no-update access is a
-- DETERMINISTIC record list. Under unique logical keys its V2.trafficRec image is a pure function of
-- (spec, va): translationStart, one 8-byte TTW read per declaredSlots slot, translationEnd. The
-- TranslationStartInfo and the AddressDescriptor never reach the records (constant recs).
import ArmCertWalk.MemPair
import ArmCertWalk.WalkTrafficRecords
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
open ArmCertCT.Native

/-- Deterministic record list of a no-update translation of `va`. -/
def trafficRecsOf {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) :
    List (Option V2.TrafficRec) :=
  some ⟨0, 0, .translationStart⟩ ::
    ((declaredSlots spec.logicalRows spec.layout va).map (fun pa => some ⟨pa, 8, .ttwRead⟩) ++
      [some ⟨0, 0, .translationEnd⟩])

theorem fold_prefix (steps : List (Nat × Bool × Array Event)) (base : Array Event) :
    ∃ d, steps.foldl (fun events step => events ++ step.2.2) base = base ++ d := by
  induction steps generalizing base with
  | nil => exact ⟨#[], by simp⟩
  | cons step rest ih =>
    obtain ⟨d, hd⟩ := ih (base ++ step.2.2)
    exact ⟨step.2.2 ++ d, by simp only [List.foldl_cons, hd, Array.append_assoc]⟩

theorem flatten_noupdate (walk : List (Nat × Bool × Array Event)) (flags : ∀ step ∈ walk, step.2.1 = false) :
    (walk.map (fun step => stepRecords step.1 step.2.1)).flatten =
      (walk.map (·.1)).map (fun pa => some ⟨pa, 8, .ttwRead⟩) := by
  induction walk with
  | nil => rfl
  | cons step rest ih =>
    have f : step.2.1 = false := flags step List.mem_cons_self
    have hs : stepRecords step.1 step.2.1 = [some ⟨step.1, 8, .ttwRead⟩] := by simp [stepRecords, f]
    rw [List.map_cons, List.flatten_cons, hs, ih (fun s mem => flags s (List.mem_cons_of_mem _ mem))]
    rfl

theorem noupdate_traffic_delta {domain : QueryDomain} {spec : TopologyImageSpec domain} {va : BitVec 64}
    {before after : Array Event} {ad : AddressDescriptor}
    (h : NoUpdateTraffic spec va before ad after) (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ T, after = before ++ T ∧ T.toList.map V2.trafficRec = trafficRecsOf spec va := by
  obtain ⟨info, walk, leaf, middle, ⟨m, walkTraffic, leafTraffic, middleEq⟩, flags, leafFlag, slots, afterEq⟩ := h
  have leafEmpty : leaf.2.2 = #[] := by
    rcases leafTraffic with ⟨_, e⟩ | ⟨u, _⟩
    · exact e
    · rw [leafFlag] at u; cases u
  have records := walk_records _ _ walk walkTraffic
  obtain ⟨d, hd⟩ := fold_prefix walk (before.push (.translationStart info))
  have mEq : m = before.push (.translationStart info) ++ d := walkTraffic.1.trans hd
  have dRec : d.toList.map V2.trafficRec =
      (declaredSlots spec.logicalRows spec.layout va).map (fun pa => some ⟨pa, 8, .ttwRead⟩) := by
    rw [mEq, Array.toList_append, List.map_append] at records
    rw [List.append_cancel_left records, flatten_noupdate walk flags, slots nodup]
  refine ⟨#[.translationStart info] ++ d ++ #[.translationEnd ad], ?_, ?_⟩
  · rw [afterEq, middleEq, leafEmpty, mEq]
    simp only [Array.push_eq_append, Array.append_empty, Array.append_assoc]
  · simp only [Array.toList_append, List.map_append, dRec, trafficRecsOf]
    rfl

#print axioms noupdate_traffic_delta
end ArmCertWalk
