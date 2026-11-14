-- Record-level classification of the ACTUAL TranslateAddress event delta by the canonical
-- Isla V2.trafficRec (ArmCertCTNative.UpdateTrafficV2, byte-identical to Isla update-traffic-v1
-- d4ff3c30 / 8a920f2c). Descriptor reads and AF/dirty swaps are TTW traffic at their actual
-- descriptor slot (size 8): ttwRead / ttwRead+ttwWrite; markers are ⟨0, 0, kind⟩. This is the
-- memory-side input to SlotFacts (physical / marker slots) via OrderedEventV2.record.
import ArmCertWalk.NativeTranslateAddressEvents
import ArmCertWalk.TTWAccKind
import ArmCertCTNative.UpdateTrafficV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
open ArmCertCT.Native

theorem descriptor_read_record (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo)
    (ttw : acc.acctype = .AccessType_TTW) :
    V2.trafficRec (descriptorReadEvent acc addr ti) = some ⟨addr.paddress.address.toNat, 8, .ttwRead⟩ := by
  simp [descriptorReadEvent, read_request, ttw_access_kind acc ttw, V2.trafficRec]

theorem swap_read_record (acc : AccessDescriptor) (addr : AddressDescriptor)
    (ttw : acc.acctype = .AccessType_TTW) :
    V2.trafficRec (swapReadEvent acc addr) = some ⟨addr.paddress.address.toNat, 8, .ttwRead⟩ := by
  simp [swapReadEvent, ttw_access_kind acc ttw, V2.trafficRec]

theorem swap_write_record (ee : BitVec 1) (word : BitVec 64) (acc : AccessDescriptor) (addr : AddressDescriptor)
    (ttw : acc.acctype = .AccessType_TTW) :
    V2.trafficRec (swapWriteEvent ee word acc addr) = some ⟨addr.paddress.address.toNat, 8, .ttwWrite⟩ := by
  simp [swapWriteEvent, ttw_access_kind acc ttw, V2.trafficRec]

theorem start_record (info : TranslationStartInfo) :
    V2.trafficRec (.translationStart info) = some ⟨0, 0, .translationStart⟩ := rfl

theorem end_record (address : AddressDescriptor) :
    V2.trafficRec (.translationEnd address) = some ⟨0, 0, .translationEnd⟩ := rfl

/-- Records of one actual walk step at slot `pa`. -/
def stepRecords (pa : Nat) (updated : Bool) : List (Option V2.TrafficRec) :=
  if updated then [some ⟨pa, 8, .ttwRead⟩, some ⟨pa, 8, .ttwRead⟩, some ⟨pa, 8, .ttwWrite⟩]
  else [some ⟨pa, 8, .ttwRead⟩]

/-- Records of the actual leaf swap at slot `pa`. -/
def leafRecords (pa : Nat) (updated : Bool) : List (Option V2.TrafficRec) :=
  if updated then [some ⟨pa, 8, .ttwRead⟩, some ⟨pa, 8, .ttwWrite⟩] else []

theorem step_records (pa : Nat) (updated : Bool) (delta : Array Event)
    (traffic : WalkStepTraffic pa updated delta) :
    delta.toList.map V2.trafficRec = stepRecords pa updated := by
  obtain ⟨readAcc, addr, ti, readTTW, slot, shape⟩ := traffic
  rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, updAcc, ee, word, updTTW, rfl⟩
  · simp [stepRecords, descriptor_read_record _ _ _ readTTW, slot]
  · simp [stepRecords, descriptor_read_record _ _ _ readTTW, swap_read_record _ _ updTTW,
      swap_write_record _ _ _ _ updTTW, slot]

theorem leaf_records (pa : Nat) (updated : Bool) (delta : Array Event)
    (traffic : LeafSwapTraffic pa updated delta) :
    delta.toList.map V2.trafficRec = leafRecords pa updated := by
  rcases traffic with ⟨rfl, rfl⟩ | ⟨rfl, updAcc, slot, ee, word, updTTW, slotPA, rfl⟩
  · simp [leafRecords]
  · simp [leafRecords, swap_read_record _ _ updTTW, swap_write_record _ _ _ _ updTTW, slotPA]

theorem walk_records (before after : Array Event) (steps : List (Nat × Bool × Array Event))
    (traffic : WalkTrafficFrom before steps after) :
    after.toList.map V2.trafficRec =
      before.toList.map V2.trafficRec ++ (steps.map (fun step => stepRecords step.1 step.2.1)).flatten := by
  obtain ⟨events, each⟩ := traffic
  subst events
  induction steps generalizing before with
  | nil => simp
  | cons step rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons]
    rw [ih (before ++ step.2.2) (fun s m => each s (List.mem_cons_of_mem _ m))]
    rw [Array.toList_append, List.map_append, step_records _ _ _ (each step List.mem_cons_self),
      List.append_assoc]

/-- **Actual TranslateAddress traffic records.** The ordered V2 records of the
actual event delta: start marker, per-step TTW records at the actual slots,
leaf swap records, end marker. -/
theorem translate_records (initial : Array Event) (info : TranslationStartInfo)
    (walk : List (Nat × Bool × Array Event)) (leaf : Nat × Bool × Array Event)
    (middle : Array Event) (address : AddressDescriptor)
    (traffic : TranslateTrafficFrom (initial.push (.translationStart info)) walk leaf middle) :
    (middle.push (.translationEnd address)).toList.map V2.trafficRec =
      initial.toList.map V2.trafficRec ++ [some ⟨0, 0, .translationStart⟩] ++
        (walk.map (fun step => stepRecords step.1 step.2.1)).flatten ++
        leafRecords leaf.1 leaf.2.1 ++ [some ⟨0, 0, .translationEnd⟩] := by
  obtain ⟨mid, walkTraffic, leafTraffic, middleEq⟩ := traffic
  subst middleEq
  rw [Array.toList_push, List.map_append, Array.toList_append, List.map_append,
    walk_records _ _ _ walkTraffic, leaf_records _ _ _ leafTraffic, Array.toList_push, List.map_append]
  simp [end_record, start_record]

#print axioms translate_records

/-- v3 ask (c): exact event shape of a TTW descriptor read. -/
theorem descriptor_read_event_ttw (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo)
    (ttw : acc.acctype = .AccessType_TTW) :
    descriptorReadEvent acc addr ti =
      .memRead addr.paddress.address.toNat 8 (some addr.vaddress.toNat) (.AK_ttw ()) false := by
  simp [descriptorReadEvent, read_request, ttw_access_kind acc ttw]

/-- A non-updating actual walk step is exactly one TTW 8-byte read of its slot. -/
theorem walk_step_no_update_shape (pa : Nat) (delta : Array Event) (traffic : WalkStepTraffic pa false delta) :
    ∃ va : Nat, delta = #[.memRead pa 8 (some va) (.AK_ttw ()) false] := by
  obtain ⟨readAcc, addr, ti, readTTW, slot, shape⟩ := traffic
  rcases shape with ⟨_, rfl⟩ | ⟨h, _⟩
  · exact ⟨addr.vaddress.toNat, by rw [descriptor_read_event_ttw _ _ _ readTTW, slot]⟩
  · cases h

#print axioms descriptor_read_event_ttw
#print axioms walk_step_no_update_shape
end ArmCertWalk
