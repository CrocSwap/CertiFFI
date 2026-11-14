import GetEntry.RangeGeometry
import GetEntry.ReferenceMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace S1EntryPathSlots
open S1LogicalReference
abbrev State := S1OuterSetup.State

/- VM0 uses an independent logical observation with physical identity.
   This predicate is a byte-memory encoding fact, not source execution success. -/
def Identity (observe : Observation) : Prop :=
  ∀ logical physical view, observe logical physical view → physical.address.toNat = logical

theorem observation (wp : S1TTWParams) (mem : S1ByteMemory.Memory)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe (wp.ee == 1#1) (wp.pie == 1#1)
      (wp.ha == 1#1) (wp.hd == 1#1) (fun a => mem[a]?))
    (identity : Identity observe) (logical : Nat) (physical slot : FullAddress)
    (v : S1DescriptorPIE.View 64) (present : observe logical physical v)
    (hslot : slot.address.toNat = logical) :
    ∃ d, S1ResourcePath.view wp d = v ∧ S2TableRAM.OrdinaryRAM slot.address ∧
      slot.address.toNat % 8 = 0 ∧
      S1MemoryObservation.Observed (S1TableUpdate10.observe wp) mem slot.address.toNat
        (S1ResourcePath.view wp d) := by
  rcases realizes logical physical v present with ⟨d, hb, hv⟩
  have ha := available logical physical v present
  have he : slot.address = physical.address :=
    BitVec.eq_of_toNat_eq (hslot.trans (identity logical physical v present).symm)
  have ho := (S1ReferenceEncoding.observed_iff wp mem physical v).mp ⟨d, hb, hv⟩
  refine ⟨d, hv, ?_, ?_, ?_⟩
  · rw [he]; exact ha.2.2
  · rw [hslot]; exact ha.1
  · rw [he, show S1ResourcePath.view wp d = v from hv]
    exact ho

theorem stop (wp : S1TTWParams) (d : BitVec 64) (v : S1DescriptorPIE.View 64)
    (hv : S1ResourcePath.view wp d = v) (level : Nat) (hl : level ≤ 3)
    (hk : descriptorKind level v.stable = .ok .invalid ∨
      descriptorKind level v.stable = .ok .leaf) :
    S1DecodeFacts.classify d (level : Int) ≠ .DescriptorType_Table := by
  have hc := S1ReferenceKind.view_kind _ _ _ d v hv level hl
  cases h : S1DecodeFacts.classify d (level : Int) <;> simp_all

theorem table (wp : S1TTWParams) (d : BitVec 64) (v : S1DescriptorPIE.View 64)
    (hv : S1ResourcePath.view wp d = v) (level : Nat) (hl : level ≤ 3)
    (hk : descriptorKind level v.stable = .ok .table) :
    S1DecodeFacts.classify d (level : Int) = .DescriptorType_Table := by
  have hc := S1ReferenceKind.view_kind _ _ _ d v hv level hl
  cases h : S1DecodeFacts.classify d (level : Int) <;> simp_all

theorem range_true (wp : S1TTWParams) (slot : FullAddress)
    (h : 2^(S2PhysicalSizeFrame.value wp.ps).toNat ≤ slot.address.toNat) :
    S1TablePrefix10.outOfRange wp slot = true := by
  have hf := S1EntryRangeGeometry.in_range wp slot
  cases hb : S1TablePrefix10.outOfRange wp slot with
  | false => have hh := hf.mp hb; omega
  | true => rfl

theorem of_path (wp : S1TTWParams) (va : BitVec 64) (mem : S1ByteMemory.Memory)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe (wp.ee == 1#1) (wp.pie == 1#1)
      (wp.ha == 1#1) (wp.hd == 1#1) (fun a => mem[a]?))
    (identity : Identity observe)
    {level bits : Nat} {base : BitVec 48} {result : PathEnd}
    (path : Path observe (S2PhysicalSizeFrame.value wp.ps).toNat va level bits base result) :
    bits = 9 → ∀ slot : FullAddress, slot.address.toNat = entryAddress base va level bits →
      ∃ n, S1ResourcePath.Slots wp va mem n (level : Int) slot := by
  induction path with
  | invalid level bits base physical v hl aligned present kind =>
    intro hbits slot hslot
    rcases observation wp mem observe available realizes identity _ physical slot v present hslot with
      ⟨d, hv, hram, halign, hobs⟩
    exact ⟨1, .terminal ⟨by omega, by omega⟩ hram halign hobs
      (stop wp d v hv level hl (Or.inl kind))⟩
  | leaf level bits base physical v hl aligned present kind =>
    intro hbits slot hslot
    rcases observation wp mem observe available realizes identity _ physical slot v present hslot with
      ⟨d, hv, hram, halign, hobs⟩
    exact ⟨1, .terminal ⟨by omega, by omega⟩ hram halign hobs
      (stop wp d v hv level hl (Or.inr kind))⟩
  | range level bits base physical v hl aligned present kind outOfRange =>
    intro hbits slot hslot
    rcases observation wp mem observe available realizes identity _ physical slot v present hslot with
      ⟨d, hv, hram, halign, hobs⟩
    have hn := S1EntryNextGeometry.next_slot wp d va level hl
    rw [hv] at hn
    refine ⟨1, .tableFault ⟨by omega, by omega⟩ hram halign hobs
      (table wp d v hv level (by omega) kind) ?_⟩
    apply range_true
    rw [hn]
    exact outOfRange
  | table level bits base physical v result hl aligned present kind inRange next ih =>
    intro hbits slot hslot
    rcases observation wp mem observe available realizes identity _ physical slot v present hslot with
      ⟨d, hv, hram, halign, hobs⟩
    have hn := S1EntryNextGeometry.next_slot wp d va level hl
    rw [hv] at hn
    rcases ih rfl (S1ResourcePath.nextSlot va (level : Int) d) hn with ⟨n, hrest⟩
    refine ⟨n + 1, .table ⟨by omega, by omega⟩ hram halign hobs
      (table wp d v hv level (by omega) kind) ?_ ?_⟩
    · apply (S1EntryRangeGeometry.in_range wp _).mpr
      rw [hn]
      exact inRange
    · simpa only [Int.natCast_add, Int.natCast_one] using hrest

#print axioms observation
#print axioms of_path
end S1EntryPathSlots
