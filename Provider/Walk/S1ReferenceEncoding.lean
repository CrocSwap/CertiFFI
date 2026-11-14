import Walk.S1LogicalTopology
import Walk.S1ResourcePath
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option maxHeartbeats 150000
namespace S1ReferenceEncoding
abbrev Memory := S1ByteMemory.Memory

theorem bytes_iff (ee : BitVec 1) (mem : Memory) (slot : FullAddress) (d : BitVec 64) :
    S1LogicalReference.BytesAt (ee == 1#1) (fun a => mem[a]?) slot d ↔
      S1ByteMemory.DescAt mem slot.address.toNat (S2Endian.encode ee d) := by
  constructor
  · intro h i hi
    by_cases he : ee = 1#1
    · simpa [S1LogicalReference.byte, S2Endian.encode, he, S2Endian.reverse_byte d i hi] using h i hi
    · simpa [S1LogicalReference.byte, S2Endian.encode, he] using h i hi
  · intro h i hi
    by_cases he : ee = 1#1
    · simpa [S1LogicalReference.byte, S2Endian.encode, he, S2Endian.reverse_byte d i hi] using h i hi
    · simpa [S1LogicalReference.byte, S2Endian.encode, he] using h i hi

theorem observed_iff (wp : S1TTWParams) (mem : Memory) (slot : FullAddress)
    (v : S1DescriptorPIE.View 64) :
    S1LogicalReference.PhysicalObserved (wp.ee == 1#1) (wp.pie == 1#1)
      (wp.ha == 1#1) (wp.hd == 1#1) (fun a => mem[a]?) slot v ↔
      S1MemoryObservation.Observed (S1TableUpdate10.observe wp) mem slot.address.toNat v := by
  constructor
  · rintro ⟨d, hb, hv⟩
    refine ⟨S2Endian.encode wp.ee d, (bytes_iff wp.ee mem slot d).mp hb, ?_⟩
    simpa only [S1TableUpdate10.observe, S1HardwareSwap.observe, S2Endian.encode_involutive] using hv
  · rintro ⟨raw, hb, hv⟩
    refine ⟨S2Endian.encode wp.ee raw, ?_, hv⟩
    apply (bytes_iff wp.ee mem slot _).mpr
    simpa only [S2Endian.encode_involutive] using hb

theorem equivalent (wp : S1TTWParams) (before after : Memory)
    (h : S1MemoryObservation.Equivalent (S1TableUpdate10.observe wp) before after) :
    S1LogicalReference.MemoryEquivalent (wp.ee == 1#1) (wp.pie == 1#1)
      (wp.ha == 1#1) (wp.hd == 1#1) (fun a => before[a]?) (fun a => after[a]?) := by
  intro slot aligned v
  rw [observed_iff, observed_iff]
  exact h slot.address.toNat aligned v
#print axioms bytes_iff
#print axioms observed_iff
#print axioms equivalent
end S1ReferenceEncoding
