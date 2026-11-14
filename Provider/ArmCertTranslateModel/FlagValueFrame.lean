import ArmCertTranslateModel.StructuralBridge

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Potentially CHANGED value bytes, not the traffic footprint: the actual
    source still emits an eight-byte TTW write. AF10 and dirty7 are in bytes1/0. -/
def FlagValueByte (slot address : Nat) : Prop := address = slot ∨ address = slot + 1

theorem allowed_store_value_frame (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (allowed : AllowedUpdate params role before after)
    (mem : Mem) (slot : Nat) (present : S1ByteMemory.DescAt mem slot before) :
    WritesOnly (FlagValueByte slot) (fun a => mem[a]?) (fun a => (S1ByteMemory.store mem slot after)[a]?) := by
  intro a ha
  by_cases hlo : a < slot
  · exact S1ByteMemory.lookup_outside mem slot after a (Or.inl hlo)
  by_cases hhi : slot + 8 ≤ a
  · exact S1ByteMemory.lookup_outside mem slot after a (Or.inr hhi)
  have lower : slot ≤ a := by omega
  have upper : a < slot + 8 := by omega
  obtain ⟨i, hai⟩ := Nat.exists_eq_add_of_le lower
  have hi : i < 8 := by omega
  have himin : 2 ≤ i := by
    have h0 : a ≠ slot := fun h => ha (Or.inl h)
    have h1 : a ≠ slot + 1 := fun h => ha (Or.inr h)
    omega
  have bytes := (allowed_delta params role before after allowed).slice_eq (8 * i) 8
    (by omega) (by intro j hj; omega) (by intro j hj; omega)
  rw [hai]
  change (S1ByteMemory.store mem slot after)[slot + i]? = mem[slot + i]?
  rw [S1ByteMemory.lookup_inside mem slot after i hi, bytes]
  exact (present i hi).symm

/-- A code/data byte projection disjoint only from the potentially changed
    flag bytes keeps its current values. This is narrower than excluding every
    program read from all table bytes; traffic is still the actual eight bytes. -/
theorem flag_values_unchanged_on (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (allowed : AllowedUpdate params role before after)
    (mem : Mem) (slot : Nat) (present : S1ByteMemory.DescAt mem slot before)
    (readBytes : Nat → Prop) (separated : Separated readBytes (FlagValueByte slot)) :
    AgreeOn readBytes (fun a => mem[a]?) (fun a => (S1ByteMemory.store mem slot after)[a]?) :=
  table_unchanged (allowed_store_value_frame params role before after allowed mem slot present) separated

/-- The SAME actual source successor has the narrower memory-value frame.
    No event-size, event-count or ordering simplification is made. -/
theorem swap_flag_value_frame (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (allowed : AllowedUpdate params role before after)
    (fault : FaultRecord) (acc : AccessDescriptor) (addr : AddressDescriptor)
    (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (present : S1ByteMemory.DescAt s.mem addr.paddress.address.toNat before) :
    ∃ t : State,
      AArch64_MemSwapTableDesc fault before after 0#1 acc addr ti s = .ok (fault, after) t ∧
      t.regs = s.regs ∧ WritesOnly (FlagValueByte addr.paddress.address.toNat)
        (fun a => s.mem[a]?) (fun a => t.mem[a]?) := by
  have hzero : (0#1 : BitVec 1) ≠ 1#1 := by decide
  have hold : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode 0#1 before) := by
    intro i hi
    simpa only [S2Endian.encode, hzero, ↓reduceIte] using present i hi
  obtain ⟨t, ht, hr, hm⟩ := S2SwapAnyFrame.total 0#1 fault before after acc addr ti s hNoRME hRAM hold
  simp only [S2Endian.encode, hzero, ↓reduceIte] at hm
  change t.mem = S1ByteMemory.store s.mem addr.paddress.address.toNat after at hm
  refine ⟨t, ht, hr, ?_⟩
  rw [hm]
  exact allowed_store_value_frame params role before after allowed s.mem addr.paddress.address.toNat present

#print axioms allowed_store_value_frame
#print axioms swap_flag_value_frame
end ArmCert.Translate.Model
