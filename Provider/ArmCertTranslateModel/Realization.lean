import ArmCertTranslate.Observation
import ArmCertTranslateModel.DescriptorUpdate
import Pilot.S1HardwareSwap
import Walk.S1LogicalTopology

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Mem := S1ByteMemory.Memory

/-- Exact specialization of the generic encoding to the existing model observer;
    there is no second descriptor decoder. The declared EL20 regime has EE=0. -/
def encoding (pie ha hd : Bool) :
    DescriptorEncoding 8 (BitVec 64) (BitVec 8) (S1DescriptorPIE.View 64) where
  bytes := fun d i => d.extractLsb' (8 * i.val) 8
  view := S1DescriptorPIE.view pie ha hd

theorem encoded_iff (pie ha hd : Bool) (mem : Mem) (slot : Nat) (d : BitVec 64) :
    EncodedAt (encoding pie ha hd) (fun a => mem[a]?) slot d ↔
      S1ByteMemory.DescAt mem slot d := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.isLt

theorem observed_iff (pie ha hd : Bool) (mem : Mem) (slot : Nat)
    (v : S1DescriptorPIE.View 64) :
    Observed (encoding pie ha hd) (fun a => mem[a]?) slot v ↔
      S1MemoryObservation.Observed (S1DescriptorPIE.view pie ha hd) mem slot v := by
  constructor
  · rintro ⟨d, hb, hv⟩
    exact ⟨d, (encoded_iff pie ha hd mem slot d).mp hb, hv⟩
  · rintro ⟨d, hb, hv⟩
    exact ⟨d, (encoded_iff pie ha hd mem slot d).mpr hb, hv⟩

/-- The full aligned-word observer result from the actual model restricts to
    the finite table footprint, without constraining arbitrary program data. -/
theorem equivalent_local (pie ha hd : Bool) (slots : List Nat) (mem mem' : Mem)
    (hal : ∀ slot ∈ slots, slot % 8 = 0)
    (he : S1MemoryObservation.Equivalent (S1DescriptorPIE.view pie ha hd) mem mem') :
    EquivalentOn (encoding pie ha hd) slots (fun a => mem[a]?) (fun a => mem'[a]?) := by
  intro slot hs view
  exact (observed_iff pie ha hd mem slot view).trans
    ((he slot (hal slot hs) view).trans (observed_iff pie ha hd mem' slot view).symm)

/-- Preserve the existing structural logical observation, including every leaf,
    using a physical table-byte frame. No future-walk-success premise occurs. -/
theorem logical_realizes_program_write (observe : S1LogicalReference.Observation)
    (pie ha hd : Bool) (mem mem' : Mem) (f : Footprint) (writes : Nat → Prop)
    (hr : S1LogicalReference.Realizes observe false pie ha hd (fun a => mem[a]?))
    (hc : S1LogicalReference.Covers observe f.byte)
    (hf : WritesOnly writes (fun a => mem[a]?) (fun a => mem'[a]?))
    (hs : Separated f.byte writes) :
    S1LogicalReference.Realizes observe false pie ha hd (fun a => mem'[a]?) := by
  intro logical physical view ho
  obtain ⟨d, hb, hv⟩ := hr logical physical view ho
  refine ⟨d, ?_, hv⟩
  intro i hi
  exact (table_unchanged hf hs _ (hc logical physical view ho i hi)).trans (hb i hi)

/-- Actual source table swap: same exact poststate gives its source equation,
    register frame, local realization, outside-table memory frame and raw AF/
    dirty bit restriction. Ordered events are deliberately still an open API
    obligation; no old read-only trace or full memory equality is asserted. -/
theorem swap_preserves (pie ha hd af dirty : Bool)
    (fault : FaultRecord) (d : BitVec 64) (acc : AccessDescriptor)
    (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (f : Footprint) (observe : Nat → S1DescriptorPIE.View 64 → Prop)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hAlign : addr.paddress.address.toNat % 8 = 0)
    (hDesc : S1ByteMemory.DescAt s.mem addr.paddress.address.toNat d)
    (hAF : af = true → ha = true)
    (hDirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true))
    (hWidth : f.width = 8)
    (hSlot : addr.paddress.address.toNat ∈ f.slots)
    (hSlots : ∀ slot ∈ f.slots, slot % 8 = 0)
    (hCover : Covered observe f.slots)
    (hReal : Realizes (encoding pie ha hd) observe (fun a => s.mem[a]?)) :
    ∃ t : State,
      AArch64_MemSwapTableDesc fault d (S1Descriptor.hardwareUpdate af dirty d)
        0#1 acc addr ti s = .ok (fault, S1Descriptor.hardwareUpdate af dirty d) t ∧
      t.regs = s.regs ∧
      Realizes (encoding pie ha hd) observe (fun a => t.mem[a]?) ∧
      WritesOnly f.byte (fun a => s.mem[a]?) (fun a => t.mem[a]?) ∧
      DescriptorDelta ha hd pie d (S1Descriptor.hardwareUpdate af dirty d) := by
  have hzero : (0#1 : BitVec 1) ≠ 1#1 := by decide
  have hdesc' : S1ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode 0#1 d) := by
    simpa only [S2Endian.encode, hzero, ↓reduceIte] using hDesc
  obtain ⟨t, ht, hregs, hequiv, hframe⟩ :=
    S1HardwareSwap.complete 0#1 pie ha hd af dirty fault d acc addr ti s
      hNoRME hRAM hAlign hdesc' hDirty
  have heq : S1MemoryObservation.Equivalent (S1DescriptorPIE.view pie ha hd) s.mem t.mem := by
    have hobs : S1HardwareSwap.observe 0#1 pie ha hd = S1DescriptorPIE.view pie ha hd := by
      funext raw
      simp only [S1HardwareSwap.observe, S2Endian.encode, hzero, ↓reduceIte]
    rw [hobs] at hequiv
    exact hequiv
  refine ⟨t, ht, hregs, hReal.transport hCover (equivalent_local pie ha hd f.slots s.mem t.mem hSlots heq),
    ?_, hardware_delta ha hd pie af dirty d hAF hDirty⟩
  intro a ha
  apply hframe
  by_cases hlo : a < addr.paddress.address.toNat
  · exact Or.inl hlo
  · right
    have hn : ¬ a < addr.paddress.address.toNat + 8 := by
      intro hi
      apply ha
      exact ⟨addr.paddress.address.toNat, hSlot, by omega, by simpa only [hWidth] using hi⟩
    omega

#print axioms logical_realizes_program_write
#print axioms swap_preserves
end ArmCert.Translate.Model
