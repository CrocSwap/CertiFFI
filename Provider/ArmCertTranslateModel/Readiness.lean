import ArmCertTranslateModel.Realization

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Keep AF readiness alongside the source's permission-sensitive stable view.
    HA=0 therefore cannot hide the difference between AF=0 and AF=1. -/
def readyView (pie ha hd : Bool) (d : BitVec 64) : S1DescriptorPIE.View 64 × Bool :=
  (S1DescriptorPIE.view pie ha hd d, d.getLsbD 10 || ha)

def readyEncoding (pie ha hd : Bool) :
    DescriptorEncoding 8 (BitVec 64) (BitVec 8) (S1DescriptorPIE.View 64 × Bool) where
  bytes := (encoding pie ha hd).bytes
  view := readyView pie ha hd

theorem ready_determined (pie ha hd : Bool) : ViewDetermined (readyEncoding pie ha hd) := by
  intro raw raw' hb
  have heq : raw = raw' := S2Endian.ext_bytes raw raw' (fun i hi => congrFun hb ⟨i, hi⟩)
  rw [heq]

theorem ready_hardware_view (pie ha hd af dirty : Bool) (d : BitVec 64)
    (hAF : af = true → ha = true)
    (hDirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true)) :
    readyView pie ha hd (S1Descriptor.hardwareUpdate af dirty d) = readyView pie ha hd d := by
  apply Prod.ext
  · exact S1DescriptorPIE.hardware_view pie ha hd af dirty d hDirty
  · have hdlt := hardware_delta ha hd pie af dirty d hAF hDirty
    change ((S1Descriptor.hardwareUpdate af dirty d).getLsbD 10 || ha) = (d.getLsbD 10 || ha)
    cases hh : ha
    · rw [← hdlt.af_eq_of_disabled hh]
    · simp

/-- An actual source-compatible byte store preserves the enriched observer at
    every covered aligned slot, including slots shared by many virtual paths. -/
theorem store_ready_equivalent (pie ha hd af dirty : Bool) (d : BitVec 64)
    (mem : Mem) (slot : Nat) (slots : List Nat)
    (hAlign : slot % 8 = 0) (hSlots : ∀ b ∈ slots, b % 8 = 0)
    (hDesc : S1ByteMemory.DescAt mem slot d)
    (hAF : af = true → ha = true)
    (hDirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true)) :
    EquivalentOn (readyEncoding pie ha hd) slots (fun a => mem[a]?)
      (fun a => (S1ByteMemory.store mem slot (S1Descriptor.hardwareUpdate af dirty d))[a]?) := by
  apply EquivalentOn.of_changes (ready_determined pie ha hd)
  intro b hb
  by_cases heq : slot = b
  · subst b
    right
    refine ⟨d, S1Descriptor.hardwareUpdate af dirty d, ?_, ?_, ?_⟩
    · funext i
      exact hDesc i.val i.isLt
    · funext i
      exact S1ByteMemory.stored_descriptor mem slot _ i.val i.isLt
    · exact (ready_hardware_view pie ha hd af dirty d hAF hDirty).symm
  · left
    funext i
    exact S1ByteMemory.lookup_outside mem slot _ (b + i.val) (by have := hSlots b hb; have := i.isLt; omega)

/-- Derive readiness preservation for the SAME actual poststate returned by the
    source swap. This lemma consumes its exact equation, which the caller
    obtains from S1HardwareSwap.complete; it is not a new environment premise. -/
theorem swap_ready_equivalent (pie ha hd af dirty : Bool)
    (fault : FaultRecord) (d : BitVec 64) (acc : AccessDescriptor)
    (addr : AddressDescriptor) (ti : TranslationInfo) (s t : State)
    (slots : List Nat)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hAlign : addr.paddress.address.toNat % 8 = 0)
    (hSlots : ∀ slot ∈ slots, slot % 8 = 0)
    (hDesc : S1ByteMemory.DescAt s.mem addr.paddress.address.toNat d)
    (hAF : af = true → ha = true)
    (hDirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true))
    (ht : AArch64_MemSwapTableDesc fault d (S1Descriptor.hardwareUpdate af dirty d)
      0#1 acc addr ti s = .ok (fault, S1Descriptor.hardwareUpdate af dirty d) t) :
    EquivalentOn (readyEncoding pie ha hd) slots (fun a => s.mem[a]?) (fun a => t.mem[a]?) := by
  have hzero : (0#1 : BitVec 1) ≠ 1#1 := by decide
  have hdesc' : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode 0#1 d) := by
    intro i hi
    simpa only [S2Endian.encode, hzero, ↓reduceIte] using hDesc i hi
  have he := S2SwapAnyFrame.effect 0#1 fault d (S1Descriptor.hardwareUpdate af dirty d)
    acc addr ti s hNoRME hRAM hdesc'
  rw [ht] at he
  have hm := he.2.2.2
  simp only [S2Endian.encode, hzero, ↓reduceIte] at hm
  change t.mem = S1ByteMemory.store s.mem addr.paddress.address.toNat (S1Descriptor.hardwareUpdate af dirty d) at hm
  rw [hm]
  exact store_ready_equivalent pie ha hd af dirty d s.mem addr.paddress.address.toNat slots
    hAlign hSlots hDesc hAF hDirty

#print axioms ready_hardware_view
#print axioms store_ready_equivalent
#print axioms swap_ready_equivalent
end ArmCert.Translate.Model
