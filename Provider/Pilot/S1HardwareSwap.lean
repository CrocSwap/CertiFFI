import Pilot.S2SwapAnyFrame
import Pilot.S1MemoryObservation
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1HardwareSwap
abbrev State := SequentialState Regs oracleChoiceSource

def observe (ee : BitVec 1) (pie ha hd : Bool) (raw : BitVec 64) :=
  S1DescriptorPIE.view pie ha hd (S2Endian.encode ee raw)

/- Exact shared model swap, with the stage-1 dirty direction and observer.
   Covers both byte orders and retains the actual post-read/write state. -/
theorem complete (ee : BitVec 1) (pie ha hd af dirty : Bool)
    (fault : FaultRecord) (d : BitVec 64) (acc : AccessDescriptor)
    (addr : AddressDescriptor) (ti : TranslationInfo) (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hAlign : addr.paddress.address.toNat % 8 = 0)
    (hDesc : S1ByteMemory.DescAt s.mem addr.paddress.address.toNat (S2Endian.encode ee d))
    (hDirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true)) :
    ∃ t : State,
      AArch64_MemSwapTableDesc fault d (S1Descriptor.hardwareUpdate af dirty d)
        ee acc addr ti s = .ok (fault, S1Descriptor.hardwareUpdate af dirty d) t ∧
      t.regs = s.regs ∧
      S1MemoryObservation.Equivalent (observe ee pie ha hd) s.mem t.mem ∧
      (∀ x, x < addr.paddress.address.toNat ∨ addr.paddress.address.toNat + 8 ≤ x →
        t.mem[x]? = s.mem[x]?) := by
  obtain ⟨t, heq, hregs, hmem⟩ := S2SwapAnyFrame.total ee fault d
    (S1Descriptor.hardwareUpdate af dirty d) acc addr ti s hNoRME hRAM hDesc
  refine ⟨t, heq, hregs, ?_, ?_⟩
  · rw [hmem]
    apply S1MemoryObservation.store_equivalent _ _ _ _ _ hAlign hDesc
    simp only [observe, S2Endian.encode_involutive]
    exact (S1DescriptorPIE.hardware_view pie ha hd af dirty d hDirty).symm
  · intro x hx
    rw [hmem]
    exact S1ByteMemory.lookup_outside _ _ _ x hx

#print axioms complete
end S1HardwareSwap
