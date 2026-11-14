import Pilot.S2PhysWrite
import Pilot.S2ByteMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2PhysFrame
abbrev State := SequentialState Regs oracleChoiceSource
def memResult {α : Type} : EStateM.Result (Sail.Error exception) State α → Option S2ByteMemory.Memory
  | .ok _ s => some s.mem
  | .error _ _ => none

theorem mem_eq (desc : AddressDescriptor) (acc : AccessDescriptor) (ti : Option TranslationInfo)
    (data : BitVec 64) (s : State) (hTableRAM : S2TableRAM.OrdinaryRAM desc.paddress.address) :
    memResult (PhysMemWrite desc 8 acc ti data s) =
      some (S2ByteMemory.store s.mem desc.paddress.address.toNat data) := by
  have hUART : Sail.BitVec.castWidth (m := 40)
      (Sail.BitVec.extractLsb desc.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 15360#40 := by
    simpa [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb,
      Sail.Int.toNatChecked, UART_BASE] using hTableRAM.2
  rw [S2PhysWrite.complete desc acc ti data s hTableRAM.1 hTableRAM.2]
  delta S2PhysWrite.native
  simp only [memResult, S2ByteMemory.store, dite_eq_right hUART]
  rfl

theorem written_memory (desc : AddressDescriptor) (acc : AccessDescriptor) (ti : Option TranslationInfo)
    (data : BitVec 64) (s s' : State) (status : PhysMemRetStatus)
    (hTableRAM : S2TableRAM.OrdinaryRAM desc.paddress.address)
    (hrun : PhysMemWrite desc 8 acc ti data s = .ok status s') :
    s'.mem = S2ByteMemory.store s.mem desc.paddress.address.toNat data := by
  have h := mem_eq desc acc ti data s hTableRAM
  rw [hrun] at h
  exact Option.some.inj h

theorem update_write_equivalent (ha hd af dirty : Bool) (desc : AddressDescriptor)
    (acc : AccessDescriptor) (ti : Option TranslationInfo) (d : BitVec 64)
    (s s' : State) (status : PhysMemRetStatus)
    (hTableRAM : S2TableRAM.OrdinaryRAM desc.paddress.address)
    (halign : desc.paddress.address.toNat % 8 = 0)
    (hold : S2ByteMemory.DescAt s.mem desc.paddress.address.toNat d)
    (hdirty : dirty = true → ha = true ∧ hd = true ∧ d.getLsbD 51 = true)
    (hrun : PhysMemWrite desc 8 acc ti (S2Descriptor.hardwareUpdate af dirty d) s = .ok status s') :
    S2ByteMemory.Equivalent ha hd s.mem s'.mem := by
  rw [written_memory desc acc ti _ s s' status hTableRAM hrun]
  exact S2ByteMemory.store_equivalent ha hd s.mem _ d _ halign hold
    (S2Descriptor.hardwareUpdate_view ha hd af dirty d hdirty).symm

theorem af_write_equivalent (ha hd : Bool) (desc : AddressDescriptor) (acc : AccessDescriptor)
    (ti : Option TranslationInfo) (d : BitVec 64) (s s' : State) (status : PhysMemRetStatus)
    (hTableRAM : S2TableRAM.OrdinaryRAM desc.paddress.address)
    (halign : desc.paddress.address.toNat % 8 = 0)
    (hold : S2ByteMemory.DescAt s.mem desc.paddress.address.toNat d)
    (hrun : PhysMemWrite desc 8 acc ti (S2Descriptor.setAF d) s = .ok status s') :
    S2ByteMemory.Equivalent ha hd s.mem s'.mem := by
  rw [written_memory desc acc ti _ s s' status hTableRAM hrun]
  exact S2ByteMemory.af_equivalent ha hd s.mem _ d halign hold

theorem dirty_write_equivalent (desc : AddressDescriptor) (acc : AccessDescriptor)
    (ti : Option TranslationInfo) (d : BitVec 64) (s s' : State) (status : PhysMemRetStatus)
    (hTableRAM : S2TableRAM.OrdinaryRAM desc.paddress.address)
    (halign : desc.paddress.address.toNat % 8 = 0)
    (hold : S2ByteMemory.DescAt s.mem desc.paddress.address.toNat d)
    (hdbm : d.getLsbD 51 = true)
    (hrun : PhysMemWrite desc 8 acc ti (S2Descriptor.setDirty d) s = .ok status s') :
    S2ByteMemory.Equivalent true true s.mem s'.mem := by
  rw [written_memory desc acc ti _ s s' status hTableRAM hrun]
  exact S2ByteMemory.dirty_equivalent s.mem _ d halign hold hdbm

#print axioms af_write_equivalent
#print axioms dirty_write_equivalent
#print axioms update_write_equivalent
end S2PhysFrame
