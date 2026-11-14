import Pilot.S2WriteBytes
import Pilot.S2TableRAM
import Pilot.S2ByteMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace S2PhysWrite
drive_spec native, complete :
  fun (desc : AddressDescriptor) (acc : AccessDescriptor) (ti : Option TranslationInfo)
      (data : BitVec 64) (s : SequentialState Regs oracleChoiceSource)
      (hGIC : desc.paddress.address.extractLsb' 16 40 ≠ GIC_BASE.zeroExtend 40)
      (hUART : desc.paddress.address.extractLsb' 16 40 ≠ UART_BASE.zeroExtend 40) =>
    PhysMemWrite desc 8 acc ti data s
attribute [step_summary] complete
#print axioms complete

noncomputable def ramNative (desc : AddressDescriptor) (acc : AccessDescriptor)
    (ti : Option TranslationInfo) (data : BitVec 64)
    (s : SequentialState Regs oracleChoiceSource) :
    EStateM.Result (Sail.Error exception) (SequentialState Regs oracleChoiceSource) PhysMemRetStatus :=
  let req := write_request acc ti 8 desc.vaddress desc.paddress.address data
  let m := S2ByteMemory.store s.mem desc.paddress.address.toNat data
  let evs := s.events.push (.memWrite req.pa.toNat 8 (req.va.map (·.toNat))
    req.access_kind req.value req.tag)
  .ok (CreatePhysMemRetStatus .Fault_None)
    {s with mem := m, events := evs}

theorem complete_ram (desc : AddressDescriptor) (acc : AccessDescriptor) (ti : Option TranslationInfo)
    (data : BitVec 64) (s : SequentialState Regs oracleChoiceSource)
    (hTableRAM : S2TableRAM.OrdinaryRAM desc.paddress.address) :
    PhysMemWrite desc 8 acc ti data s = ramNative desc acc ti data s := by
  have hUART : Sail.BitVec.castWidth (m := 40)
      (Sail.BitVec.extractLsb desc.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 15360#40 := by
    simpa [Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.extractLsb,
      Sail.Int.toNatChecked, UART_BASE] using hTableRAM.2
  rw [complete desc acc ti data s hTableRAM.1 hTableRAM.2]
  delta native
  simp only [dite_eq_right hUART]
  rfl
attribute [step_summary] complete_ram
#print axioms complete_ram
end S2PhysWrite
