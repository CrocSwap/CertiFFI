import Pilot.Driver
import Pilot.S2ByteMemory
import Pilot.S2TableRAM
import Pilot.S2Requests
import Pilot.S2Bytes
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
attribute [local simp] Nat.add_assoc
namespace S2PhysRead
drive_spec native, complete :
  fun (desc : AddressDescriptor) (acc : AccessDescriptor) (ti : Option TranslationInfo)
      (data : BitVec 64) (s : SequentialState Regs oracleChoiceSource)
      (hGIC : Sail.BitVec.castWidth (m := 40)
        (Sail.BitVec.extractLsb desc.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 11264#40)
      (hUART : Sail.BitVec.castWidth (m := 40)
        (Sail.BitVec.extractLsb desc.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 15360#40)
      (h0 : s.mem[desc.paddress.address.toNat]? = some (data.extractLsb' 0 8))
      (h1 : s.mem[desc.paddress.address.toNat + 1]? = some (data.extractLsb' 8 8))
      (h2 : s.mem[desc.paddress.address.toNat + 2]? = some (data.extractLsb' 16 8))
      (h3 : s.mem[desc.paddress.address.toNat + 3]? = some (data.extractLsb' 24 8))
      (h4 : s.mem[desc.paddress.address.toNat + 4]? = some (data.extractLsb' 32 8))
      (h5 : s.mem[desc.paddress.address.toNat + 5]? = some (data.extractLsb' 40 8))
      (h6 : s.mem[desc.paddress.address.toNat + 6]? = some (data.extractLsb' 48 8))
      (h7 : s.mem[desc.paddress.address.toNat + 7]? = some (data.extractLsb' 56 8)) =>
    PhysMemRead desc 8 acc ti s
attribute [step_summary] complete
#print axioms complete
theorem complete_desc (desc : AddressDescriptor) (acc : AccessDescriptor) (ti : Option TranslationInfo)
    (data : BitVec 64) (s : SequentialState Regs oracleChoiceSource)
    (hGIC : Sail.BitVec.castWidth (m := 40)
      (Sail.BitVec.extractLsb desc.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 11264#40)
    (hUART : Sail.BitVec.castWidth (m := 40)
      (Sail.BitVec.extractLsb desc.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 15360#40)
    (hdesc : S2ByteMemory.DescAt s.mem desc.paddress.address.toNat data) :
    PhysMemRead desc 8 acc ti s = native desc acc ti data s := by
  apply complete desc acc ti data s hGIC hUART
  · simpa using hdesc 0 (by decide)
  · exact hdesc 1 (by decide)
  · exact hdesc 2 (by decide)
  · exact hdesc 3 (by decide)
  · exact hdesc 4 (by decide)
  · exact hdesc 5 (by decide)
  · exact hdesc 6 (by decide)
  · exact hdesc 7 (by decide)
attribute [step_summary] complete_desc
end S2PhysRead
