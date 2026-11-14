import Pilot.S2PhysRead
import Pilot.S2PhysWrite
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
attribute [local simp] Nat.add_assoc
namespace S2SwapAny
/- Local 64-bit either-endian/no-RME case; no narrowing of the final profile claim. -/
drive_spec native, complete :
  fun (fault : FaultRecord) (prev next data : BitVec 64) (ee : BitVec 1)
      (acc : AccessDescriptor) (addr : AddressDescriptor) (ti : TranslationInfo)
      (s : SequentialState Regs oracleChoiceSource)
      (hNoRME : s.regs.FeatureImpl[232] = false)
      (hGIC : Sail.BitVec.castWidth (m := 40)
        (Sail.BitVec.extractLsb addr.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 11264#40)
      (hUART : Sail.BitVec.castWidth (m := 40)
        (Sail.BitVec.extractLsb addr.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 15360#40)
      (hGICCanonical : addr.paddress.address.extractLsb' 16 40 ≠ GIC_BASE.zeroExtend 40)
      (hUARTCanonical : addr.paddress.address.extractLsb' 16 40 ≠ UART_BASE.zeroExtend 40)
      (hTableRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
      (hDesc : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat data)
      (h0 : s.mem[addr.paddress.address.toNat]? = some (data.extractLsb' 0 8))
      (h1 : s.mem[addr.paddress.address.toNat + 1]? = some (data.extractLsb' 8 8))
      (h2 : s.mem[addr.paddress.address.toNat + 2]? = some (data.extractLsb' 16 8))
      (h3 : s.mem[addr.paddress.address.toNat + 3]? = some (data.extractLsb' 24 8))
      (h4 : s.mem[addr.paddress.address.toNat + 4]? = some (data.extractLsb' 32 8))
      (h5 : s.mem[addr.paddress.address.toNat + 5]? = some (data.extractLsb' 40 8))
      (h6 : s.mem[addr.paddress.address.toNat + 6]? = some (data.extractLsb' 48 8))
      (h7 : s.mem[addr.paddress.address.toNat + 7]? = some (data.extractLsb' 56 8)) =>
    AArch64_MemSwapTableDesc fault prev next ee acc addr ti s
attribute [step_summary] complete
#print axioms complete
end S2SwapAny
