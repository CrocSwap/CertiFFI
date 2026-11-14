import Pilot.S2PhysRead
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
attribute [local simp] Nat.add_assoc
namespace S2Fetch
/- Local no-RME case. G3 instantiation must be justified by the ID-to-Sail mapping;
   no whole feature vector or unobserved numerical register word is assumed. -/
drive_spec native, complete :
  fun (ee : BitVec 1) (addr : AddressDescriptor) (acc : AccessDescriptor)
      (fault : FaultRecord) (ti : TranslationInfo) (data : BitVec 64)
      (s : SequentialState Regs oracleChoiceSource)
      (hNoRME : s.regs.FeatureImpl[232] = false)
      (hGIC : Sail.BitVec.castWidth (m := 40)
        (Sail.BitVec.extractLsb addr.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 11264#40)
      (hUART : Sail.BitVec.castWidth (m := 40)
        (Sail.BitVec.extractLsb addr.paddress.address (Sail.Int.toNatChecked 55) 16) ≠ 15360#40)
      (h0 : s.mem[addr.paddress.address.toNat]? = some (data.extractLsb' 0 8))
      (h1 : s.mem[addr.paddress.address.toNat + 1]? = some (data.extractLsb' 8 8))
      (h2 : s.mem[addr.paddress.address.toNat + 2]? = some (data.extractLsb' 16 8))
      (h3 : s.mem[addr.paddress.address.toNat + 3]? = some (data.extractLsb' 24 8))
      (h4 : s.mem[addr.paddress.address.toNat + 4]? = some (data.extractLsb' 32 8))
      (h5 : s.mem[addr.paddress.address.toNat + 5]? = some (data.extractLsb' 40 8))
      (h6 : s.mem[addr.paddress.address.toNat + 6]? = some (data.extractLsb' 48 8))
      (h7 : s.mem[addr.paddress.address.toNat + 7]? = some (data.extractLsb' 56 8)) =>
    FetchDescriptor ee addr acc fault 64 ti s
attribute [step_summary] complete
#print axioms complete
end S2Fetch
