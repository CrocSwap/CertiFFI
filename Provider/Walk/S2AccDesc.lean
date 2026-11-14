import Pilot.Driver
import Walk.S2SecurityEL
import Walk.S2MapVPM
import Walk.S2GenMPAM
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2AccDesc
drive_spec new_native, new_eq :
  fun (s : SequentialState Regs oracleChoiceSource)
      (hNoRME : s.regs.FeatureImpl[232] = false)
      (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) => NewAccDesc .AccessType_TTW s
attribute [step_summary] new_eq
drive_spec update_native, update_eq :
  fun (acc : AccessDescriptor) (s : SequentialState Regs oracleChoiceSource)
      (hNoRME : s.regs.FeatureImpl[232] = false)
      (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) =>
    CreateAccDescTTEUpdate acc s
attribute [step_summary] update_eq
drive_spec read_native, read_eq :
  fun (acc : AccessDescriptor) (s : SequentialState Regs oracleChoiceSource)
      (hNoRME : s.regs.FeatureImpl[232] = false)
      (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) =>
    CreateAccDescS2TTW acc s
attribute [step_summary] read_eq
#print axioms new_eq
#print axioms update_eq
#print axioms read_eq
end S2AccDesc
