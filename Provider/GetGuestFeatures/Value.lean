import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 150000
namespace GetGuestFeatures
abbrev State := SequentialState Regs oracleChoiceSource

namespace Have128BitDescriptorExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.Have128BitDescriptorExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.Have128BitDescriptorExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end Have128BitDescriptorExt

namespace HaveSVE
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveSVE () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveSVE = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveSVE

namespace HaveTME
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveTME () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveTME = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveTME

namespace HavePACExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HavePACExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HavePACExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HavePACExt

namespace HaveE0PDExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveE0PDExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveE0PDExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveE0PDExt

namespace AArch64_HaveHPDExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.AArch64_HaveHPDExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.AArch64_HaveHPDExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end AArch64_HaveHPDExt

namespace HaveMTE4Ext
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveMTE4Ext () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveMTE4Ext = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveMTE4Ext

namespace HaveAIEExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveAIEExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveAIEExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveAIEExt

namespace HaveRME
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveRME () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveRME = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveRME

namespace HaveSecureEL2Ext
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveSecureEL2Ext () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveSecureEL2Ext = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveSecureEL2Ext

namespace HaveMTE2Ext
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveMTE2Ext () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveMTE2Ext = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveMTE2Ext

namespace HaveTrapLoadStoreMultipleDeviceExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveTrapLoadStoreMultipleDeviceExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveTrapLoadStoreMultipleDeviceExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveTrapLoadStoreMultipleDeviceExt

namespace HaveFeatCMOW
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveFeatCMOW () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveFeatCMOW = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveFeatCMOW

namespace HaveAccessFlagUpdateExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveAccessFlagUpdateExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveAccessFlagUpdateExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveAccessFlagUpdateExt

namespace HaveDirtyBitModifierExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveDirtyBitModifierExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveDirtyBitModifierExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveDirtyBitModifierExt

namespace Have52BitIPAAndPASpaceExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.Have52BitIPAAndPASpaceExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.Have52BitIPAAndPASpaceExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end Have52BitIPAAndPASpaceExt

namespace HaveS1PIExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveS1PIExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveS1PIExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveS1PIExt

namespace HavePAN3Ext
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HavePAN3Ext () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HavePAN3Ext = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HavePAN3Ext

namespace HaveTHExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveTHExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveTHExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveTHExt

namespace HaveAccessFlagUpdateForTableExt
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveAccessFlagUpdateForTableExt () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveAccessFlagUpdateForTableExt = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveAccessFlagUpdateForTableExt

namespace HaveFeatMEC
drive_spec native, complete : fun (s : State) => ArmFull.Functions.HaveFeatMEC () s
attribute [step_summary] complete
theorem function_eq : ArmFull.Functions.HaveFeatMEC = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end HaveFeatMEC
end GetGuestFeatures
