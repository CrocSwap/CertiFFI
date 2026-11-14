import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace UndefSummaries
drive_spec ErrorState_native, ErrorState_eq :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_ErrorState label () s
attribute [step_summary] ErrorState_eq
#print axioms ErrorState_eq
drive_spec MPAMinfo_native, MPAMinfo_eq :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_MPAMinfo label () s
attribute [step_summary] MPAMinfo_eq
#print axioms MPAMinfo_eq
drive_spec FullAddress_native, FullAddress_eq :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_FullAddress label () s
attribute [step_summary] FullAddress_eq
#print axioms FullAddress_eq
drive_spec GPCFRecord_native, GPCFRecord_eq :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_GPCFRecord label () s
attribute [step_summary] GPCFRecord_eq
#print axioms GPCFRecord_eq
drive_spec TLBContext_native, TLBContext_eq :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_TLBContext label () s
attribute [step_summary] TLBContext_eq
#print axioms TLBContext_eq
drive_spec AccessDescriptor_native, AccessDescriptor_eq :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_AccessDescriptor label () s
attribute [step_summary] AccessDescriptor_eq
#print axioms AccessDescriptor_eq
drive_spec FaultRecord_native, FaultRecord_eq :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_FaultRecord label () s
attribute [step_summary] FaultRecord_eq
#print axioms FaultRecord_eq
drive_spec AddressDescriptor_native, AddressDescriptor_eq :
  fun (label : ChoiceLabel) (s : SequentialState Regs oracleChoiceSource) =>
    undefined_AddressDescriptor label () s
attribute [step_summary] AddressDescriptor_eq
#print axioms AddressDescriptor_eq
end UndefSummaries
