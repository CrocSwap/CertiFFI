import Pilot.Driver
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace GetGuestVirtualization
abbrev State := SequentialState Regs oracleChoiceSource
namespace TTBR0
drive_spec native, complete : fun (s : State) => TTBR0_EL1_read () s
attribute [step_summary] complete
theorem function_eq : TTBR0_EL1_read = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end TTBR0
namespace TTBR1
drive_spec native, complete : fun (s : State) => TTBR1_EL1_read () s
attribute [step_summary] complete
theorem function_eq : TTBR1_EL1_read = fun _ => native := by
  funext u
  cases u
  funext s
  exact complete s
#print axioms complete
end TTBR1
namespace Constraint
drive_spec native, complete : fun (s : State) => ConstrainUnpredictable .Unpredictable_NVNV1 s
attribute [step_summary] complete
theorem function_eq : ConstrainUnpredictable .Unpredictable_NVNV1 = native := by
  funext s
  exact complete s
#print axioms complete
end Constraint
namespace TG0
drive_spec native, complete : fun (tg : BitVec 2) (s : State) => AArch64_S1DecodeTG0 tg s
attribute [step_summary] complete
theorem function_eq : AArch64_S1DecodeTG0 = native := by
  funext tg s
  exact complete tg s
#print axioms complete
end TG0
namespace TG1
drive_spec native, complete : fun (tg : BitVec 2) (s : State) => AArch64_S1DecodeTG1 tg s
attribute [step_summary] complete
theorem function_eq : AArch64_S1DecodeTG1 = native := by
  funext tg s
  exact complete tg s
#print axioms complete
end TG1
end GetGuestVirtualization
