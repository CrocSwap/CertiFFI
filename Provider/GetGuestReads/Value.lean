import Walk.S1ParamsUnknown
import Walk.S1EL2Enabled
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 150000
namespace GetGuestReads
abbrev State := SequentialState Regs oracleChoiceSource

def read {α : Type} (r : RegisterRef Regs α) : SailM α :=
  fun s => .ok (r.get s.regs) s

theorem read_eq {α : Type} (r : RegisterRef Regs α) :
    (readReg r : SailM α) = read r := rfl

drive_spec occurrence, occurrence_eq : fun (n : Nat) (s : State) => occLabel n s

theorem occurrence_function_eq : occLabel = occurrence := by
  funext n s
  exact occurrence_eq n s

theorem unknown_function_eq : undefined_S1TTWParams = fun label _ => S1ParamsUnknown.native label := by
  funext label u
  cases u
  funext s
  exact S1ParamsUnknown.complete label s

theorem el2_function_eq : EL2Enabled = fun _ => S1EL2Enabled.native := by
  funext u
  cases u
  funext s
  exact S1EL2Enabled.complete s
#print axioms read_eq
#print axioms occurrence_eq
#print axioms unknown_function_eq
#print axioms el2_function_eq
end GetGuestReads
