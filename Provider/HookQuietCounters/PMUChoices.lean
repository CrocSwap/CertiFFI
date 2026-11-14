import HookQuietCounters.ICNTRParts
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUChoices.undefined_constraint_total"
  (← IO.getStderr).flush

theorem undefined_constraint_total (label : ChoiceLabel) (s : NativeState) :
    ∃ c, (undefined_Constraint label () : SailM Constraint) s = .ok c s := ⟨_, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUChoices.constrain_restc_total"
  (← IO.getStderr).flush

theorem constrain_restc_total (s : NativeState) :
    ∃ (c : Constraint) (bits : BitVec 2),
      (ConstrainUnpredictableBits .Unpredictable_RESTC 2 : SailM (Constraint × (BitVec 2))) s =
        .ok (c, bits) (afterOcc 543 (afterOcc 542 s)) := ⟨_, _, rfl⟩
#print axioms undefined_constraint_total
#print axioms constrain_restc_total
end HookQuietCounters
